// Copyright 2022 Adobe. All rights reserved.
// This file is licensed to you under the Apache License,
// Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0)
// or the MIT license (http://opensource.org/licenses/MIT),
// at your option.

// Unless required by applicable law or agreed to in writing,
// this software is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR REPRESENTATIONS OF ANY KIND, either express or
// implied. See the LICENSE-MIT and LICENSE-APACHE files for the
// specific language governing permissions and limitations under
// each license.

use std::str::FromStr;

use asn1_rs::FromDer;
use async_generic::async_generic;
use bcder::OctetString;
use chrono::{offset::LocalResult, DateTime, TimeZone, Utc};
use der::asn1::ObjectIdentifier;
use rasn::{prelude::*, types};
use rasn_cms::{CertificateChoices, SignerIdentifier};
use sha1::Sha1;
use sha2::{Sha256, Sha384, Sha512};

use crate::{
    crypto::{
        asn1::rfc3161::TstInfo,
        cose::{check_end_entity_certificate_profile, CertificateTrustPolicy},
        raw_signature::validator_for_sig_and_hash_algs,
        time_stamp::{
            response::{signed_data_from_time_stamp_response, tst_info_from_signed_data},
            TimeStampError,
        },
    },
    log_item,
    status_tracker::StatusTracker,
    validation_status::{
        TIMESTAMP_MALFORMED, TIMESTAMP_MISMATCH, TIMESTAMP_OUTSIDE_VALIDITY, TIMESTAMP_TRUSTED,
        TIMESTAMP_UNTRUSTED, TIMESTAMP_VALIDATED,
    },
};

const TIMESTAMP_OID_STR: &str = "1.3.6.1.5.5.7.3.8";

// when signed attributes are present the digest is the DER
// encoding of the SignerInfo SignedAttributes
fn signed_attributes_digested_content(
    signer_info: &rasn_cms::SignerInfo,
) -> Result<Option<Vec<u8>>, rasn::error::EncodeError> {
    if let Some(signed_attributes) = &signer_info.signed_attrs {
        match rasn::der::encode(signed_attributes) {
            Ok(encoded) => Ok(Some(encoded)),
            Err(e) => Err(e),
        }
    } else {
        Ok(None)
    }
}

/// Decode the TimeStampToken info and verify it against the supplied data and trust policy
#[async_generic]
pub fn verify_time_stamp(
    ts: &[u8],
    data: &[u8],
    ctp: &CertificateTrustPolicy,
    validation_log: &mut StatusTracker,
    verify_trust: bool,
) -> Result<TstInfo, TimeStampError> {
    // Get the signed data frorm the timestamp data
    let Ok(Some(sd)) = signed_data_from_time_stamp_response(ts) else {
        log_item!("", "could not parse timestamp data", "verify_time_stamp")
            .validation_status(TIMESTAMP_MALFORMED)
            .informational(validation_log);

        return Err(TimeStampError::DecodeError(
            "unable to find signed data".to_string(),
        ));
    };

    // Grab the list of certs used in signing this timestamp
    let Some(certs) = &sd.certificates else {
        log_item!("", "could not parse timestamp data", "verify_time_stamp")
            .validation_status(TIMESTAMP_UNTRUSTED)
            .informational(validation_log);

        return Err(TimeStampError::DecodeError(
            "time stamp contains no certificates".to_string(),
        ));
    };
    let certs_vec = certs.to_vec();

    // Convert certs to DER format
    let cert_ders: Vec<Vec<u8>> = certs_vec
        .iter()
        .filter_map(|cc| {
            if let CertificateChoices::Certificate(c) = cc {
                rasn::der::encode(c).ok()
            } else {
                None
            }
        })
        .collect();

    if cert_ders.len() != certs.len() {
        log_item!("", "could not parse timestamp data", "verify_time_stamp")
            .validation_status(TIMESTAMP_UNTRUSTED)
            .informational(validation_log);

        return Err(TimeStampError::DecodeError(
            "time stamp certificate could not be processed".to_string(),
        ));
    }

    let mut last_err = TimeStampError::InvalidData;
    let mut current_validation_log = StatusTracker::default();

    // Look for any valid signer.
    for signer_info in sd.signer_infos.to_vec().iter() {
        current_validation_log = StatusTracker::default(); // reset for latest results

        // Find signer's cert.
        let cert_pos = match certs_vec.iter().position(|cc| {
            let c = match cc {
                CertificateChoices::Certificate(c) => c,
                _ => return false,
            };

            match &signer_info.sid {
                SignerIdentifier::IssuerAndSerialNumber(sn) => {
                    sn.issuer == c.tbs_certificate.issuer
                        && sn.serial_number == c.tbs_certificate.serial_number
                }

                SignerIdentifier::SubjectKeyIdentifier(ski) => {
                    if let Some(extensions) = &c.tbs_certificate.extensions {
                        extensions.iter().any(|e| {
                            if e.extn_id == Oid::JOINT_ISO_ITU_T_DS_CERTIFICATE_EXTENSION_SUBJECT_KEY_IDENTIFIER {
                                return *ski == e.extn_value;
                            }
                            false
                        })
                    } else {
                        false
                    }
                }
            }
        }) {
            Some(c) => c,
            None => continue,
        };
        let CertificateChoices::Certificate(cert) = certs_vec[cert_pos] else {
            continue;
        };

        // get the cert common name, use different crate since x509-certificate does
        // not parse the common name correctly
        let mut common_name = String::new();
        if let Ok((_, new_c)) =
            x509_parser::certificate::X509Certificate::from_der(&cert_ders[cert_pos])
        {
            for rdn in new_c.subject().iter_common_name() {
                if let Ok(cn) = rdn.as_str() {
                    common_name.push_str(cn);
                }
            }
        }

        // Load TstInfo. We will verify its contents below against signed
        // values.
        let Ok(Some(mut tst)) = tst_info_from_signed_data(&sd) else {
            log_item!("", "timestamp response had no TstInfo", "verify_time_stamp")
                .validation_status(TIMESTAMP_MALFORMED)
                .informational(&mut current_validation_log);

            last_err = TimeStampError::InvalidData;
            continue;
        };

        let mi = &tst.message_imprint;

        // Check for time stamp expiration.
        let mut signing_time = generalized_time_to_datetime(tst.gen_time.clone()).timestamp();

        // Check the signer info's signed attributes.
        if let Some(attributes) = &signer_info.signed_attrs {
            // If there is a signed signing time attribute use it
            if let Some(Some(attrib_signing_time)) = attributes
                .to_vec()
                .iter()
                .find(|attr| attr.r#type == Oid::ISO_MEMBER_BODY_US_RSADSI_PKCS9_SIGNING_TIME)
                .map(|attr| {
                    if attr.values.len() != 1 {
                        // per CMS spec can only contain 1 signing time value
                        return None;
                    }

                    attr.values
                        .to_vec()
                        .first()
                        .and_then(|v| rasn::der::decode::<rasn_pkix::Time>(v.as_bytes()).ok())
                })
            {
                let signed_signing_time = match attrib_signing_time {
                    rasn_pkix::Time::Utc(date_time) => date_time.timestamp(),
                    rasn_pkix::Time::General(date_time) => {
                        generalized_time_to_datetime(date_time).timestamp()
                    }
                };

                if let Some(gt) = timestamp_to_generalized_time(signed_signing_time) {
                    // Use actual signed time.
                    signing_time = generalized_time_to_datetime(gt.clone()).timestamp();
                    tst.gen_time = gt;
                };
            }

            // Check that the mandatory signed message digest is self-consistent.
            match attributes
                .to_vec()
                .iter()
                .find(|attr| attr.r#type == Oid::ISO_MEMBER_BODY_US_RSADSI_PKCS9_MESSAGE_DIGEST)
            {
                Some(message_digest) => {
                    // message digest attribute MUST have exactly 1 value.
                    if message_digest.values.len() != 1 {
                        log_item!(
                            "",
                            "timestamp response contained multiple message digests",
                            "verify_time_stamp"
                        )
                        .validation_status(TIMESTAMP_MALFORMED)
                        .informational(&mut current_validation_log);

                        last_err = TimeStampError::DecodeError(format!(
                            "message digest attribute has {n} values, should have one",
                            n = message_digest.values.len()
                        ));

                        continue;
                    }

                    // Get signed message digest.
                    let signed_message_digest = match message_digest.values.to_vec().first() {
                        Some(a) => match rasn::der::decode::<types::OctetString>(a.as_bytes()) {
                            Ok(os) => os.to_vec(),
                            Err(_) => {
                                log_item!(
                                    "",
                                    "timestamp could not decode signed message data",
                                    "verify_time_stamp"
                                )
                                .validation_status(TIMESTAMP_MALFORMED)
                                .informational(&mut current_validation_log);

                                last_err = TimeStampError::DecodeError(
                                    "unable to decode signed message data".to_string(),
                                );
                                continue;
                            }
                        },
                        None => {
                            log_item!("", "timestamp bad message digest", "verify_time_stamp")
                                .validation_status(TIMESTAMP_MALFORMED)
                                .informational(&mut current_validation_log);

                            last_err = TimeStampError::DecodeError(
                                "unable to decode message digest".to_string(),
                            );
                            continue;
                        }
                    };

                    // Get message digest hash algorithm.
                    let Ok(di_oid) =
                        bcder::Oid::from_str(&signer_info.digest_algorithm.algorithm.to_string())
                    else {
                        log_item!(
                            "",
                            "timestamp bad message digest algorithm",
                            "verify_time_stamp"
                        )
                        .validation_status(TIMESTAMP_MALFORMED)
                        .informational(&mut current_validation_log);

                        last_err =
                            TimeStampError::DecodeError("unsupported digest algorithm".to_string());
                        continue;
                    };

                    let digest_algorithm = match DigestAlgorithm::try_from(&di_oid) {
                        Ok(d) => d,
                        Err(_) => {
                            log_item!(
                                "",
                                "timestamp bad message digest algorithm",
                                "verify_time_stamp"
                            )
                            .validation_status(TIMESTAMP_MALFORMED)
                            .informational(&mut current_validation_log);

                            last_err = TimeStampError::DecodeError(
                                "unsupported digest algorithm".to_string(),
                            );
                            continue;
                        }
                    };

                    let mut h = digest_algorithm.digester();
                    if let Some(content) = &sd.encap_content_info.content {
                        h.update(content);
                    }

                    let digest = h.finish();

                    if signed_message_digest != digest.as_ref() {
                        log_item!("", "timestamp bad message digest", "verify_time_stamp")
                            .validation_status(TIMESTAMP_MISMATCH)
                            .informational(&mut current_validation_log);

                        last_err = TimeStampError::InvalidData;
                        continue;
                    }
                }

                None => {
                    log_item!("", "timestamp no message digest", "verify_time_stamp")
                        .validation_status(TIMESTAMP_MALFORMED)
                        .informational(&mut current_validation_log);

                    last_err = TimeStampError::DecodeError("no message imprint".to_string());
                    continue;
                }
            }
        }

        // Build CMS TBS structure to verify.  If SignedAttributes are available then
        // use those as the TBS else the TBS is the value of the ContentInfo
        let tbs = match signed_attributes_digested_content(signer_info) {
            Ok(sdc) => match sdc {
                Some(tbs) => tbs,
                None => match &sd.encap_content_info.content {
                    Some(d) => d.to_vec(),
                    None => {
                        log_item!("", "timestamp no message digest", "verify_time_stamp")
                            .validation_status(TIMESTAMP_MALFORMED)
                            .informational(&mut current_validation_log);

                        last_err = TimeStampError::DecodeError(
                            "time stamp does not contain digested content".to_string(),
                        );
                        continue;
                    }
                },
            },
            Err(_) => {
                log_item!(
                    "",
                    "timestamp signer attributes malformed",
                    "verify_time_stamp"
                )
                .validation_status(TIMESTAMP_MALFORMED)
                .informational(&mut current_validation_log);

                last_err =
                    TimeStampError::DecodeError("timestamp signer info malformed".to_string());
                continue;
            }
        };

        // hash used for signature
        let Ok(hash_alg) =
            bcder::Oid::from_str(&signer_info.digest_algorithm.algorithm.to_string())
        else {
            log_item!("", "timestamp bad hash alg", "verify_time_stamp")
                .validation_status(TIMESTAMP_MALFORMED)
                .informational(&mut current_validation_log);

            last_err = TimeStampError::DecodeError("timestamp bad tbs certificate".to_string());
            continue;
        };

        // grab signature value.
        let sig_val =
            bcder::OctetString::new(bytes::Bytes::copy_from_slice(&signer_info.signature));

        // grab the signing key
        let signing_key_der_results =
            rasn::der::encode(&cert.tbs_certificate.subject_public_key_info);

        let Ok(signing_key_der) = signing_key_der_results else {
            log_item!("", "timestamp bad signing key", "verify_time_stamp")
                .validation_status(TIMESTAMP_MALFORMED)
                .informational(&mut current_validation_log);

            last_err = TimeStampError::DecodeError("timestamp bad tbs certificate".to_string());
            continue;
        };

        // algorithm used to sign the certificate
        let Ok(sig_alg) = bcder::Oid::from_str(
            &cert
                .tbs_certificate
                .subject_public_key_info
                .algorithm
                .algorithm
                .to_string(),
        ) else {
            log_item!("", "timestamp bad tbs certificate alg", "verify_time_stamp")
                .validation_status(TIMESTAMP_MALFORMED)
                .informational(&mut current_validation_log);

            last_err = TimeStampError::DecodeError("timestamp bad tbs certificate".to_string());
            continue;
        };

        // Verify signature of time stamp signature.
        if _sync {
            // IMPORTANT: The synchronous implementation of validate_timestamp_sync
            // on WASM is unable to support _some_ signature algorithms. The async path
            // should be used whenever possible (for WASM, at least).
            if validate_timestamp_sig(&sig_alg, &hash_alg, &sig_val, &tbs, &signing_key_der)
                .is_err()
            {
                log_item!(
                    "",
                    "timestamp signed data did not match signature",
                    "verify_time_stamp"
                )
                .validation_status(TIMESTAMP_UNTRUSTED)
                .informational(&mut current_validation_log);

                last_err = TimeStampError::Untrusted;
                continue;
            }
        } else {
            #[cfg(not(target_arch = "wasm32"))]
            if validate_timestamp_sig(&sig_alg, &hash_alg, &sig_val, &tbs, &signing_key_der)
                .is_err()
            {
                log_item!(
                    "",
                    "timestamp signed data did not match signature",
                    "verify_time_stamp"
                )
                .validation_status(TIMESTAMP_UNTRUSTED)
                .informational(&mut current_validation_log);

                last_err = TimeStampError::Untrusted;
                continue;
            }

            // NOTE: We're keeping the WASM-specific async path alive for now because it
            // supports more signature algorithms. Look for future WASM platform to provide
            // the opportunity to unify.
            #[cfg(target_arch = "wasm32")]
            if validate_timestamp_sig_async(&sig_alg, &hash_alg, &sig_val, &tbs, &signing_key_der)
                .await
                .is_err()
            {
                log_item!(
                    "",
                    "timestamp signed data did not match signature",
                    "verify_time_stamp"
                )
                .validation_status(TIMESTAMP_UNTRUSTED)
                .informational(&mut current_validation_log);

                last_err = TimeStampError::Untrusted;
                continue;
            }
        }

        // Make sure the time stamp's cert was valid for the stated signing time.
        let not_before = time_to_datetime(cert.tbs_certificate.validity.not_before).timestamp();
        let not_after = time_to_datetime(cert.tbs_certificate.validity.not_after).timestamp();

        if !(signing_time >= not_before && signing_time <= not_after) {
            log_item!(
                "",
                "timestamp signer outside of certificate validity",
                "verify_time_stamp"
            )
            .validation_status(TIMESTAMP_OUTSIDE_VALIDITY)
            .informational(&mut current_validation_log);

            last_err = TimeStampError::ExpiredCertificate;
            continue;
        }

        // Make sure the time stamp is valid for the specified data.
        let digest_algorithm = match DigestAlgorithm::try_from(&mi.hash_algorithm.algorithm) {
            Ok(d) => d,
            Err(_) => {
                log_item!(
                    "",
                    "timestamp unknown message digest algorithm",
                    "verify_time_stamp"
                )
                .validation_status(TIMESTAMP_UNTRUSTED)
                .informational(&mut current_validation_log);

                last_err = TimeStampError::UnsupportedAlgorithm;
                continue;
            }
        };

        let mut h = digest_algorithm.digester();
        h.update(data);

        let digest = h.finish();
        if digest.as_ref() == mi.hashed_message.to_bytes() {
            log_item!(
                "",
                format!("timestamp message digest matched: {}", &common_name),
                "verify_time_stamp"
            )
            .validation_status(TIMESTAMP_VALIDATED)
            .success(&mut current_validation_log);
        } else {
            log_item!(
                "",
                format!("timestamp message digest did not match: {}", &common_name),
                "verify_time_stamp"
            )
            .validation_status(TIMESTAMP_MISMATCH)
            .informational(&mut current_validation_log);

            last_err = TimeStampError::InvalidData;
            continue;
        }

        // the certificate must be on the trust list to be considered valid
        if verify_trust {
            let mut adjusted_ctp = ctp.clone();

            // Order certificates from leaf to root before trust validation
            let ordered_cert_ders = order_certificates_leaf_to_root(&cert_ders, cert_pos)?;

            // make sure this is a timestamping EKU
            adjusted_ctp.clear_ekus();
            adjusted_ctp.add_valid_ekus(TIMESTAMP_OID_STR.as_bytes()); // timestamp signing EKU
            if check_end_entity_certificate_profile(
                &ordered_cert_ders[0],
                &adjusted_ctp,
                &mut current_validation_log,
                Some(&tst),
            )
            .is_err()
            {
                log_item!(
                    "",
                    format!("timestamp cert untrusted: {}", &common_name),
                    "verify_time_stamp"
                )
                .validation_status(TIMESTAMP_UNTRUSTED)
                .informational(&mut current_validation_log);

                last_err = TimeStampError::Untrusted;
                continue;
            }

            if adjusted_ctp
                .check_certificate_trust(
                    &ordered_cert_ders[0..],
                    &ordered_cert_ders[0],
                    Some(signing_time),
                )
                .is_err()
            {
                log_item!(
                    "",
                    format!("timestamp cert untrusted: {}", &common_name),
                    "verify_time_stamp"
                )
                .validation_status(TIMESTAMP_UNTRUSTED)
                .informational(&mut current_validation_log);

                last_err = TimeStampError::Untrusted;
                continue;
            }

            // Only reachable once `check_end_entity_certificate_profile` and
            // `check_certificate_trust` have both succeeded, so the code now
            // reports a decision that was actually made. When `verify_trust` is
            // false nothing is logged for trust at all: `TIMESTAMP_VALIDATED`
            // above already reports what was established (the token's signature
            // and message imprint), and claiming more than that is the bug.
            log_item!(
                "",
                format!("timestamp cert trusted: {}", &common_name),
                "verify_time_stamp"
            )
            .validation_status(TIMESTAMP_TRUSTED)
            .success(&mut current_validation_log);
        }

        // Outside the `verify_trust` block on purpose. `verify_time_stamp` is
        // called with `verify_trust = false` on the *outgoing* path
        // (`time_stamp/http_request.rs`, `assertions/timestamp.rs`), where the
        // `Result` is `?`-propagated -- moving the return inside would turn
        // every freshly obtained timestamp into `Err(last_err)`.
        // If we find a valid value, we're done.
        validation_log.append(&current_validation_log);
        return Ok(tst);
    }

    validation_log.append(&current_validation_log);
    Err(last_err)
}

/// The token's certificate set as DER, plus the index of the first signer's
/// certificate within it. `None` when the token carries no certificates or no
/// `SignerInfo` that any of them matches.
///
/// Shared by [`tsa_signer_cert_der_from_token`] and
/// [`tsa_cert_chain_der_from_token`], which differ only in how much of the
/// result they return. Neither verifies the token.
fn signer_certs_from_token(ts: &[u8]) -> Result<Option<(Vec<Vec<u8>>, usize)>, TimeStampError> {
    let Some(sd) = signed_data_from_time_stamp_response(ts)? else {
        return Ok(None);
    };
    let Some(certs) = &sd.certificates else {
        return Ok(None);
    };
    let certs_vec = certs.to_vec();
    let cert_ders: Vec<Vec<u8>> = certs_vec
        .iter()
        .filter_map(|cc| {
            if let CertificateChoices::Certificate(c) = cc {
                rasn::der::encode(c).ok()
            } else {
                None
            }
        })
        .collect();
    if cert_ders.len() != certs_vec.len() {
        return Err(TimeStampError::DecodeError(
            "time stamp certificate could not be processed".to_string(),
        ));
    }
    // RFC 3161 tokens carry exactly one `SignerInfo`; `verify_time_stamp` loops
    // over them only because CMS permits more.
    let Some(signer_info) = sd.signer_infos.to_vec().into_iter().next() else {
        return Ok(None);
    };
    let Some(cert_pos) = certs_vec.iter().position(|cc| {
        let c = match cc {
            CertificateChoices::Certificate(c) => c,
            _ => return false,
        };
        match &signer_info.sid {
            SignerIdentifier::IssuerAndSerialNumber(sn) => {
                sn.issuer == c.tbs_certificate.issuer
                    && sn.serial_number == c.tbs_certificate.serial_number
            }
            SignerIdentifier::SubjectKeyIdentifier(ski) => {
                if let Some(extensions) = &c.tbs_certificate.extensions {
                    extensions.iter().any(|e| {
                        if e.extn_id
                            == Oid::JOINT_ISO_ITU_T_DS_CERTIFICATE_EXTENSION_SUBJECT_KEY_IDENTIFIER
                        {
                            return *ski == e.extn_value;
                        }
                        false
                    })
                } else {
                    false
                }
            }
        }
    }) else {
        return Ok(None);
    };
    Ok(Some((cert_ders, cert_pos)))
}

/// Extract the TSA signer certificate (DER) from an RFC 3161 timestamp token.
/// Does not verify the token; only parses it and returns the first signer's certificate.
pub fn tsa_signer_cert_der_from_token(ts: &[u8]) -> Result<Option<Vec<u8>>, TimeStampError> {
    let Some((cert_ders, cert_pos)) = signer_certs_from_token(ts)? else {
        return Ok(None);
    };
    Ok(Some(cert_ders[cert_pos].clone()))
}

/// Extract the TSA's certificate chain (DER, leaf first) from an RFC 3161
/// timestamp token, ordered by [`order_certificates_leaf_to_root`] -- the same
/// ordering [`verify_time_stamp`] applies before its own trust check.
///
/// Does not verify the token, and says nothing about whether it verifies: a
/// caller that acts on the chain must first establish that the token itself is
/// usable (`timeStamp.validated`, and no `timeStamp.mismatch` /
/// `.malformed` / `.outsideValidity`).
///
/// Exists because C2PA 2.4 §14.4.2 requires TSA trust anchors to be maintained
/// separately from claim-signer anchors, while `Settings::Trust` has a single
/// anchor slot and `verify_time_stamp` narrows only the EKU. Without the chain,
/// the only way to ask "does this TSA chain to *my* TSA list" is to re-verify
/// the whole asset under a different `trust_anchors`.
pub fn tsa_cert_chain_der_from_token(ts: &[u8]) -> Result<Vec<Vec<u8>>, TimeStampError> {
    let Some((cert_ders, cert_pos)) = signer_certs_from_token(ts)? else {
        return Ok(Vec::new());
    };
    order_certificates_leaf_to_root(&cert_ders, cert_pos)
}

fn generalized_time_to_datetime<T: Into<DateTime<Utc>>>(gt: T) -> DateTime<Utc> {
    gt.into()
}

fn timestamp_to_generalized_time(dt: i64) -> Option<crate::crypto::asn1::GeneralizedTime> {
    match Utc.timestamp_opt(dt, 0) {
        // try_into fails for dates outside der's supported 1970-9999 range
        LocalResult::Single(time) => time.try_into().ok(),
        _ => None,
    }
}

/// Digest algorithm enum compatible with bcder OIDs
#[derive(Clone, Copy, Debug)]
enum DigestAlgorithm {
    Sha1,
    Sha256,
    Sha384,
    Sha512,
}

impl DigestAlgorithm {
    fn digester(self) -> Hasher {
        match self {
            // `Sha1` follows the `digest` 0.10 traits, while `Sha2*` follows
            // `digest` 0.11, so each `new()` must be fully qualified to the
            // matching `Digest` trait.
            DigestAlgorithm::Sha1 => Hasher::Sha1(<Sha1 as sha1::Digest>::new()),
            DigestAlgorithm::Sha256 => Hasher::Sha256(<Sha256 as sha2::Digest>::new()),
            DigestAlgorithm::Sha384 => Hasher::Sha384(<Sha384 as sha2::Digest>::new()),
            DigestAlgorithm::Sha512 => Hasher::Sha512(<Sha512 as sha2::Digest>::new()),
        }
    }
}

impl TryFrom<&bcder::Oid> for DigestAlgorithm {
    type Error = ();

    fn try_from(oid: &bcder::Oid) -> Result<Self, Self::Error> {
        // Using der::asn1 instead of oids defined in oid.rs, because this is faster and we intend to remove x509_parser eventually.
        // Convert bcder::Oid to string, then parse as ObjectIdentifier for comparison
        let oid_str = oid.to_string();
        let const_oid = ObjectIdentifier::new(&oid_str).map_err(|_| ())?;

        // SHA-1: 1.3.14.3.2.26
        const SHA1_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.14.3.2.26");
        // SHA-256: 2.16.840.1.101.3.4.2.1
        const SHA256_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("2.16.840.1.101.3.4.2.1");
        // SHA-384: 2.16.840.1.101.3.4.2.2
        const SHA384_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("2.16.840.1.101.3.4.2.2");
        // SHA-512: 2.16.840.1.101.3.4.2.3
        const SHA512_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("2.16.840.1.101.3.4.2.3");

        if const_oid == SHA1_OID {
            Ok(DigestAlgorithm::Sha1)
        } else if const_oid == SHA256_OID {
            Ok(DigestAlgorithm::Sha256)
        } else if const_oid == SHA384_OID {
            Ok(DigestAlgorithm::Sha384)
        } else if const_oid == SHA512_OID {
            Ok(DigestAlgorithm::Sha512)
        } else {
            Err(())
        }
    }
}

/// Hasher enum to hold different digest types
enum Hasher {
    Sha1(Sha1),
    Sha256(Sha256),
    Sha384(Sha384),
    Sha512(Sha512),
}

impl Hasher {
    fn update(&mut self, data: &[u8]) {
        match self {
            Hasher::Sha1(h) => {
                use sha1::Digest;
                h.update(data);
            }
            Hasher::Sha256(h) => {
                use sha2::Digest;
                h.update(data);
            }
            Hasher::Sha384(h) => {
                use sha2::Digest;
                h.update(data);
            }
            Hasher::Sha512(h) => {
                use sha2::Digest;
                h.update(data);
            }
        }
    }

    fn finish(self) -> HasherOutput {
        match self {
            Hasher::Sha1(h) => {
                use sha1::Digest;
                HasherOutput(h.finalize().to_vec())
            }
            Hasher::Sha256(h) => {
                use sha2::Digest;
                HasherOutput(h.finalize().to_vec())
            }
            Hasher::Sha384(h) => {
                use sha2::Digest;
                HasherOutput(h.finalize().to_vec())
            }
            Hasher::Sha512(h) => {
                use sha2::Digest;
                HasherOutput(h.finalize().to_vec())
            }
        }
    }
}

/// Wrapper for hash output that implements AsRef<[u8]>
struct HasherOutput(Vec<u8>);

impl AsRef<[u8]> for HasherOutput {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

fn time_to_datetime(t: rasn_pkix::Time) -> DateTime<Utc> {
    match t {
        rasn_pkix::Time::Utc(u) => u,
        rasn_pkix::Time::General(gt) => generalized_time_to_datetime(gt),
    }
}

/// Order certificates from leaf to root based on the signer certificate position
fn order_certificates_leaf_to_root(
    cert_ders: &[Vec<u8>],
    leaf_cert_pos: usize,
) -> Result<Vec<Vec<u8>>, TimeStampError> {
    if leaf_cert_pos >= cert_ders.len() {
        return Err(TimeStampError::DecodeError(
            "invalid leaf certificate position".to_string(),
        ));
    }

    let parsed_certs: Result<Vec<_>, _> = cert_ders
        .iter()
        .map(|cert_der| x509_parser::certificate::X509Certificate::from_der(cert_der))
        .collect();

    let parsed_certs = match parsed_certs {
        Ok(certs) => certs,
        Err(_) => {
            return Err(TimeStampError::DecodeError(
                "failed to parse certificates".to_string(),
            ));
        }
    };

    let mut ordered_certs = Vec::new();
    let mut used_indices = std::collections::HashSet::new();

    // Start with the provided signer certificate position
    ordered_certs.push(cert_ders[leaf_cert_pos].clone());
    used_indices.insert(leaf_cert_pos);

    let mut current_cert_index = leaf_cert_pos;

    for _ in 0..cert_ders.len() {
        let current_cert = &parsed_certs[current_cert_index].1;
        let mut found_next = false;

        // Find the next certificate in the chain (try to match issuer and subject name)
        for (i, (_, next_cert)) in parsed_certs.iter().enumerate() {
            if used_indices.contains(&i) {
                continue;
            }

            if current_cert.issuer() == next_cert.subject() {
                ordered_certs.push(cert_ders[i].clone());
                used_indices.insert(i);
                current_cert_index = i;
                found_next = true;
                break;
            }
        }

        if !found_next {
            // No more certificates could be included in this chain.
            break;
        }
    }

    Ok(ordered_certs)
}

fn validate_timestamp_sig(
    sig_alg: &bcder::Oid,
    hash_alg: &bcder::Oid,
    sig_val: &OctetString,
    tbs: &[u8],
    signing_key_der: &[u8],
) -> Result<(), TimeStampError> {
    let Some(validator) = validator_for_sig_and_hash_algs(sig_alg, hash_alg) else {
        return Err(TimeStampError::UnsupportedAlgorithm);
    };

    validator
        .validate(&sig_val.to_bytes(), tbs, signing_key_der)
        .map_err(|_| TimeStampError::InvalidData)
}

#[cfg(target_arch = "wasm32")]
async fn validate_timestamp_sig_async(
    sig_alg: &bcder::Oid,
    hash_alg: &bcder::Oid,
    sig_val: &OctetString,
    tbs: &[u8],
    signing_key_der: &[u8],
) -> Result<(), TimeStampError> {
    if let Some(validator) =
        crate::crypto::raw_signature::async_validator_for_sig_and_hash_algs(sig_alg, hash_alg)
    {
        validator
            .validate_async(&sig_val.to_bytes(), tbs, signing_key_der)
            .await
            .map_err(|_| TimeStampError::InvalidData)
    } else if let Some(validator) =
        crate::crypto::raw_signature::validator_for_sig_and_hash_algs(sig_alg, hash_alg)
    {
        validator
            .validate(&sig_val.to_bytes(), tbs, signing_key_der)
            .map_err(|_| TimeStampError::InvalidData)
    } else {
        Err(TimeStampError::UnsupportedAlgorithm)
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use crate::{
        crypto::{
            base64,
            cose::{parse_cose_sign1, validate_cose_tst_info, CertificateTrustPolicy},
            hash::sha256,
        },
        status_tracker::StatusTracker,
        store::Store,
    };

    /// Carries a `sigTst` header, so it exercises the real timestamp path
    /// rather than a synthesised token. Any fixture in the list produced by
    /// `grep -rla sigTst sdk/tests/fixtures` would do.
    const CA_JPG: &[u8] = include_bytes!("../../../tests/fixtures/CA.jpg");

    /// The parsed `COSE_Sign1` of `CA.jpg`'s active claim, and the claim bytes
    /// it was computed over — the two inputs `validate_cose_tst_info` needs.
    fn ca_jpg_sign1() -> (coset::CoseSign1, Vec<u8>) {
        let mut stream = std::io::Cursor::new(CA_JPG);
        let jumbf = crate::jumbf_io::load_jumbf_from_stream("image/jpeg", &mut stream).unwrap();

        let mut log = StatusTracker::default();
        let store = Store::from_jumbf(&jumbf, &mut log).unwrap();
        let claim = store.provenance_claim().unwrap();

        let data = claim.data().unwrap();
        let sign1 = parse_cose_sign1(claim.signature_val(), &data, &mut log).unwrap();
        (sign1, data)
    }

    /// `check_certificate_trust` accepts an end-entity certificate listed by
    /// the base64 SHA-256 of its DER (§14.4.3), which is the cheapest way to
    /// give the test an anchor that genuinely matches this token's signer
    /// without shipping a PEM bundle alongside the fixture.
    fn end_entity_credential_line(cert_der: &[u8]) -> String {
        base64::encode(&sha256(cert_der))
    }

    fn tsa_signer_cert(sign1: &coset::CoseSign1, data: &[u8]) -> Vec<u8> {
        let token = crate::crypto::cose::timestamp_token_bytes_from_sign1(sign1)
            .expect("fixture carries a sigTst token");
        let _ = data;
        tsa_signer_cert_der_from_token(&token)
            .unwrap()
            .expect("token names a signer certificate")
    }

    /// The chain the fork exposes must be the *same* certificates
    /// `verify_time_stamp` builds for its own trust check, in the same order --
    /// otherwise a caller evaluating it against a TSA list is answering a
    /// different question from the one the status codes report.
    #[test]
    fn the_exposed_tsa_chain_is_leaf_first_and_starts_at_the_signer() {
        let (sign1, data) = ca_jpg_sign1();
        let token = crate::crypto::cose::timestamp_token_bytes_from_sign1(&sign1)
            .expect("fixture carries a sigTst token");

        let chain = tsa_cert_chain_der_from_token(&token).unwrap();
        assert!(!chain.is_empty(), "the token carries certificates");
        assert_eq!(
            chain[0],
            tsa_signer_cert(&sign1, &data),
            "element 0 must be the signer's own certificate, not an issuer"
        );

        // Leaf first means each element is issued by the next one.
        for pair in chain.windows(2) {
            let (_, child) = x509_parser::certificate::X509Certificate::from_der(&pair[0]).unwrap();
            let (_, parent) =
                x509_parser::certificate::X509Certificate::from_der(&pair[1]).unwrap();
            assert_eq!(
                child.issuer(),
                parent.subject(),
                "chain is not ordered leaf to root"
            );
        }
    }

    /// A signature with no `sigTst` must yield an empty chain rather than an
    /// error or a borrowed signer chain. `SignatureInfo::tsa_cert_chain` is
    /// `""` in that case, and a caller keys "no time-stamp" off exactly that.
    #[test]
    fn a_token_that_is_not_a_token_yields_an_empty_chain() {
        assert!(tsa_cert_chain_der_from_token(b"not a timestamp token")
            .unwrap_or_default()
            .is_empty());
    }

    /// Upstream #2317: `TIMESTAMP_TRUSTED` used to be logged after the
    /// `if verify_trust` block, so it was emitted even when no trust check ran.
    /// `claim.rs` sets `verify_timestamp_trust = false` for every claim v1, so
    /// that path produced a `timeStamp.trusted` backed by nothing.
    ///
    /// Reverting the patch (moving the `log_item!` back below the block) makes
    /// this assertion fail; `TIMESTAMP_VALIDATED` is asserted alongside it so
    /// the test cannot pass by never reaching the code at all.
    #[test]
    fn no_trusted_code_when_trust_checking_is_off() {
        let (sign1, data) = ca_jpg_sign1();
        let ctp = CertificateTrustPolicy::new();
        let mut log = StatusTracker::default();

        validate_cose_tst_info(&sign1, &data, &ctp, &mut log, false)
            .expect("the fixture's timestamp token verifies");

        assert!(
            log.has_status(TIMESTAMP_VALIDATED),
            "the token's signature and message imprint were checked, so this must be logged"
        );
        assert!(
            !log.has_status(TIMESTAMP_TRUSTED),
            "no trust check ran, so nothing may claim the TSA is trusted"
        );
    }

    /// The other half: with `verify_trust` on and an anchor that does match,
    /// the code is still emitted. Without this, the patch could be "fixed" by
    /// deleting the code outright and the suite would stay green.
    #[test]
    fn trusted_code_when_trust_checking_is_on_and_the_anchor_matches() {
        let (sign1, data) = ca_jpg_sign1();

        let mut ctp = CertificateTrustPolicy::new();
        let leaf = tsa_signer_cert(&sign1, &data);
        ctp.add_end_entity_credentials(end_entity_credential_line(&leaf).as_bytes())
            .unwrap();

        let mut log = StatusTracker::default();
        validate_cose_tst_info(&sign1, &data, &ctp, &mut log, true)
            .expect("the fixture's timestamp token verifies");

        assert!(log.has_status(TIMESTAMP_VALIDATED));
        assert!(
            log.has_status(TIMESTAMP_TRUSTED),
            "the trust check succeeded, so the code must still be emitted"
        );
    }

    /// And with trust checking on against a store the token cannot reach, the
    /// outcome is `untrusted`, never `trusted`.
    #[test]
    fn untrusted_code_when_trust_checking_is_on_and_nothing_matches() {
        let (sign1, data) = ca_jpg_sign1();
        let ctp = CertificateTrustPolicy::new();
        let mut log = StatusTracker::default();

        let _ = validate_cose_tst_info(&sign1, &data, &ctp, &mut log, true);

        assert!(!log.has_status(TIMESTAMP_TRUSTED));
        assert!(log.has_status(TIMESTAMP_UNTRUSTED));
    }
}
