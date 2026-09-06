# Verification

## Recorded Lean build: 2026-09-05

The complete project build and verification script exited with code 0.

- 45 project modules plus the root import module passed the source gate.
- All 359 named public theorem/lemma declarations passed the readable axiom audit.
- Independent environment enumeration checked all 517 project theorem declarations,
  including generated declarations and aliases.
- Only `propext`, `Classical.choice`, and `Quot.sound` were observed.
- No proof holes, custom axioms, native-decision trust, or build warnings.

The transcript is `validation/main-results-verification.txt`; exact source and
configuration hashes are in `validation/main-results-source-sha256.txt`.
`FORMALIZATION_SCOPE.md` records the mathematical boundary. Published acceptance
gaps remain explicit hypotheses and are not discharged by the axiom audit.

## Release documentation update

This release updates the repository documentation and omits intermediate
development notes and component-only logs. All 48 Lean files (45 mathematical
modules, the root module, and two audit modules), the pinned Lake configuration,
the verification scripts, and the CI workflow are byte-for-byte identical to
the files in the recorded build's source manifest. The original full build log
and its integrity record are retained unchanged.

The source check was run again with `python3 scripts/check-trust.py` and passed.
Lean compilation was not rerun for this documentation-only release.

`validation/main-results-source-sha256.txt` is the original build snapshot; its
README and validation-document entries refer to their earlier text. For the
current release, use `validation/release-source-sha256.txt`. On macOS, run from
the project root:

```sh
shasum -a 256 -c validation/release-source-sha256.txt
```

`validation/release-integrity.json` records the source comparison and the
preserved build-log digest. Checksums identify files; they do not replace the
Lean build and theorem-dependency audit.
