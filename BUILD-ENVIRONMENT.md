# Build environment

## Reproducible project pins

- Lean: `leanprover/lean4:v4.19.0` (official Linux x86-64 release).
- Compiler commit: `6caaee842e9495688c1567e78c0e68dbb96942aa`.
- Lake: `5.0.0-6caaee8` (bundled with Lean 4.19.0).
- Mathlib: release `v4.19.0`, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- All transitive dependency commits are recorded in `lake-manifest.json`.

With elan installed, run from this directory:

```sh
lake exe cache get
lake build
```

Lake obtains dependencies at the manifest commits. `lake update` can regenerate the dependency manifest, but is not needed to reproduce the checked revision. No local absolute paths are encoded in the manifest or lakefile.

## Compatibility adjustment in the authoring environment

The authoring runtime has an unusual process namespace: `/proc/self/exe` exists, while `/proc/<getpid()>/exe` does not. Lean 4.19.0 uses the latter to find its executable. A narrowly scoped `LD_PRELOAD` wrapper maps only that own-process executable lookup to `/proc/self/exe`.

The compiler executable and Lean kernel implementation were not modified. The wrapper changes executable-path discovery only. Standard systems do not need it. The release archive extractor also required `TAR_OPTIONS=--no-same-owner` because the runtime does not map the UIDs recorded in release archives; archive contents were unchanged.

The compatibility source is included in `validation/local-runtime/proc-self-compat.c` to document that build environment; it is not a project dependency. The reproduction commands above use a standard Lean installation and require no author-local launcher path.

## Validation status

Final theorem/build validation is recorded in `README.md` and the delivered validation report. The toolchain pins alone do not establish that a theorem has been checked.
