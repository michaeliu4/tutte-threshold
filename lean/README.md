# Tutte threshold Lean package

This standalone Lean 4 package contains the checked proof closure for the Tutte-threshold results. The default `Results` library imports `Results.TutteThreshold.Solution.Main`; challenge and test files are intentionally excluded.

## Main declarations

- `Results.TutteThreshold.thm_1_2`
- `Results.TutteThreshold.thm_1_1_sufficiency`
- `Results.TutteThreshold.thm_1_1`
- `Results.TutteThreshold.thm_1_3_structure`
- `Results.TutteThreshold.thm_1_3_asymptotic`
- `Results.TutteThreshold.thm_1_3_limit`

## Assurance and assumptions

Recorded audit status: **Level 3, full checked**. The proof has no custom assumptions and does not use `native_decide`. The mathematical owner has not confirmed the mapping between the manuscript statements and the Lean declarations. The latest review of the corrected closure was performed by the same provider; an earlier independent review predates two comment corrections.

`PrintAxioms.lean` prints Lean's axiom dependencies for the six main declarations.

## Provenance and build

The proof sources are byte-for-byte copies from private main commit `b3da9c75451546c72845b58d74308222adb5f9ae`. `SOURCE-PROVENANCE.json` records each source and public Git blob hash. The package pins Lean and mathlib to `v4.32.1` and includes the corresponding dependency manifest.

Run these commands from the repository root. Build and provenance files are at that root.

```sh
lake exe cache get
lake build Results
lake env lean PrintAxioms.lean
```

No license is granted for the Lean source files in this package.
