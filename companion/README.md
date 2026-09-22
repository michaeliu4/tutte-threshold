# Exact finite replacement certificate

Companion to *A sharp universal threshold for Tutte-polynomial inequalities*, by Mingchang Liu (V1). The data and checker reproduce the finite comparisons used in Lemma 3.1 and Appendix A.

From this directory run:

```sh
python3 verify.py
```

Python 3.14.2 was used for the recorded verification. The code requires Python 3.10 or later and uses only the standard library. No installation, network connection, optimization package, floating point arithmetic, or absolute data path is required. The command prints its result without modifying the data.

Expected result: `PASS`; 7 profiles; all 56 series/parallel compositions of 28 unordered profile pairs; 6 exact closures, 8 excluded compositions, and 42 replacements; 21 representative replacements with 37 terms; 42 dual-expanded replacements with 74 terms; 168 exact coordinate inequalities. Of these, 160 have nonnegative coefficients in `t=x-2`, and 8 are exceptional cubics (4 representative cubics). The inequalities are certified on `[2,3]`.

`representative_certificate.json` contains the seven graphs, the dual profile permutation, and the 21 representative records. `reduced_certificate.json` contains all 56 composition records. Profile indices 0 through 6 mean `e, P2, S2, P3, S3, D, E`, where `D=S(P2,P2)` and `E=P(S2,S2)` (so `E` is the dual of `D`, also denoted `D*`). The stored signature order is `(T,F,A(2),I(2),C(2),B(2))`. Graph vertices 0 and 1 are the terminals. A term stores `(h,u,v,w)` as exact rational strings.

The checker recomputes every profile and composition axis polynomial by subset ranks, checks the stored tree and forest counts and graph signatures, checks the local series/parallel-class restriction, and reconstructs all dual replacement terms. The function `locally_reduced` tests this restriction; it is distinct from manuscript admissibility (no loops or coloops). The stored status `inadmissible` denotes a failed local restriction. For the eight excluded compositions, the manuscript exhibits a real parallel or series class of at least four elements. The checker checks strict edge reduction, positive weights, `w*w <= u*v`, both tree and forest budgets, and all four polynomial slacks. The four coordinates are `A, A+I, C, C+B`, with respective costs `u*A_h, u*(A_h+I_h), v*C_h, v*(C_h+B_h)`.

For a cubic `a+b*t+c*t*t+d*t*t*t` with `d<0`, the checker verifies `a,b,c+d >= 0`; the identity

```
a+b*t+t*t*((c+d)+(-d)*(1-t))
```

certifies nonnegativity on `0 <= t <= 1`. Nonnegative coefficient sequences certify the other slacks directly. These finite checks do not establish the graph decomposition or universal replacement theorem; their use in the proof depends on the mathematical lemmas in the manuscript.

From the parent directory, regenerate the printable tables with:

```sh
python3 generate_certificate_tables.py
```

The generator first runs the same exact checker, then writes the seven-profile table, all rational replacement weights, all 84 representative slack coefficient sequences, all 56 composition classifications, a worked replacement, and the four exceptional cubics. The LaTeX files require `amsmath`, `booktabs`, and `longtable`, together with the manuscript macros `\epsp`, `\PP`, `\SSS`, `\DD`, and `\EE`. The profile table also records the real edge count `h`. Replacement terms belonging to one network are kept together across page breaks, with default row stretch `\arraystretch=1.25`; the replacement table uses `1.45`.

## Verification scope

The included polynomial and graph-rank routines reconstruct the certificate using exact arithmetic. This checker is a replay using the mathematical helper routines developed with the certificate, rather than an independently implemented verifier. The manuscript supplies the structural and analytic proof.

## Discovery

The optional `discovery/` directory preserves the original numerical search and its recorded candidates. The search used NumPy and SciPy; rationalization of the supplied candidates uses only the standard library. Its README explains the distinction between discovering the original table, producing the shorter dual-generated table, and verifying the fixed certificate. Discovery scripts are not called by the proof checker or manuscript build.

Run the verifier without Python optimization (`-O`, `-OO` or `PYTHONOPTIMIZE`). It checks this condition before loading the data and exits with an error if assertions are disabled.
