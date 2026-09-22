# Tutte polynomial replacement weights and verification

Computational companion to **The sharp threshold for the multiplicative Merino–Welsh inequality on matroids**. Release **V1.1** accompanies the revised manuscript **V1**.

The paper determines the least universal evaluation parameter for a product inequality of Tutte polynomials over finite matroids without loops or coloops. This repository supplies the rational replacement weights and exact calculations used in Lemma 3.1 and Appendix A, *Replacement weights and their verification*.

## Verify the replacement inequalities

Use Python 3.10 or later. The verification requires only the standard library. Run without `-O`, `-OO` or `PYTHONOPTIMIZE`; optimized execution is rejected because it disables the assertions used by the checker.

```sh
python3 companion/verify.py
```

A successful run prints `"status": "PASS"` and the following totals:

| Check | Total |
|---|---:|
| Retained profiles | 7 |
| Series/parallel compositions | 56 |
| Exact recognitions / excluded compositions / replacements | 6 / 8 / 42 |
| Representative replacements / rational terms | 21 / 37 |
| Dual-expanded replacements / rational terms | 42 / 74 |
| Exact polynomial inequalities on `[2,3]` | 168 |
| Nonnegative shifted-coefficient / exceptional-cubic cases | 160 / 8 |

The checker reconstructs the graph-rank and polynomial calculations using exact rational arithmetic. It checks the prescribed finite comparisons; the universal theorem also uses the structural and analytic arguments in the paper. The code is not a proof-assistant formalization of those arguments.

## Reproduce the tables

From the repository root, run:

```sh
python3 generate_certificate_tables.py
```

This first verifies the data, then regenerates the six LaTeX files in `tables/`. The files provide the profile coordinates, replacement weights, composition classifications, polynomial slack coefficients, a worked replacement and the exceptional cubics. Their LaTeX macros are listed in [the companion README](companion/README.md).

## Files

| Path | Contents |
|---|---|
| `companion/representative_certificate.json` | Seven profiles, duality map and 21 representative replacements |
| `companion/reduced_certificate.json` | All 56 composition records, including the 42 replacements |
| `companion/verify.py` | Verification entry point |
| `companion/graphs.py`, `companion/polynomials.py` | Graph-rank and exact polynomial routines |
| `generate_certificate_tables.py`, `tables/` | Table generator and its recorded LaTeX output |
| `companion/discovery/` | Optional numerical-search scripts and stored candidates |

The [companion README](companion/README.md) explains the data format and verification scope. The [discovery README](companion/discovery/README.md) explains how to reproduce rationalization from the stored candidates. Re-running the optional numerical search requires NumPy and SciPy; neither is needed for verification or table generation. Numerical search may produce different candidates or fail to close. The proof uses the fixed rational data and the exact inequalities.

## Version and citation

Use the [V1.1 release](https://github.com/michaeliu4/tutte-threshold/releases/tag/V1.1) when checking manuscript V1. V1.1 adds an optimized-mode safeguard to the checker and updates the manuscript title in the documentation. The rational data, polynomial comparisons and generated tables are unchanged from V1. The original V1 tag is preserved; `main` may receive later changes.

Mingchang Liu. *Tutte polynomial replacement weights and verification*. V1.1. Computational companion to *The sharp threshold for the multiplicative Merino–Welsh inequality on matroids*. [GitHub repository](https://github.com/michaeliu4/tutte-threshold).

Machine-readable citation information is provided in `CITATION.cff`.
