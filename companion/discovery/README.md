# Optional certificate discovery

These scripts preserve the numerical search that produced the original rational replacements. They are separate from the exact proof checker in the parent directory.

`mix_pool_explore.py` grows a pool from the one-edge network, processing series and parallel compositions in increasing total edge count. It calls `cone_explore.solve`, which uses NumPy and SciPy's SLSQP optimizer to seek a joint replacement by smaller profiles. An unsuccessful numerical search is not a proof that a replacement is impossible. The stored `mix_pool_explore.json` records the run that closed with seven profiles.

`make_mixture_certificate.py` converts those stored candidates to rational numbers, checks the rational inequalities at x=2, and substitutes two explicit elementary certificates. It uses only the Python standard library. To reproduce that rationalization without rerunning optimization, make a working copy of this directory and run:

```sh
python3 make_mixture_certificate.py
```

This writes `mixture_certificate.json` in that copy. The result is the original 85-term certificate. The manuscript uses a shorter table: remove the eleven terms with zero w-weight, choose the lexicographically smaller composition in each dual pair, and generate its partner by the duality rule in Appendix A. The independently found candidates for two dual compositions need not be dual to one another; the published partner is generated from the chosen representative. The resulting 21 representatives contain 37 terms; the expanded table contains 74. The exact checker in the parent directory checks the fixed published data on the full interval [2,3], not merely at x=2.

To rerun the optional numerical search, install NumPy and SciPy in a separate environment and run in a working copy:

```sh
python3 mix_pool_explore.py
python3 make_mixture_certificate.py
```

The search overwrites `mix_pool_explore.json`; preserve the supplied copy if comparing against the recorded run. Numerical reruns can produce different candidates or fail to close, and the original optimizer versions were not recorded. `prior_network_reduction.json` is retained because `cone_explore.py` reads it at import time; it is not a proof input. Signature matches are discovery heuristics. The manuscript's six recognitions are justified by the explicit pointed constructions.

No optimization dependency is needed for `python3 ../verify.py`. The exact rational data, rather than a repeat of the heuristic search, are the reproducible proof input.
