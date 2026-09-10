# Evidence: even-modulus manuscript checkers (grade E/C, not K)

Copied from `torus_integrated_proof.zip` (manuscript `even_directed_tori_integrated.tex`,
SHA256 `846a1e5f0a4ab5ea3511b312a3a8230210dc10e27f1483d1700445a670188e98`).  The manuscript
itself is not stored in this repository.  These are finite Python checks and certificates;
they are regression oracles for the Lean work in `TorusEven/` and prove nothing by themselves.

Reproduced on 2026-09-10 (Python 3.12, numpy 2.5.3, sympy 1.14.0); every regenerated
report matched the SHA256 in `MANIFEST.json`.

```sh
python checks/verify_integration.py            # D5 chronological bridge, m = 4..12, endpoint words to 256
python checks/verify_tour_certificate.py       # five 1024-tours of D_5(4), certificates/d5_m4_tours.json
python checks/check_transversal_lemma.py       # abstract lemma, 100 random instances + negative control
python checks/check_small_entries.py           # (m,d) = (4,7),(6,7),(4,9) full; (6,9),(8,7),(8,9) prefix
python checks/check_core_manuscript.py --out CORE_REPLAY_REPORT.json
```

`INTERFACES.md` lists the Lean interfaces the manuscript expects; `TorusEven/Goals.lean`
is the Lean-side counterpart.  `certificates/d5_m4_tours.json` is the manuscript's own
`D_5(4)` schedule; the Lean leaf currently used is the Route-E `m = 4` schedule in
`D5Odd/EvenRouteEM4.lean`, so the two are independent witnesses of the same theorem.
