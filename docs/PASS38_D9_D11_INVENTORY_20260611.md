# PASS38 D9/D11 High-Even Seed Inventory

Bundle inspected, read-only:
`/tmp/paper_versions/even_modulus_directed_tori_pass38_review_revision/even_modulus_directed_tori_pass38_review_revision/`

Working output:
`/tmp/codex_pass38_task/PASS38_D9_D11_INVENTORY.md`

## 1. D9/D11 assets listed by metadata

`FILE_LIST.txt` contains exactly two dimension 9 or 11 seed/certificate files:

| file | kind | dim | modulus encoded? | size bytes | in FILE_LIST | in WITNESS_LIST | in POINTWISE_CERTIFICATES | sha256 verified |
|---|---:|---:|---|---:|---|---|---|---|
| `seeds/high_even_encoded/D9_high_even_seed.json` | high-even forest-incidence seed/certificate | 9 | no fixed modulus in file; applies via theorem for every even `m > 9` | 11457 | yes | yes | no D9 entry | Y: MANIFEST and WITNESS_MANIFEST |
| `seeds/high_even_encoded/D11_high_even_seed.json` | high-even forest-incidence seed/certificate | 11 | no fixed modulus in file; applies via theorem for every even `m > 11` | 20077 | yes | yes | no D11 entry | Y: MANIFEST and WITNESS_MANIFEST |

No separate D9/D11 witness files are listed. `POINTWISE_CERTIFICATES.txt` documents only pointwise root-flat certificates for `D5_m4`, `D7_m4`, and `D7_m6`; it has no D9 or D11 certificate entry.

Manifest hashes used:

| file | sha256 |
|---|---|
| `seeds/high_even_encoded/D9_high_even_seed.json` | `73c1dc257a26a528b56e31ffd69ed9be7c740a3562e58dc3c7b09e618ce73dd9` |
| `seeds/high_even_encoded/D11_high_even_seed.json` | `b89a20642e57369097e04d536ad3f0bf319c44afb4e8ad863e145ed25362a0ff` |

Relevant manifest transcript:

```text
$ sha256sum seeds/high_even_encoded/D9_high_even_seed.json seeds/high_even_encoded/D11_high_even_seed.json
73c1dc257a26a528b56e31ffd69ed9be7c740a3562e58dc3c7b09e618ce73dd9  seeds/high_even_encoded/D9_high_even_seed.json
b89a20642e57369097e04d536ad3f0bf319c44afb4e8ad863e145ed25362a0ff  seeds/high_even_encoded/D11_high_even_seed.json

$ sha256sum -c MANIFEST.sha256 --ignore-missing
seeds/high_even_encoded/D11_high_even_seed.json: OK
seeds/high_even_encoded/D9_high_even_seed.json: OK

$ sha256sum -c WITNESS_MANIFEST.sha256 --ignore-missing
seeds/high_even_encoded/D11_high_even_seed.json: OK
seeds/high_even_encoded/D9_high_even_seed.json: OK
```

## 2. Seed file structures

### `seeds/high_even_encoded/D9_high_even_seed.json`

JSON object keys: `certificate_type`, `d`, `stages`, `supports`, `terminal_alignment`.
It records `d = 9` and `certificate_type = high-even forest-incidence certificate`; no modulus field is present.
There are 7 stages, equal to `D-2`; each stage has `stage`, `shift`, `triple`, and `pairs`.
There are 27 supports: 6 `triple`, 18 `pair`, and 3 `final_pair`; each support has `stage`, `packet_type`, `packet`, and `support_edges`.
`terminal_alignment` has `basis_edges`, `perm`, `root_vertices`, `rows`, `signs`, and `triple`.

### `seeds/high_even_encoded/D11_high_even_seed.json`

JSON object keys: `certificate_type`, `d`, `stages`, `supports`, `terminal_alignment`.
It records `d = 11` and `certificate_type = high-even forest-incidence certificate`; no modulus field is present.
There are 9 stages, equal to `D-2`; each stage has `stage`, `shift`, `triple`, and `pairs`.
There are 44 supports: 8 `triple`, 32 `pair`, and 4 `final_pair`; each support has `stage`, `packet_type`, `packet`, and `support_edges`.
`terminal_alignment` has `basis_edges`, `perm`, `root_vertices`, `rows`, `signs`, and `triple`.

## 3. What `verify.py` checks

`verify.py` has no argparse or per-file command-line interface. Running `python3 verify.py` runs the whole supplement verification: manifests, pointwise root-flat cases, high-even encoded cases, the finite `m=4` terminal case, and the terminal-family consistency checks.

For D9/D11-specific checks, I invoked `verify.verify_high_even_seed(path)` from `python3`. This uses the same verifier code but scopes the run to one high-even JSON file.

Verification depth:

| certificate kind | files | verification depth |
|---|---|---|
| pointwise root-flat | `seeds/rootflat/D5_m4_*`, `D7_m4_*`, `D7_m6_*` | reconstructs decoded layer rows, checks RF1 Latin rows, RF2 layer-map bijections, RF3 one-cycle return maps, then checks reserve-switch witnesses |
| high-even forest-incidence | `seeds/high_even_encoded/D5/D7/D9/D11_high_even_seed.json` | clause-level forest-incidence check; does not reconstruct pointwise RF maps. It checks the finite predicates that the manuscript proves imply RF1/RF2/RF3 after phase-normalized realization for every even `m > D` |
| terminal blocks and families | internal formulas in `verify.py` | checks explicit terminal return cycles, cap classifications, router pencils, multiphase switch formulas, and related consistency values |
| manifests | `MANIFEST.sha256`, `WITNESS_MANIFEST.sha256` | recomputes hashes over listed files and checks missing/extra/mismatched entries |

For high-even seeds, `verify_high_even_seed()` checks:

- `D-2` stages, valid chronological stage ids, distinct shifts, and each stage is exactly one triple plus a matching on all labels.
- For every colour, shifted stage edges form the required two-component final forest with singleton component not equal to the colour.
- Determinant rows have constant term `B = +/-1`.
- Every support is acyclic, contains a unique valid active basis, is edge-disjoint from relevant previous colour forests, and satisfies the rank/intersection and rank-minor gcd saturation tests.
- Contracted rooted support-order records are forests with interval cuts and laminarity.
- The computed terminal `A2` alignment matches the recorded `terminal_alignment`.

## 4. Verification outcomes

### D9 high-even seed

Command used:

```text
python3 - <<'PY'
import json
from pathlib import Path
import verify
path = Path('seeds/high_even_encoded/D9_high_even_seed.json')
r = verify.verify_high_even_seed(path)
summary = {
  'asset': str(path),
  'ok': r['ok'],
  'd': r['d'],
  'stages': r['stages'],
  'distinct_stage_placements': r['distinct_stage_placements'],
  'supports': r['supports'],
  'support_by_stage': r['support_by_stage'],
  'support_equalities': r['support_equalities'],
  'active_basis_choices': r['active_basis_choices'],
  'support_order_checks': r['support_order_checks'],
  'support_order_laminar': r['support_order_laminar'],
  'isolates': r['isolates'],
  'determinants': r['determinants'],
  'terminal_carrier': r['terminal_carrier'],
  'sha256': r['sha256'],
}
print(json.dumps(summary, indent=2, sort_keys=True))
PY
```

Outcome: PASS.

Transcript:

```json
{
  "active_basis_choices": 27,
  "asset": "seeds/high_even_encoded/D9_high_even_seed.json",
  "d": 9,
  "determinants": [
    [1, -1],
    [0, -1],
    [0, -1],
    [0, 1],
    [0, 1],
    [0, 1],
    [0, -1],
    [0, -1],
    [0, -1]
  ],
  "distinct_stage_placements": true,
  "isolates": [8, 0, 1, 1, 2, 3, 5, 6, 7],
  "ok": true,
  "sha256": "73c1dc257a26a528b56e31ffd69ed9be7c740a3562e58dc3c7b09e618ce73dd9",
  "stages": 7,
  "support_by_stage": {
    "1": 4,
    "2": 4,
    "3": 4,
    "4": 4,
    "5": 4,
    "6": 4,
    "7": 3
  },
  "support_equalities": 60,
  "support_order_checks": 60,
  "support_order_laminar": true,
  "supports": 27,
  "terminal_carrier": {
    "basis_edges": [[0, 4], [0, 3]],
    "perm": [0, 1, 2],
    "root_vertices": [4, 0, 3],
    "rows": [[-1, -1], [0, 1], [1, 0]],
    "signs": [1, 1, -1],
    "triple": [7, 3, 6]
  }
}
```

### D11 high-even seed

Command used:

```text
python3 - <<'PY'
import json
from pathlib import Path
import verify
path = Path('seeds/high_even_encoded/D11_high_even_seed.json')
r = verify.verify_high_even_seed(path)
summary = {
  'asset': str(path),
  'ok': r['ok'],
  'd': r['d'],
  'stages': r['stages'],
  'distinct_stage_placements': r['distinct_stage_placements'],
  'supports': r['supports'],
  'support_by_stage': r['support_by_stage'],
  'support_equalities': r['support_equalities'],
  'active_basis_choices': r['active_basis_choices'],
  'support_order_checks': r['support_order_checks'],
  'support_order_laminar': r['support_order_laminar'],
  'isolates': r['isolates'],
  'determinants': r['determinants'],
  'terminal_carrier': r['terminal_carrier'],
  'sha256': r['sha256'],
}
print(json.dumps(summary, indent=2, sort_keys=True))
PY
```

Outcome: PASS.

Transcript:

```json
{
  "active_basis_choices": 44,
  "asset": "seeds/high_even_encoded/D11_high_even_seed.json",
  "d": 11,
  "determinants": [
    [-1, 1],
    [0, 1],
    [0, 1],
    [0, -1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, -1],
    [0, -1],
    [0, -1],
    [0, -1]
  ],
  "distinct_stage_placements": true,
  "isolates": [10, 0, 1, 1, 2, 4, 4, 5, 6, 7, 8],
  "ok": true,
  "sha256": "b89a20642e57369097e04d536ad3f0bf319c44afb4e8ad863e145ed25362a0ff",
  "stages": 9,
  "support_by_stage": {
    "1": 5,
    "2": 5,
    "3": 5,
    "4": 5,
    "5": 5,
    "6": 5,
    "7": 5,
    "8": 5,
    "9": 4
  },
  "support_equalities": 96,
  "support_order_checks": 96,
  "support_order_laminar": true,
  "supports": 44,
  "terminal_carrier": {
    "basis_edges": [[6, 8], [4, 8]],
    "perm": [0, 1, 2],
    "root_vertices": [6, 8, 4],
    "rows": [[1, 1], [0, -1], [-1, 0]],
    "signs": [1, 1, -1],
    "triple": [9, 0, 7]
  }
}
```

### Control: D5 high-even seed

Command used: `verify.verify_high_even_seed(Path('seeds/high_even_encoded/D5_high_even_seed.json'))`.

Outcome: PASS.

Key output:

```json
{
  "active_basis_choices": 5,
  "asset": "seeds/high_even_encoded/D5_high_even_seed.json",
  "d": 5,
  "distinct_stage_placements": true,
  "ok": true,
  "sha256": "28e3e3af8f8042bc26e739b5a773dcd082fae3224d0793df90cd080ec20da067",
  "stages": 3,
  "support_equalities": 12,
  "support_order_checks": 12,
  "support_order_laminar": true,
  "supports": 5
}
```

### Control: D5 pointwise root-flat seed

Command used: `verify.verify_rootflat_cases()['D5_4']`.

Outcome: PASS.

Key output:

```json
{
  "asset": "seeds/rootflat/D5_m4_seed.json + seeds/rootflat/D5_m4_witness.json",
  "d": 5,
  "m": 4,
  "ok": true,
  "rf1": true,
  "rf2": true,
  "rf3": true,
  "root_flat_size": 256,
  "sha256_seed": "2e6146f9b6bc0c4a6a2a033415c5b91838678eb90a9c6bb8afa6f3bea68eb9be",
  "witnesses": [
    {
      "C": [48],
      "C_size": 1,
      "colors": [0, 1],
      "common_edge_images": [57],
      "common_edge_singleton": true,
      "comparison_closed_on_C": true,
      "post_switch_color_a_one_cycle": true,
      "post_switch_color_b_one_cycle": true,
      "unit_mod_m": true
    }
  ]
}
```

## 5. Manuscript theorem and predicates

Theorem statement from `manuscript/even_modulus_directed_tori.tex`:

```tex
\begin{theorem}[Graphic high-even seeds]\label{thm:encoded-bases}
For each high-even seed record in dimension $D\in\{5,7,9,11\}$, the graphic seed predicates of \cref{def:graphic-encoded-seed} hold: stage partitions, shifted colour coforests, support completions, determinant units, support saturation, and terminal $A_2$ alignment.  The rooted support-interval records used in paired growth are then derived from these support forests by \cref{lem:support-induced-interval-record}.  By \cref{prop:encoded-to-rf}, the phase-normalized realization rule turns each finite forest-incidence packet datum into an RF layer schedule in dimension $D$ for every even $m>D$.  The same graphic data carry the terminal three-colour alignment condition used in \cref{prop:marked-encoded-seeds}.  Consequently $\HD(D,m)$ holds in these base dimensions.  The determinant-unit, support-exactness, and saturation assertions used by these seeds are modularly exact consequences of the graphic root-lattice lemmas above.
\end{theorem}
```

Encoded local-block schedule definition, condensed from `def:encoded-schedule`:

- An encoded local-block schedule fixes odd `D` and has `D-2` stages with injective physical guide-row placements.
- Each stage has cyclic shift `alpha_s`, a triple `(a,b,c)`, and a matching on remaining labels; this defines a permutation `sigma_s`.
- For colour `r`, the shifted forest edge is `{r+alpha_s, sigma_s(r)+alpha_s}` and the carry deviation is `u_{sigma_s(r)+alpha_s} - u_{r+alpha_s}`.
- A support record is a forest containing an allowed active basis for a triple or pair local block; it must be acyclic and must remain a required two-component forest after adding previous colour edges.
- The determinant in the quotient lattice must have affine form `A_r m + B_r` with `B_r = +/-1`; active blocks carry strict local-block lattice data and a terminal three-colour alignment.

High-even finite predicates `(H1)-(H7)` from `def:certificate-predicate-packages`:

| predicate | one-line meaning |
|---|---|
| H1 | distinct stage placements; every stage is one shifted triple packet plus a matching |
| H2 | shifted colour edges form the coforest pattern giving determinant constants `B_r = +/-1` |
| H3 | each packet support forest contains active basis, is edge-disjoint from previous colour forest, and gives support exactness/common complements |
| H4 | rank-minor saturation identities are integral saturated equalities, preserved modulo `m` |
| H5 | terminal record is an oriented `A2` triple aligned with the terminal block |
| H6 | rooted support-order records induce laminar interval cuts for paired growth |
| H7 | phase-normalized offsets are compatible with preceding packet supports, so realization is well-defined |

Graphic seed predicates `(GS1)-(GS4)` from `def:graphic-encoded-seed`:

| predicate | one-line meaning |
|---|---|
| GS1 | stages are shifted triple rows plus matchings, with distinct placements |
| GS2 | for every colour, all shifted stage edges form a two-component forest with singleton not equal to that colour |
| GS3 | every local support is a forest containing an allowed active basis and satisfying the required edge-disjoint two-component forest condition for participating colours |
| GS4 | final triple satisfies the terminal `A2` collapse pattern |

Structural seed conditions `(E1)-(E7)` from `def:encoded-structural-conditions`:

| predicate | one-line meaning |
|---|---|
| E1 | each stage is one shifted three-colour row and a matching |
| E2 | recorded stage placements are distinct valid tail positions |
| E3 | shifted colour stage edges form the required colour coforest |
| E4 | packet supports are forests with allowed active bases and required previous-forest compatibility |
| E5 | determinant list has `A_r m + B_r` with `B_r = +/-1` |
| E6 | support forests determine active bases with rank-minor gcd `1`, certifying saturation |
| E7 | final triple is oriented and aligned with the terminal `A2` quotient |

## 6. Final 5-line summary

D9 high-even encoded seed exists: `seeds/high_even_encoded/D9_high_even_seed.json`, dimension 9, no fixed modulus in the file; theorem scope is every even `m > 9`.
D9 verification passed at clause level: 7 stages, 27 supports, 60 saturated support/order checks, determinant constants `B = +/-1`, terminal `A2` alignment matched.
D11 high-even encoded seed exists: `seeds/high_even_encoded/D11_high_even_seed.json`, dimension 11, no fixed modulus in the file; theorem scope is every even `m > 11`.
D11 verification passed at clause level: 9 stages, 44 supports, 96 saturated support/order checks, determinant constants `B = +/-1`, terminal `A2` alignment matched.
Verification depth for D9/D11 is forest-incidence/encoded local-block clause-level, not pointwise RF layer enumeration; the manuscript's phase-normalized realization theorem is what converts these verified clauses into RF1/RF2/RF3 schedules.
