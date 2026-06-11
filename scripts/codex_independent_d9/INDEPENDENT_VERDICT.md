# Independent D9 Verdict

| check id | PASS/FAIL | one-line numeric evidence |
|---|---|---|
| C1a | PASS | 7 stages; each row has 1 triple + 3 pairs on 9 labels |
| C1b | PASS | 9 color forests; row_edges=63; isolates=[6, 4, 8, 0, 1, 2, 3, 4, 2]; closings=['6->0', '4->1', '8->2', '0->3', '1->4', '2->5', '3->6', '4->7', '2->8'] |
| C1c | PASS | 21 pair rows; all lambda increments are +/-1 |
| C1d | PASS | 6 nonterminal triples; determinants=[-1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1] |
| C1e | PASS | final shifted triple=[6, 0, 1] |
| C2a | PASS | 28 supports; 63 color traces; inactive derivatives checked=216 |
| C2b | PASS | heights=[2, 1, 8, 0, 5, 4, 7]; max pairwise \|diff\|=8 at r3=8 vs r4=0 |
| C2c | PASS | 7 row bands; per-stage values=[(0, 1, 2, 3), (0, 1, 2, 3), (0, 1, 2, 3), (0, 1, 2, 3), (0, 1, 2, 3), (0, 1, 2, 3), (0, 1, 2, 3)] |
| C3a | PASS | q_T/q_R verified; terminal edges=06,01; reserve grid sites=12 |
| C3b | PASS | max \|diff\| terminal-splice=4, reserve-splice=9, terminal-reserve=3 |
| C3c | PASS | separator w=[1, 1, 1, 0, 1, 0, 1, 1, 1]; diff=-3 proves disjoint over Z |
| C4 | PASS | constants=120; global max \|value\|=9 at reserve-splice r3_p2_P[3, 6] (value=9) |

## ASSUMPTIONs
- C1b ASSUMPTION: active JSON has no final forest/closing-edge field; reconstruct one directed row edge per color/stage from rows_shifted and active_data, then close by isolate->color.
- C2a ASSUMPTION: stage-7 terminal_triple_basic has no A2 witness in active JSON; ledger is checked as one-dimensional terminal support with unit scalar active vectors.
- C2b ASSUMPTION: ledger has one height_shift per stage, not per part; distinctness is checked for the seven stage heights used by splice rows.

## Mismatches / Encoding Notes
- C1b encoding note: no explicit final_forests/closing_edges field is present in certificates/d9_active_anchor_candidate_v1.json.
- C2b wording/encoding note: certificates/d9_affine_splice_placement_ledger.json stores `height_shift` at stage level; individual parts do not have separate height fields.

Overall verdict: PASS
