# D9 active-anchor repair note (2026-06-11)

This note records the repaired D9 graph/coforest anchor found after the stage-5
triple obstruction in the earlier candidate.

## Repaired shifted rows

The shifts remain

\[
(2,1,8,0,5,4,7).
\]

The shifted rows are

| stage | shift | shifted triple | shifted pairs |
|---:|---:|---|---|
| 1 | 2 | (6,3,0) | (4,7), (2,8), (1,5) |
| 2 | 1 | (7,4,5) | (2,3), (0,1), (6,8) |
| 3 | 8 | (1,4,6) | (3,8), (2,5), (0,7) |
| 4 | 0 | (4,6,0) | (1,8), (3,5), (2,7) |
| 5 | 5 | **(0,5,2)** | **(1,3), (4,8), (6,7)** |
| 6 | 4 | (1,4,2) | (5,6), (7,8), (0,3) |
| 7 | 7 | (6,0,1) | (2,4), (5,7), (3,8) |

The only row changed from the earlier coforest candidate is stage 5.

## Terminal color forests

The verifier obtains the following one-isolate final forests.  In each row,
adding the displayed closing edge makes a spanning tree.

| color | isolate | closing | forest edges |
|---:|---:|---|---|
| 0 | 6 | 6→0 | 28, 01, 38, 04, 25, 24, 57 |
| 1 | 4 | 4→1 | 03, 23, 07, 18, 67, 56, 38 |
| 2 | 8 | 8→2 | 47, 23, 14, 27, 67, 56, 01 |
| 3 | 0 | 0→3 | 15, 45, 25, 35, 48, 78, 16 |
| 4 | 1 | 1→4 | 36, 57, 38, 46, 05, 78, 24 |
| 5 | 2 | 2→5 | 47, 68, 46, 35, 13, 03, 38 |
| 6 | 3 | 3→6 | 28, 47, 25, 06, 02, 14, 24 |
| 7 | 4 | 4→7 | 06, 68, 16, 27, 13, 12, 57 |
| 8 | 2 | 2→8 | 15, 01, 07, 18, 48, 03, 06 |

## Active A2 triple witnesses

For stages 1--6, the listed support M is a simultaneous rooted coforest
completion.  The two active edges give the active coordinates.  The three
vectors are the descendant-coordinate increments of the three affected colors.
Every pair of vectors has determinant ±1.

| stage | affected colors P | support M | active edges | vectors | pairwise determinants |
|---:|---|---|---|---|---|
| 1 | (4,1,7) | 01,02,03,04,05,06,07 | 03,06 | (1,-1), (-1,0), (0,1) | -1, 1, -1 |
| 2 | (6,3,4) | 12,13,45,46,47,48 | 45,47 | (0,-1), (-1,0), (-1,1) | -1, -1, -1 |
| 3 | (2,5,7) | 02,04,05,16,17 | 16,17 | (0,-1), (1,1), (-1,0) | 1, -1, 1 |
| 4 | (4,6,0) | 02,04,06,35 | 04,06 | (1,1), (0,1), (1,0) | 1, -1, -1 |
| 5 | (4,0,6) | 03,07,26 | 07,26 | (1,0), (-1,-1), (0,-1) | -1, -1, 1 |
| 6 | (6,0,7) | 07,15 | 07,15 | (1,-1), (0,1), (1,0) | 1, 1, -1 |

Stage 7 has terminal shifted triple `(6,0,1)`, i.e. `(t,0,1)` with `t=6`.
The terminal A2 cyclicity is supplied by the uniform terminal-block lemma.

## Pair-row unit condition

Every pair row contains its physical pair edge in the support, and the two
descendant-coordinate increments are units ±1.  The full table is stored in the
JSON certificate and checked by the active verifier.

## Files

- `d9_active_anchor_candidate_v1.json` — graph/coforest certificate.
- `verify_d9_active_anchor_candidate.py` — active-anchor graph verifier.
- `d9_active_anchor_candidate_v1_verification.txt` — verification transcript.

## Status

This certificate proves the D9 active graph/coforest anchor predicates:
terminal diagonal treeing, simultaneous rooted coforest completions, signed
pair-unit rows, active A2 triple rows for stages 1--6, and terminal-stage
coforest support.  To promote it to a full HED(9,m) certificate, the manuscript
still needs the D9 analogue of the anchor-schedule realization data: old-head
placement ledger, support-line separation/reserve frame, and low-modulus
pointwise RF2 realization or a uniform lemma replacing the finite low-modulus
checks.
