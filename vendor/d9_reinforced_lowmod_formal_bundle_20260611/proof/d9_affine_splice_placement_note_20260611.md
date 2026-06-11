# D9 affine splice-placement ledger (2026-06-11)

This note records the symbolic affine placement ledger for the splice supports of the D=9 active anchor. It verifies the old-head support-line and same-height separation clauses for the splice ribbons in the high-even range m>9. It does not include the terminal carrier/reserve-plane separation or low-modulus m=4,6,8 RF2 certificates.

## Stage band functionals

For each used height s_r, the four simultaneous splice parts are separated by a row-band functional w_r. The functional is constant on every active support direction in that height, and the part values are 0,1,2,3. Since m>9, these values are distinct modulo m.

| stage | height | active directions | band functional w_r | part values |
|---:|---:|---|---|---|
| 1 | 2 | 03, 06, 15, 28, 47 | [0, 1, 2, 0, 3, 1, 0, 3, 2] | 0,1,2,3 |
| 2 | 1 | 01, 23, 45, 47, 68 | [0, 0, 1, 1, 2, 2, 3, 2, 3] | 0,1,2,3 |
| 3 | 8 | 07, 16, 17, 25, 38 | [0, 0, 1, 2, 3, 1, 0, 0, 2] | 0,1,2,3 |
| 4 | 0 | 04, 06, 18, 27, 35 | [0, 1, 2, 3, 0, 3, 0, 2, 1] | 0,1,2,3 |
| 5 | 5 | 07, 13, 26, 48, 67 | [0, 1, 0, 1, 2, 3, 0, 0, 2] | 0,1,2,3 |
| 6 | 4 | 03, 07, 15, 56, 78 | [0, 1, 2, 0, 3, 1, 1, 0, 0] | 0,1,2,3 |
| 7 | 7 | 02, 24, 38, 57 | [0, 1, 0, 2, 0, 3, 4, 3, 2] | 0,1,2,3 |

## Splice support ledger

### Stage 1 (height 2)

| part | colors P | support M | active edges | band | basepoint b |
|---:|---|---|---|---:|---|
| 0 | [4, 1, 7] | 01, 02, 03, 04, 05, 06, 07 | 03, 06 | 0 | [0, 0, 0, 0, 0, 0, 0, 0, 0] |
| 1 | [2, 5] | 01, 02, 03, 04, 05, 06, 47 | 47 | 1 | [-1, 1, 0, 0, 0, 0, 0, 0, 0] |
| 2 | [0, 6] | 01, 02, 03, 04, 05, 06, 28 | 28 | 2 | [-2, 2, 0, 0, 0, 0, 0, 0, 0] |
| 3 | [8, 3] | 01, 02, 03, 04, 06, 08, 15 | 15 | 3 | [-3, 3, 0, 0, 0, 0, 0, 0, 0] |

### Stage 2 (height 1)

| part | colors P | support M | active edges | band | basepoint b |
|---:|---|---|---|---:|---|
| 0 | [6, 3, 4] | 12, 13, 45, 46, 47, 48 | 45, 47 | 0 | [0, 0, 0, 0, 0, 0, 0, 0, 0] |
| 1 | [1, 2] | 01, 04, 05, 06, 23, 27 | 23 | 1 | [-1, 0, 1, 0, 0, 0, 0, 0, 0] |
| 2 | [8, 0] | 01, 02, 03, 04, 06, 58 | 01 | 2 | [-2, 0, 2, 0, 0, 0, 0, 0, 0] |
| 3 | [5, 7] | 01, 02, 04, 05, 67, 68 | 68 | 3 | [-3, 0, 3, 0, 0, 0, 0, 0, 0] |

### Stage 3 (height 8)

| part | colors P | support M | active edges | band | basepoint b |
|---:|---|---|---|---:|---|
| 0 | [2, 5, 7] | 02, 04, 05, 16, 17 | 16, 17 | 0 | [0, 0, 0, 0, 0, 0, 0, 0, 0] |
| 1 | [4, 0] | 02, 04, 05, 06, 38 | 38 | 1 | [-1, 0, 1, 0, 0, 0, 0, 0, 0] |
| 2 | [3, 6] | 01, 03, 06, 08, 25 | 25 | 2 | [-2, 0, 2, 0, 0, 0, 0, 0, 0] |
| 3 | [1, 8] | 04, 06, 07, 08, 12 | 07 | 3 | [-3, 0, 3, 0, 0, 0, 0, 0, 0] |

### Stage 4 (height 0)

| part | colors P | support M | active edges | band | basepoint b |
|---:|---|---|---|---:|---|
| 0 | [4, 6, 0] | 02, 04, 06, 35 | 04, 06 | 0 | [0, 0, 0, 0, 0, 0, 0, 0, 0] |
| 1 | [1, 8] | 04, 06, 12, 18 | 18 | 1 | [-1, 1, 0, 0, 0, 0, 0, 0, 0] |
| 2 | [3, 5] | 01, 06, 35, 37 | 35 | 2 | [-2, 2, 0, 0, 0, 0, 0, 0, 0] |
| 3 | [2, 7] | 02, 05, 27, 36 | 27 | 3 | [-3, 3, 0, 0, 0, 0, 0, 0, 0] |

### Stage 5 (height 5)

| part | colors P | support M | active edges | band | basepoint b |
|---:|---|---|---|---:|---|
| 0 | [4, 0, 6] | 03, 07, 26 | 07, 26 | 0 | [0, 0, 0, 0, 0, 0, 0, 0, 0] |
| 1 | [5, 7] | 02, 05, 13 | 13 | 1 | [-1, 1, 0, 0, 0, 0, 0, 0, 0] |
| 2 | [8, 3] | 02, 06, 48 | 48 | 2 | [-2, 2, 0, 0, 0, 0, 0, 0, 0] |
| 3 | [1, 2] | 01, 05, 67 | 67 | 3 | [-3, 3, 0, 0, 0, 0, 0, 0, 0] |

### Stage 6 (height 4)

| part | colors P | support M | active edges | band | basepoint b |
|---:|---|---|---|---:|---|
| 0 | [6, 0, 7] | 07, 15 | 07, 15 | 0 | [0, 0, 0, 0, 0, 0, 0, 0, 0] |
| 1 | [1, 2] | 01, 56 | 56 | 1 | [-1, 1, 0, 0, 0, 0, 0, 0, 0] |
| 2 | [3, 4] | 01, 78 | 78 | 2 | [-2, 2, 0, 0, 0, 0, 0, 0, 0] |
| 3 | [5, 8] | 02, 03 | 03 | 3 | [-3, 3, 0, 0, 0, 0, 0, 0, 0] |

### Stage 7 (height 7)

| part | colors P | support M | active edges | band | basepoint b |
|---:|---|---|---|---:|---|
| 0 | [8, 2, 3] | 02 | 02 | 0 | [0, 0, 0, 0, 0, 0, 0, 0, 0] |
| 1 | [4, 6] | 24 | 24 | 1 | [-1, 1, 0, 0, 0, 0, 0, 0, 0] |
| 2 | [7, 0] | 57 | 57 | 2 | [-2, 2, 0, 0, 0, 0, 0, 0, 0] |
| 3 | [5, 1] | 38 | 38 | 3 | [-3, 3, 0, 0, 0, 0, 0, 0, 0] |

## Verification conditions

The verifier checks the following finite symbolic conditions.

1. For every stage r, w_r vanishes on every active edge direction used at that height. Thus each splice support cylinder lies in a fixed row-band fiber.

2. The four part band values at each height are 0,1,2,3, hence the four simultaneous physical supports are disjoint for every modulus m>9.

3. For every affected color c and every inactive support edge f, the descendant coordinate lambda_f is constant on the active support directions. Equivalently, lambda_f(alpha_e)=0 for every active e.

4. The omitted-component exterior coordinate is also constant on every active support direction.

5. The active coordinate vector of each physical increment agrees with the active-anchor certificate: signed unit in pair rows and primitive A2 vectors in triple rows.


## Proven splice-placement statement

Let U_{r,P}=b_{r,P}+span(A_{r,P}) be the affine support cylinder in the layer of height s_r, where A_{r,P} is the active edge set printed above. Then, after contraction by each affected color c's previous forest F_{c,<r}, the old heads of U_{r,P} lie on the printed support line/plane: all inactive support coordinates and the omitted exterior coordinate are fixed, while active coordinates vary freely. The row-band functional separates the four simultaneous parts at the same height. Therefore the old-head transversality and splice-support separation clauses of the anchor-schedule realization are satisfied for all D9 splice ribbons in the high-even range m>9.
