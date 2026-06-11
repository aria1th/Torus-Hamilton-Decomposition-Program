# D9 terminal carrier and endpoint reserve frame (2026-06-11)
This note records the symbolic high-even terminal/reserve frame for the D9 active anchor. It covers every even modulus m>9. Low moduli m=4,6,8 are not covered here.
## Terminal carrier
Terminal chronological triple: `[8, 2, 3]` at height `7`, shifted root vertices `[6, 0, 1]`.
Terminal carrier plane: `q_T + <06,01>`, with `q_T=[0, 0, 2, 2, -4, 0, 0, 0, 0]`.
Terminal alignment rows: `[[-1, 0], [1, 1], [0, -1]]`, permutation `[0, 1, 2]`, signs `[1, 1, -1]`.
The verifier checks 28 separating functionals, one for each splice support cylinder. Each functional vanishes on both the terminal carrier directions and the splice support directions, and its constant-value difference has absolute value at most 4. Therefore it is nonzero modulo every m>9.
## Endpoint reserve plane
Reserve plane: `q_R + <24,35>`, with `q_R=[3, 4, 3, 5, -15, 0, 0, 0, 0]`.
Reserve sites use coefficient grid `{0,1,2,3} x {0,1,2}`; hence there are D+3=12 sites.

| site | coeff | point |
|---|---:|---|
| `U0` | `(0, 0)` | `[3, 4, 3, 5, -15, 0, 0, 0, 0]` |
| `U1` | `(1, 0)` | `[3, 4, 2, 5, -14, 0, 0, 0, 0]` |
| `U2` | `(2, 0)` | `[3, 4, 1, 5, -13, 0, 0, 0, 0]` |
| `U1_c` | `(3, 0)` | `[3, 4, 0, 5, -12, 0, 0, 0, 0]` |
| `U2_c` | `(0, 1)` | `[3, 4, 3, 4, -15, 1, 0, 0, 0]` |
| `U3_c` | `(1, 1)` | `[3, 4, 2, 4, -14, 1, 0, 0, 0]` |
| `U4_c` | `(2, 1)` | `[3, 4, 1, 4, -13, 1, 0, 0, 0]` |
| `U5_c` | `(3, 1)` | `[3, 4, 0, 4, -12, 1, 0, 0, 0]` |
| `U6_c` | `(0, 2)` | `[3, 4, 3, 3, -15, 2, 0, 0, 0]` |
| `U7_c` | `(1, 2)` | `[3, 4, 2, 3, -14, 2, 0, 0, 0]` |
| `U8_c` | `(2, 2)` | `[3, 4, 1, 3, -13, 2, 0, 0, 0]` |
| `U_star` | `(3, 2)` | `[3, 4, 0, 3, -12, 2, 0, 0, 0]` |

The verifier checks 29 separating functionals: one against each of the 28 splice supports and one against the terminal carrier plane. Each difference is nonzero with absolute value at most 9, so it is nonzero modulo every m>9.
## Separation lemma used
Let `A=a+<V>` and `B=b+<W>` be affine subspaces of the root-flat lattice over Z/mZ. If there is an integer functional `ell` with `ell(V)=ell(W)=0` and `0<|ell(a-b)|<m`, then `A` and `B` are disjoint modulo m. All certificate rows have `|ell(a-b)|<=9`, so the check is uniform for every even `m>9`.
## Verification
Verified by `/mnt/data/verify_d9_terminal_reserve_frame.py`; transcript in `/mnt/data/d9_terminal_reserve_frame_verification.txt`.
