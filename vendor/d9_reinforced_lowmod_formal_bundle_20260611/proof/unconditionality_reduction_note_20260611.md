# Unconditionality reduction after A3 (2026-06-11)

## Corrected endpoint-collision paired growth

For ordinary paired growth rows `(0 1)(-1 -2)` and `(3 4)(2 1)`, replace endpoint-boundary avoidance by midpoint-collision avoidance.

For row `(0 1)(-1 -2)`, the quotient cut is `theta(-1)=1`, `theta(0)=theta(1)=theta(-2)=0`.  A translated old line can be nonzero only for endpoint pairs `(-1,1)` or `(-1,-2)`, hence only at midpoint centers `0` and `-3/2`.  Since tested centers are `{rho-1,rho,rho+1}`, at most six phases are forbidden.  In a label set of odd size `D >= 11`, an admissible phase exists.

For row `(3 4)(2 1)`, the quotient cut is `theta(2)=1`, `theta(3)=theta(4)=theta(1)=0`.  Nonzero endpoint pairs are `(2,4)` and `(2,1)`, with midpoint centers `3` and `3/2`; again at most six phases are forbidden, so `D >= 11` supplies an admissible phase.

Therefore `HED(D-2,m) => HED(D,m)` for odd `D >= 11`, every even `m >= 4`, once the input `HED` exists.

## Main reduction

If `HED(9,m)` holds for every even `m >= 4`, then the even-modulus theorem follows without chained `7 -> 9`:

- even `d`: phase doubling/product branch unchanged;
- odd `d <= 7`: existing finite-low-dimensional inputs handle `3,5,7` as before;
- odd `d = 9`: direct `HED(9,m)`, then forget chain fields for `HD`;
- odd `d >= 11`: iterate corrected paired growth from `HED(9,m)`.

Thus the remaining unconditionality target is exactly direct `HED(9,m)` for all even `m >= 4`.

## Audit of current D9 candidate

The candidate `d9_anchor_candidate.json` verifies terminal diagonal treeing and simultaneous rooted-coforest support completions, but it is not a full anchor realization.  A stricter pair-row tail--head audit requires a common rank-one active edge with descendant coordinate `+1` for both colors in each pair row.  The current candidate fails 14 pair parts under this necessary active-identity test.  Hence it cannot yet be cited as a complete `HED(9,m)` proof.

Files:

- `verify_d9_anchor_candidate.py`: tree/coforest support verifier;
- `audit_d9_pair_active_identity.py`: stricter pair active-identity audit.
