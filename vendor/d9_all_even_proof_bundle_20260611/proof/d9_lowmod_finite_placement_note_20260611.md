# D9 low-modulus finite placement certificate (2026-06-11)

## Scope

This note closes the finite residual moduli left by the symbolic high-even D9 anchor:

\[
  m\in\{4,6,8\}.
\]

The active D9 anchor is unchanged.  The support directions, signed pair-unit rows,
primitive active \(A_2\) triple rows, and terminal form \((6,0,1)\) are exactly the
same as in `d9_active_anchor_candidate_v1.json`.  Only the affine basepoints of
splice supports, the terminal carrier, and the endpoint reserve plane are chosen
separately modulo \(m\).

The finite certificate is `d9_lowmod_finite_placement_candidate.json`; it is
verified by `verify_d9_lowmod_finite_placement.py`.

## Proposition

For each \(m\in\{4,6,8\}\), the D9 active anchor admits a finite affine placement
realization modulo \(m\).  More explicitly, the certificate gives:

1. 28 splice supports
   \[
      U_{r,P}=b_{r,P}+\langle A_{r,P}\rangle\subset K_{9,m},
      \qquad K_{9,m}=\{x\in(\mathbb Z/m)^9:\sum_i x_i=0\};
   \]
2. a terminal carrier plane
   \[
      Q_T=b_T+\langle 06,01\rangle;
   \]
3. an endpoint reserve plane
   \[
      Q_R=b_R+\langle 24,35\rangle;
   \]
4. twelve distinct reserve singleton sites in \(Q_R\);
5. pairwise disjointness of all splice supports whose height shifts coincide
   modulo \(m\);
6. disjointness of \(Q_T\) and \(Q_R\) from all splice supports, and from each
   other;
7. all old-head transversality equations, omitted-component constancy equations,
   signed pair-unit equations, and primitive \(A_2\) determinant equations.

Consequently the D9 anchor-schedule realization criterion holds for
\(m=4,6,8\).

## Proof

Fix \(m\in\{4,6,8\}\).  The verifier works inside the finite root-flat group
\(K_{9,m}\).  For a listed support with active edge set \(A_{r,P}\), it enumerates
its affine coset

\[
  b_{r,P}+\langle A_{r,P}\rangle.
\]

The basepoint is checked to lie in \(K_{9,m}\).  The active directions are the
same as in the symbolic active-anchor certificate, so the already verified
coforest support data remain valid.  The finite verifier recomputes the
contracted previous forest \(F_{c,<r}\) for every affected color \(c\), recomputes
all descendant coordinates, and checks that every inactive coordinate and the
omitted-component coordinate vanish on all active directions.  Thus the old-head
image of each affine support is exactly the required printed support line or
support plane in the contraction quotient.

For pair rows the verifier checks that the active descendant increment is a unit
modulo \(m\).  In fact the integer value is always \(\pm1\), hence a unit for all
three moduli.  Therefore the signed rank-one splice is cyclic on
\(\mathbb Z/m\).

For non-terminal triple rows, the verifier recomputes the three active vectors in
\((\mathbb Z/m)^2\) and checks that every pairwise determinant is a unit modulo
\(m\).  The integer determinants are \(\pm1\), hence each active two-plane is a
primitive \(A_2\)-splice.

The only extra difficulty in low modulus is height folding: some high-even stage
shifts become equal modulo \(m\).  The finite certificate handles this directly by
choosing basepoints so that all splice supports with equal folded height are
pairwise disjoint.  The verifier enumerates the actual finite cosets and checks
these intersections are empty.

The terminal carrier and reserve plane are also enumerated as finite planes.  The
verifier checks that both planes are disjoint from every splice support and from
each other.  It then checks that the twelve listed reserve sites are exactly
points of the reserve plane and are pairwise distinct.

Thus RF2 is preserved by the finite layer-comparison switch lemma: at every
folded height, the localized switches have disjoint supports, and each support is
closed under the corresponding comparison map.  The quotient splice algebra is
unchanged from the active D9 anchor, so each color return is a single cycle.  The
terminal carrier and endpoint reserve clauses are also realized.

Therefore the D9 high-even chain datum is realized for this \(m\).  Since the
argument applies to \(m=4,6,8\), the finite residual moduli are closed. ∎

## Verification transcript

`verify_d9_lowmod_finite_placement.py` prints:

```text
OK: D9 low-modulus finite placement verified
m=4: 28 splice supports verified; terminal size=16 reserve size=16; reserve sites=12
m=6: 28 splice supports verified; terminal size=36 reserve size=36; reserve sites=12
m=8: 28 splice supports verified; terminal size=64 reserve size=64; reserve sites=12
```
