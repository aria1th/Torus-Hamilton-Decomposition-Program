# D9 all-even anchor theorem (2026-06-11)

## Theorem

For every even modulus \(m\ge4\),

\[
  \mathrm{HED}(9,m)
\]

holds.

## Proof

Split into two cases.

### Case 1: \(m>9\)

The symbolic D9 high-even anchor theorem applies.  Its ingredients are:

1. the D9 active graph/coforest anchor (`d9_active_anchor_candidate_v1.json`);
2. the symbolic affine splice-placement ledger (`d9_affine_splice_placement_ledger.json`);
3. the terminal carrier and endpoint reserve frame
   (`d9_terminal_reserve_frame_candidate.json`).

The active anchor gives terminal diagonal treeing, simultaneous rooted coforest
completions, signed pair-unit rows, primitive \(A_2\) triple rows, and terminal
form \((6,0,1)\).  The splice-placement ledger realizes all active supports as
affine cylinders with old-head transversality and same-height row-band separation.
The terminal/reserve frame gives a separated terminal carrier and twelve reserve
sites.  Projection-separation differences have absolute value at most \(9\), hence
are nonzero modulo every even \(m>9\).  Therefore the anchor-schedule realization
criterion gives \(\mathrm{HED}(9,m)\).

### Case 2: \(m\in\{4,6,8\}\)

Use the finite low-modulus placement certificate
`d9_lowmod_finite_placement_candidate.json`.  It keeps the same active D9 anchor
and support directions but chooses basepoints directly in \(K_{9,m}\).  The finite
verifier enumerates all splice support cosets, the terminal carrier plane, and
the reserve plane.  It checks:

* old-head transversality and omitted-component constancy;
* signed unit pair splices;
* primitive active \(A_2\) triple splices;
* disjointness of all splice supports whose heights coincide modulo \(m\);
* disjointness of the terminal carrier and reserve plane from all splice supports
  and from each other;
* twelve distinct reserve sites.

Thus the finite anchor-schedule realization criterion gives
\(\mathrm{HED}(9,m)\) for \(m=4,6,8\).

The two cases cover all even \(m\ge4\). ∎

## Consequence for the odd branch

Together with the corrected midpoint-collision paired growth,

\[
  \mathrm{HED}(9,m)\Rightarrow\mathrm{HED}(11,m)
  \Rightarrow\mathrm{HED}(13,m)\Rightarrow\cdots,
\]

the odd branch \(d\ge9\) is closed for every even \(m\ge4\), without using the
old chained \(7\to9\) step.
