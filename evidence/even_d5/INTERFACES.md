# Next kernel interfaces (specification, not built Lean code)

The integrated paper removes an external ordinary-D5 assumption at the level of
mathematical proof. No new kernel theorem is claimed by this document.

## 1. ChronologicalTransversal

Parameters: a finite abelian group X; subgroups H,W with X=H direct-sum W;
a permutation S whose orbits are precisely H-cosets; P in Equiv.Perm X;
a fixed b with P(x)-x-b in H; e in W of order m; an affine coset C=z+W.

Construct the piecewise permutation J by addition of e on C and identity outside.
Return a theorem that the orbits of S * (P.symm * J * P) are precisely
H+<e>-cosets. In Lean, verify multiplication conventions before adopting this
surface notation. The core proof uses an exact section A=P^{-1}(C), not an
assumed conjugation law for the raw cylinder.

Sublemmas:
- P permutes the H-cosets by a fixed translate.
- A meets every S-orbit exactly once.
- the induced relative permutation on A has m-cycles through m distinct old
  orbits, grouped by H+<e>.
- first-return source surgery concatenates these orbit segments with no unhit
  orbit term remaining.

## 2. IntegerComplementCertificate

Store the concrete integer matrices Q=[H^- W_P], their integral inverses for
m>=6, and e-coordinates Q^{-1}e=(0,v). Prove finite equalities over Z first.
Reduce the identities modulo m; do not ask a field-rank tactic to handle ZMod m.
At m=4, use a separate certificate with Q inverse modulo 4.

The twelve prefix obligations are not discharged by determinant checks alone.
They require the pointwise congruence P(x)=x+b mod H^- from the actual already
inserted displacements. This is the exact bridge to module 1.

## 3. D5PlanarEndpoint

Define omega, j_0,j_1,j_2, the coordinate-point families A,B,C,X_t,Y_t,Z_t, and the
three fibre-swap involutions. Prove the three displayed 2m-cycle lists by a
finite index-range case split. Required subgoals include disjointness and
coverage, successor identities at every junction, and empty ranges at m=4.
The finite Python loop to m=256 is a regression oracle, not a proof of this
quantified statement.

## 4. D5FourTour

The JSON contains five complete tours on 1024 vertex IDs. Decode IDs into
(root coordinates, height), then use the explicit physical fifth coordinate
h-sum(root) mod 4. The checker must prove all of:
- each list has length 1024 and contains every vertex once;
- the wrap-around edge is included;
- each successive difference is exactly one positive standard basis vector;
- at each source, the five tours use all five directions once.

Prove checker_sound independently of the constructor. Record whether the
certificate equality was discharged by kernel reduction or by a separate
trusted computation mechanism. A Python True value is not that proof term.

## 5. FinalCaseAssembly

Use the current RelativeCollar theorem for odd d>=7, its empty-active
specialization for all even d, the internal D3 theorem, and ordinary D5.
The final case split should not import the retired endpoint-growth framework.
An optional all-m>=3 corollary imports the separately verified odd-modulus
endpoint with its exact theorem type and pinned source revision.
