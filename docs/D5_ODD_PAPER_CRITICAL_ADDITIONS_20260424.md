# D5 odd paper: critical additions to consider, 2026-04-24

This note checks the paper draft against the Lean endpoint.  No mathematical
contradiction was found, but several places should be strengthened before the
paper is treated as final.

## Highest priority: split off the \(m=3\) proof path

The paper states the normalized cycle lemma for every odd \(m\ge 3\):

```tex
\begin{lemma}[Cycle lemma]
For every odd \(m\ge3\), the normalized return map \(G\) is a single \(m^4\)-cycle on \(A_m\).
\end{lemma}
```

The Lean development proves this in two different ways:

- for \(m\ge5\), by the conceptual first-return proof through \(\Sigma\);
- for \(m=3\), by a finite 81-state rank certificate for each color.

The paper tries to include \(m=3\) inside the first-return discussion by saying
that empty block words handle the boundary case.  The verifier confirms the
closed formulas for \(m=3\), but the appendix explicitly says the verifier is
audit-only.  This is the most likely reviewer pressure point.

Recommended fix:

1. State the first-return/cycle proof as \(m\ge5\), or explicitly mark the
   \(m=3\) boundary checks inside the proof.
2. Add a separate lemma:

   ```tex
   \begin{lemma}[The \(m=3\) return certificate]
   For the schedule \((\mathrm{Sch}_3)\), every color return \(R_c\) is a
   single cycle on \(A_3\).
   \end{lemma}
   ```

3. Prove it by a finite rank certificate, matching the Lean theorem
   `m3Schedule_allColorHamiltonian`.  The paper can either include the rank
   table as supplementary data or cite the distributed verifier/certificate.

This change would align the paper with the actually formalized proof architecture.

## High priority: make the Cayley edge partition explicit

The final proof currently says the five colors partition the arc set because
each row \(c\mapsto d_t(w,c)\) is a permutation.  This is correct, but it is
worth making the object explicit:

```tex
E_c=\{(x,x+e_{d_{\sigma(x)}(\iota_{\sigma(x)}x,c)}):x\in(\mathbb Z_m)^5\}.
```

Then add:

- for each fixed \(x\), the five directions
  \(d_{\sigma(x)}(\iota_{\sigma(x)}x,c)\) are exactly \(\mathbb Z_5\);
- hence the sets \(E_c\) partition the directed Cayley arc set;
- if \(R_c\) is one \(m^4\)-cycle on \(A_m\), then \(E_c\) is one directed
  Hamilton cycle of length \(m^5\).

This is exactly what `D5Odd/Cayley.lean` now formalizes.

## High priority: strengthen the return criterion statement

The return criterion is mathematically standard, but the current proof is quite
compressed.  For safety, state it with the hypotheses it uses:

- every color edge increases the layer by one;
- each vertex has exactly one outgoing edge of that color;
- \(R_c\) is the \(m\)-step map obtained by following that color.

Then prove explicitly that if \(R_c\) has a cycle
\((w_0,\ldots,w_{\ell-1})\) on \(A_m\), the lifted orbit has length \(m\ell\)
because the layer coordinate advances through \(0,1,\ldots,m-1\).  This avoids
any hidden assumption about intermediate layers.

## Medium priority: clarify what is proved by the 27-cell certificate

The matching certificate is probably acceptable, but the exact-cover proof says
that the displayed table rules out overlaps and gives exhaustion by a finite
Boolean comparison.  A skeptical reader may want a sharper certificate statement.

Recommended addition:

```tex
The certificate consists of the 27 row signatures in Table X plus the following
finite claim: for every assignment of the five coordinates to the symbolic
classes \(0,1,-1,\mathrm{other}\) compatible with the root-flat relation,
exactly one of the five predecessor tests \(p(Z(y-q_i))=i\) holds.
```

Then say this finite claim is included as a supplementary machine-checkable
certificate and was also formalized in Lean.  For \(m=3\), note that the
``other'' class may be empty, but the symbolic test remains sound because
\(0,1,-1\) are still distinct in \(\mathbb Z_3\).

## Medium priority: name the color-conjugacy correction carefully

The paper already has the important correction

```tex
\rho_c(q_i)=q_{i+c}-q_{4+c}.
```

This is good and matches the formalization.  It may be worth adding one sentence
that this is why the color transfer is affine rather than a bare coordinate
rotation.  This prevents readers from mentally replacing the proof with the
false simpler identity \(\rho_c(q_i)=q_{i+c}\).

## Lower priority: update the verifier appendix language

The appendix says the verifier is audit-only.  That is good, but if the paper
uses the \(m=3\) rank certificate or the exact-cover certificate as finite
certificates, distinguish:

- audit-only numerical tests for many odd \(m\);
- finite certificates that are part of the proof, if any.

Right now these are close enough in wording that a reviewer might ask which
computations are proof inputs and which are sanity checks.

## Bottom line

The paper does not seem to be missing a new mathematical idea.  The critical
addition is expository/proof-architecture: make the \(m=3\) case explicitly
finite-certified or restrict the hand first-return theorem to \(m\ge5\), then
state the Cayley edge partition and return lift as explicit lemmas.
