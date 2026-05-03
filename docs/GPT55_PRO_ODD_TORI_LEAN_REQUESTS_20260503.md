# GPT-5.5 Pro Requests for Odd Tori Lean Formalization

Date: 2026-05-03.

This note records large Lean-formalization subtasks that are worth sending to a
frontier model before implementation starts.  The local goal is recorded in
`docs/ODD_TORI_GLOBAL_FORMALIZATION_GOAL_20260503.md`.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

## Priority Ranking

The Lean-heavy subtasks are:

1. Active Hall/Hoffman realization and controlled residue rounding.
2. Signed transportation and the prefix-count count branch.
3. Extended prefix-count primitiveity and full-vertex base-tail skew lift.
4. Dyadic-triadic interval arithmetic and the `d < 29` boundary witness table.
5. D2 seed formalization.

Only the first two are large enough to justify GPT-5.5 Pro immediately.  The
others are better handled locally after the theorem interface is fixed.

## Request 1: Active Hall-Slack Lean Plan

Purpose:

Produce a Lean-friendly decomposition of the active Hall/Hoffman realization
part of the base-tail theorem.  This is likely the heaviest proof block because
it mixes finite assignment, Hall cuts, total unimodularity/network flow or an
alternative certificate interface, controlled rounding, and modular residue
constraints.

Prompt:

```text
We are formalizing in Lean 4/mathlib a theorem about directed Hamilton
decompositions of equal-side directed tori.  Existing repo interfaces include:

- Shared.CayleyHamiltonDecomposition d m
- RoundComposite.OddUniformSolved
- product/composite lift infrastructure
- root-flat/skew-product/single-cycle lemmas

The new global theorem should prove every odd d >= 3 and odd m >= 3 from seeds
D2,D3,D5,D7 plus two manuscript mechanisms:

1. prefix-count count branch for odd d >= 5, odd m >= d;
2. base-tail Hall-slack branch for odd m < d.

Please focus only on the Lean formalization of the active Hall-slack branch.

Mathematical statement to formalize:

Let m < d be odd.  Let b < d and T = d - b.  Suppose:

- D_b(m) has a directed Hamilton decomposition;
- d = k_1 + ... + k_b;
- for each j, m is a sum of k_j positive units modulo m;
- T > b;
- m^b > m*d*T.

Then D_d(m) has a directed Hamilton decomposition.

The manuscript proof uses a full-vertex base-tail certificate.  The base vertex
set is X = (ZMod m)^(b+1), containing the layer coordinate and first b prefix
coordinates.  The remaining T-1 prefix coordinates form the tail.  The base
multigraph has one copy of each g_0,...,g_{b-1} and T active copies of g_b.

The base is decomposed by cylinder decompositions from D_b(m).  Active arcs
form a bipartite incidence graph Gamma subset X x C.  Every base vertex has
active degree T.  An active symboling assigns each active edge a symbol in
S_T = {0, Delta, 2, ..., T-1}, every base vertex seeing every active symbol
exactly once.  For each color c, the active symbol counts M[c,sigma] must
satisfy prefix-count unit residues:

M[c,0]      ==  u_c mod m
M[c,Delta]  == -u_c mod m
M[c,k]      ==  0 mod m for numeric k

where u_c are units with sum zero mod m.  For odd d use one triple 1,1,-2 and
pairs 1,-1.

The realization theorem in the manuscript:

- Active Hall criterion: a nonnegative integer matrix M is realizable by an
  active symboling iff row sums, column sums, and Hoffman cut inequalities hold:

  M(U,S) <= sum_x min(|A(x) cap U|, |S|)

- Barycenter B[c,sigma] = A_c/T lies in the Hall polytope.
- If T > b, every nontrivial Hall cut has slack at least
  (m^b/T) * min(|S|, T-|S|).
- Controlled residue rounding: if m^b > m*d*T, there is a nonnegative integer
  M with the desired row sums, column sums, residues, and all Hall inequalities.
- Then Hall realizes M, and the residues give the tail prefix-count unit
  conditions.

Task:

1. Propose precise Lean theorem statements and structures for this active
   Hall-slack block.
2. Separate the proof into lemmas of manageable size.
3. Identify which lemmas are likely already in mathlib and which should be
   axiomatized temporarily or proved directly.
4. Suggest a proof-assistant-friendly alternative if formalizing Hoffman/TU
   max-flow is too expensive.  For example, should we use a finite certificate
   interface for active symboling instead of proving Hall realization in Lean?
5. Give a recommended implementation order and file/module layout.
6. Provide Lean-like signatures, not just prose.
7. Highlight any mathematical gaps or hidden assumptions in the manuscript
   formulation that would block formalization.

Be pragmatic.  The output should help a Lean engineer start implementing this
without rediscovering the proof architecture.
```

## Request 2: Signed Transportation Count-Branch Lean Plan

Purpose:

Produce a Lean-friendly decomposition of the count branch for `m >= d`.  This
is the other large formalization block because the manuscript uses signed
transportation, a `q >= 2` branch, and a restricted `q = 1` branch.

Prompt:

```text
We are formalizing in Lean 4/mathlib a theorem about directed Hamilton
decompositions of equal-side directed tori.  Existing repo interfaces include:

- Shared.CayleyHamiltonDecomposition d m
- RoundComposite.OddUniformSolved
- product/composite lift infrastructure
- root-flat/skew-product/single-cycle lemmas

The new global theorem should prove every odd d >= 3 and odd m >= 3 from seeds
D2,D3,D5,D7 plus two manuscript mechanisms:

1. prefix-count count branch for odd d >= 5, odd m >= d;
2. base-tail Hall-slack branch for odd m < d.

Please focus only on the Lean formalization of the prefix-count count branch.

Target theorem:

For odd d >= 5 and odd m >= d, D_d(m) has a directed Hamilton decomposition.

The manuscript uses a symbol set

S_d = {0, Delta, 2, 3, ..., d-1}

and a prefix-count primitiveity theorem.  For a color row with counts

N_0, N_Delta, N_2, ..., N_{d-1},

the return map is single-cycle if:

gcd(N_0, m) = 1
gcd(N_k - N_Delta, m) = 1 for 2 <= k <= d-1.

A prefix-admissible count matrix has row sums m, column sums m, and every row
satisfies those primitiveity conditions.  A count matrix can be decomposed into
layer permutations, giving the root-flat certificate.

The count branch constructs such matrices for all odd d >= 5, odd m >= d.  The
manuscript writes m = (d-1)q + r.

- For q >= 2, it uses signed transportation with entries in {+/-1,+/-2}.
- For q = 1, i.e. d <= m <= 2d-3, nonnegativity is tighter.  The construction
  first builds a {+/-1}-matrix and then changes matched +1 entries to +2 and one
  carefully chosen -1 entry to -2.

Task:

1. Propose precise Lean theorem statements for:
   - prefix-count primitiveity;
   - prefix-admissible count matrix;
   - count matrix criterion;
   - q >= 2 signed transportation branch;
   - q = 1 restricted branch;
   - final count branch for all odd m >= d.
2. Split the signed transportation proof into Lean-sized arithmetic/combinatorial
   lemmas.
3. Identify a representation for matrices that keeps proofs tractable:
   Fin d -> Fin d -> Int/Nat, finite support maps, lists, or arrays.
4. Suggest how to avoid formalizing a full regular bipartite matching theorem
   if possible.  Is an explicit layer-permutation construction better for Lean?
5. Provide Lean-like signatures and proof dependencies.
6. Identify hidden assumptions in the manuscript's signed transportation branch,
   especially around nonnegativity, row/column sums, and branch coverage.
7. Recommend the implementation order and file/module layout.

Be pragmatic.  The output should help a Lean engineer begin implementation and
decide whether to formalize the combinatorial matrix construction directly or
replace part of it with a certificate interface.
```

## Polling

The request ids, once submitted, should be recorded below.

```text
active_hall_slack:
  response_id = resp_01bc2f30d606b77c0069f781eded40819ca33fc85820d0d3c4
  initial_status = queued

signed_transport_count_branch:
  response_id = resp_02e89d0269448d6b0069f781f016888190bfe73ff01f394e06
  initial_status = queued
```

Retrieve with the Responses API:

```bash
set -a
. /data/angel/repos/etc/.env
set +a
curl -s -H "Authorization: Bearer $OPENAI_API_KEY" \
  https://api.openai.com/v1/responses/resp_01bc2f30d606b77c0069f781eded40819ca33fc85820d0d3c4
curl -s -H "Authorization: Bearer $OPENAI_API_KEY" \
  https://api.openai.com/v1/responses/resp_02e89d0269448d6b0069f781f016888190bfe73ff01f394e06
```
