# D7 m=3,5 Lean Certificate Appendix Text

Date: 2026-05-08.

This note is the manuscript-facing appendix/reproducibility text for the finite
`D_7` odd base cases `m = 3` and `m = 5`.  It records the exact Lean certificate
interface and theorem statements, so the paper can cite the small cases without
leaving them as informal computer checks.

## Appendix Statement

For `D_7` and odd modulus `m`, the Lean formalization uses a root-flat schedule
interface.  For the two finite base moduli `m = 3` and `m = 5`, the schedule is
given by explicit zero-set selector tables and finite rank certificates.  The
formal certificate has four fields:

```lean
structure D7Odd.Handoff.RootFlatCertificate
    (m : Nat) [NeZero m] where
  schedule : D7Odd.Handoff.RootFlatSchedule m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.returnsSingleCycle
```

The corresponding Hamilton target is:

```lean
def D7Odd.Handoff.HamiltonDecompositionD7
    (m : Nat) [NeZero m] : Prop :=
  Nonempty (D7Odd.Handoff.RootFlatCertificate m)
```

Thus the finite base cases used by the dispatcher are not raw external
assertions.  They are Lean terms of this certificate type:

```lean
def D7Odd.Handoff.smallRootFlatCertificate3 :
    D7Odd.Handoff.RootFlatCertificate 3

def D7Odd.Handoff.smallRootFlatCertificate5 :
    D7Odd.Handoff.RootFlatCertificate 5
```

and their endpoint theorem statements are:

```lean
theorem D7Odd.Handoff.smallHamilton3 :
    D7Odd.Handoff.HamiltonDecompositionD7 3

theorem D7Odd.Handoff.smallHamilton5 :
    D7Odd.Handoff.HamiltonDecompositionD7 5
```

The small cases are packaged for the odd `D_7` dispatcher by:

```lean
structure D7Odd.Handoff.SmallBranchResults where
  m3 : D7Odd.Handoff.HamiltonDecompositionD7 3
  m5 : D7Odd.Handoff.HamiltonDecompositionD7 5

def D7Odd.Handoff.smallBranchResults :
    D7Odd.Handoff.SmallBranchResults
```

The generic branch is then combined with the finite base cases through:

```lean
theorem D7Odd.Handoff.odd_from_branches
    (small : D7Odd.Handoff.SmallBranchResults)
    (generic : D7Odd.Handoff.GenericOddBranchResult)
    {m : Nat} [NeZero m] (hm3 : 3 <= m) (hodd : Odd m) :
    D7Odd.Handoff.HamiltonDecompositionD7 m
```

At the graph endpoint level, the handoff certificate is transported to the
torus and Cayley statements by:

```lean
theorem D7Odd.D7_odd_torus_unconditional
    {m : Nat} [NeZero m] (hodd : Odd m) (hm3 : 3 <= m) :
    D7Odd.TorusHamiltonDecompositionD7 m

theorem D7Odd.D7_odd_shared_cayley_uniform :
    forall {m : Nat}, 3 <= m -> Odd m ->
      Shared.CayleyHamiltonDecomposition 7 m
```

These theorem statements are the appendix-level citation target for the `D_7`
seed cases in the all-dimensional odd-modulus proof.

## Certificate Content

The small schedules are defined in `D7Odd/Handoff/SmallBranches.lean` from the
finite selector data in `D7Odd/Handoff/SmallCertificates.lean`:

```lean
def D7Odd.Handoff.smallSchedule3 :
    D7Odd.Handoff.RootFlatSchedule 3

def D7Odd.Handoff.smallSchedule5 :
    D7Odd.Handoff.RootFlatSchedule 5
```

For each `m`, the proof obligations match the fields of
`RootFlatCertificate`:

- `rowLatin`: for each layer time and root-flat state, the color-to-direction
  map is bijective;
- `layerBijective`: for each layer time and color, the root-flat layer map is
  bijective;
- `returnsSingleCycle`: for each color, the full root-flat return map is a
  single cycle.

The common finite interface is:

```lean
def D7Odd.Handoff.SmallCertificateTarget3 : Prop :=
  (forall t c, Function.Bijective
      (D7Odd.Handoff.smallLayer3 t c)) /\
  (forall t w, Function.Bijective
      fun c : Fin 7 => D7Odd.Handoff.smallDir3 t w c) /\
  (forall c, IsSingleCycleMap
      (D7Odd.Handoff.smallReturn3 c))

def D7Odd.Handoff.SmallCertificateTarget5 : Prop :=
  (forall t c, Function.Bijective
      (D7Odd.Handoff.smallLayer5 t c)) /\
  (forall t w, Function.Bijective
      fun c : Fin 7 => D7Odd.Handoff.smallDir5 t w c) /\
  (forall c, IsSingleCycleMap
      (D7Odd.Handoff.smallReturn5 c))
```

The closed Lean theorems are:

```lean
theorem D7Odd.Handoff.smallCertificateTarget3 :
    D7Odd.Handoff.SmallCertificateTarget3

theorem D7Odd.Handoff.smallCertificateTarget5 :
    D7Odd.Handoff.SmallCertificateTarget5
```

## Reproducibility Details

For `m = 3`, Lean uses a generated rank function

```lean
def D7Odd.Handoff.smallRank3Z
    (c : Fin 7) (x : Fin 6 -> ZMod 3) : ZMod 729
```

together with the rank-step proof to show that each six-coordinate return map
is one cycle, then transports the result back to the root-flat representation:

```lean
theorem D7Odd.Handoff.smallReturnSix3_single_cycle
    (c : Fin 7) :
    IsSingleCycleMap (D7Odd.Handoff.smallReturnSix3 c)

theorem D7Odd.Handoff.smallReturn3_single_cycle
    (c : Fin 7) :
    IsSingleCycleMap (D7Odd.Handoff.smallReturn3 c)
```

For `m = 5`, the return-map cycle proof is supplied by per-color array
certificates:

```lean
structure D7Odd.Handoff.SmallRank5Cert (c : Fin 7) where
  cert : RankArrayCert 15625
  ok : cert.ok = true
  comm : forall i : Fin 15625,
    D7Odd.Handoff.indexToSix5 (cert.nextFunOfOk ok i) =
      D7Odd.Handoff.smallReturnSix5 c
        (D7Odd.Handoff.indexToSix5 i)

def D7Odd.Handoff.SmallRank5CertificateTarget : Prop :=
  forall c : Fin 7, Nonempty (D7Odd.Handoff.SmallRank5Cert c)
```

The rank-array certificates are instantiated in
`D7Odd/Handoff/SmallRank5Data0.lean` through
`D7Odd/Handoff/SmallRank5Data6.lean` and assembled as:

```lean
theorem D7Odd.Handoff.smallRank5CertificateTarget :
    D7Odd.Handoff.SmallRank5CertificateTarget

theorem D7Odd.Handoff.smallReturn5CycleTarget :
    D7Odd.Handoff.SmallReturn5CycleTarget
```

The selector-layer bijectivity checks for `m = 5` are not performed by an
expensive direct enumeration inside the final theorem.  They are factored
through finite inverse-map certificates in
`D7Odd/Handoff/SmallLayer5SelectorData0.lean` through
`D7Odd/Handoff/SmallLayer5SelectorData6.lean`, then used in
`smallCertificateTarget5`.

## Verification Command

The appendix claim is reproduced by building the small branch and endpoint
modules:

```bash
lake build D7Odd.Handoff.SmallBranches D7Odd.Torus D7Odd.Cayley
```

For the release-level check, the stronger command remains:

```bash
lake build RoundComposite
```
