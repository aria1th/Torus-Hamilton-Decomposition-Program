# D5 odd paper/Lean audit, 2026-04-24

Source paper draft:

```text
/data/angel/repos/etc/d5_odd_paper_readerfriendly_pass39_stylepatch_with_tikz.tex
```

Checked Lean target:

```lean
theorem D5_odd_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    HamiltonDecompositionD5 m
```

Latest verification:

```bash
lake build D5Odd
python3 /data/angel/repos/etc/d5_odd_paper_verify.py 3 5 7 9
```

Both passed.  The verifier printed:

```text
m=3: matching=81, G-cycle=81
m=5: matching=625, G-cycle=625
m=7: matching=2401, G-cycle=2401
m=9: matching=6561, G-cycle=6561
```

## High-level conclusion

The Lean development proves the paper's root-flat/layer-return Hamiltonian decomposition statement for
odd `m >= 3`.  The main mathematical ingredients of the paper are present:

* the root-flat model and `q_i` steps;
* the cyclic zero-set table `Lambda1`;
* the `m >= 5` and `m = 3` schedules;
* exact-cover/Latin conditions for the schedules;
* the normalized color-zero return `G`;
* the `p = 2` Sigma section;
* the first-return endpoints and no-earlier-return strengthening;
* the induced Sigma cycle and total excursion length `m^4`;
* transfer from normalized color zero to all color returns.

The original scope caveat was that `HamiltonDecompositionD5` is the internal
root-flat/layer-schedule model.  The outer layer-lift argument has now been formalized in
`D5Odd/Torus.lean`: vertices of the full torus are identified with `(layer, root-flat point)`, one
torus color step is conjugate to the layer/root step, `m` layer/root steps return by `colorReturn`,
and the paper's return-cover criterion transfers the root-flat Hamiltonian condition to one cycle on
the full torus for each color.

There is also a paper-title wrapper in `D5Odd/Cayley.lean`: it introduces explicit Cayley edges
`x -> x + e_i`, proves the schedule colors partition the outgoing Cayley directions at every vertex,
and transfers the color-step Hamilton cycles to a `CayleyHamiltonDecompositionD5` statement.  The only
optional remaining presentation layer would be integration with an external graph-library digraph
type, if desired.

## Paper-to-Lean map

| Paper item | Lean artifact | Status |
| --- | --- | --- |
| Main theorem: odd `m >= 3` D5 Hamilton decomposition | `D5_odd_unconditional` in `D5Odd/Main.lean` | Closed in the root-flat model |
| Root flat `A_m`, steps `q_i=e_i-e_4`, root predicate | `Vec5`, `q5`, `Root5`, `ARoot5` in `D5Odd/Basic.lean` | Matches |
| Layer maps and color return | `layerMap`, `colorReturn` in `D5Odd/Schedule.lean` | Matches paper's return-map model |
| `Lambda1` cyclic zero-set table | `Lambda1`, `Lambda1_latin` in `D5Odd/ZeroSetTable.lean` | Matches expanded table |
| `Sch_{>=5}` | `ge5Dir`, `ge5Schedule` in `D5Odd/Schedule.lean` | Matches |
| `Sch_3` | `m3Dir`, `m3Schedule` in `D5Odd/Schedule.lean` | Matches |
| Latin outgoing condition | `ge5Schedule_latin`, `m3Schedule_latin` | Closed |
| Matching/exact-cover condition | `ge5Schedule_exact`, `m3Schedule_exact` | Closed; Lean splits `m>=5` and `m=3` |
| `p=2` section `Sigma={(0,a,b,0,-a-b):a+b != 0}` | `p5_eq_two_iff_root`, `sigmaVec`, `SigmaParam`, `sigmaPoint_bijective` | Closed |
| First-return table | `normalizedG0_first_return_sigma` plus branch lemmas | Closed for `m>=5` |
| No earlier Sigma return | `normalizedG0_p5_no_earlier_sigma` | Closed for `m>=5` |
| Induced Sigma cycle | `nextSigma_single_cycle` | Closed; uses `psiNZ`/`orbitSigma` rank parametrization |
| Total excursion sum `m^4` | `returnTimeSigma_sum_m4` | Closed |
| Splice lemma from first returns to one cycle | `single_cycle_of_first_return_sum` and `normalizedG0_single_cycle` | Closed for `m>=5` |
| Color-zero/all-color transfer | `colorReturn_ge5_semiconj_add5`, `colorReturn_ge5_single_cycle`, `ge5Schedule_allColorHamiltonian` | Closed |
| `m=3` Hamiltonian condition | `m3Rank_step`, `m3Rank_bijective`, `m3Schedule_allColorHamiltonian` | Closed by finite 5-color rank certificate |
| Full torus layer-lift | `layerRootEquiv`, `torusColorStep_layerRootEquiv`, `layerRootStep_m_return`, `torusHamiltonDecomposition_of_model`, `D5_odd_torus_unconditional` in `D5Odd/Torus.lean` | Closed as color-step Hamilton cycles on `(ZMod m)^5` |
| Cayley edge wrapper | `CayleyEdge5`, `IsCayleyEdgePartition`, `CayleyHamiltonDecompositionD5`, `D5_odd_cayley_unconditional` in `D5Odd/Cayley.lean` | Closed as explicit `x -> x + e_i` edge partition plus color Hamilton cycles |

## Differences from the paper proof

1. The paper states the matching lemma uniformly for every odd `m >= 3`.  Lean proves the needed
   instances in two pieces: `ge5Schedule_exact` for `m >= 5`, and `m3Schedule_exact` by finite
   decision for `m = 3`.

2. The paper presents the normalized return `G` cycle lemma for every odd `m >= 3`.  Lean proves the
   conceptual first-return proof for `m >= 5` (`h >= 2`) and closes `m = 3` separately by a generated
   rank certificate over the 81 quad states for each color.  This proves the same final schedule-level
   conclusion but is not the same proof route as the draft's unified `G` argument.

3. The paper explains color symmetry as `G_c rho_c = rho_c G_0`.  Lean proves the equivalent
   schedule-level affine semiconjugacy directly:

   ```lean
   colorReturn_ge5_semiconj_add5
   ```

   This is actually a safer formal route because root-flat coordinates use coordinate `4` as the
   basepoint, so coordinate rotation carries the correction term explicitly.

4. The paper's final theorem is graph-level.  Lean now has three final levels.  The reduced
   root-flat/layer theorem is:

   ```lean
   exists F : LayerSchedule m,
     IsLayerExactCover F /\ IsScheduleLatin F /\ AllColorHamiltonian F
   ```

   The full torus/layer-lift theorem is:

   ```lean
   theorem D5_odd_torus_unconditional {m : Nat} [NeZero m]
       (hodd : Odd m) (hm3 : 3 <= m) :
       TorusHamiltonDecompositionD5 m
   ```

   This proves the actual Hamilton cycles on `Vec5 m = (ZMod m)^5` via the schedule's color step
   maps.  What is still not introduced is a separate graph-library Cayley digraph type; the theorem is
   stated directly in terms of the color step maps.

   The explicit Cayley-edge wrapper is:

   ```lean
   theorem D5_odd_cayley_unconditional {m : Nat} [NeZero m]
       (hodd : Odd m) (hm3 : 3 <= m) :
       CayleyHamiltonDecompositionD5 m
   ```

   This states the edge partition directly using edges of the form `x -> x + e_i`.

## Risk assessment

No mismatch was found in the core construction.  The reduced return-map theorem, the standard
layer-lift bridge, and the explicit Cayley-edge wrapper are all formalized.

The only remaining optional formalization layer is integration with a separate graph-library digraph
API.  The current Lean statement already uses explicit Cayley edges `x -> x + e_i`.
