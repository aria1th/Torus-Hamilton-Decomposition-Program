# Torus Hamilton Decomposition Program

Lean 4 formalization workspace for Hamilton decompositions of directed
odd-modulus torus Cayley digraphs.

The main target is the directed basis Cayley digraph

```text
Cay((ZMod m)^d, {e_0, ..., e_{d-1}})
```

and the goal is to prove that, for every `d >= 2` and every odd `m >= 3`,
its arcs decompose into `d` directed Hamilton cycles.

This repository is also a proof-audit workspace.  Some modules are finished
theorem libraries, while the newest `RoundComposite` files expose the current
paper-facing endpoint cuts for the all-dimensional theorem.

## Current Status

Snapshot: 2026-05-05.

Latest stable release:
[`0.0.2-d7`](https://github.com/aria1th/Torus-Hamilton-Decomposition-Program/releases/tag/0.0.2-d7).

```text
All odd m, all d >= 2
│
├─ finite seeds
│  ├─ d = 2                               [done]
│  ├─ d = 3                               [done]
│  ├─ d = 5                               [done]
│  └─ d = 7                               [done]
│
├─ high-modulus branch, m >= d
│  ├─ prefix-count/root-flat machinery     [done]
│  ├─ q >= 2 signed binary trellis core    [done]
│  ├─ half-slack/support bridge            [done]
│  └─ high-modulus endpoint adapters       [done]
│
├─ closure/dispatcher layer
│  ├─ product/composite closure            [done]
│  ├─ seed-semigroup arithmetic            [done]
│  └─ all-dimension wrappers               [done]
│
└─ small-modulus successor branch, m < d
   ├─ active-block cylinder construction   [done]
   ├─ primitive active-prefix lift          [done]
   ├─ local swap/residue algebra            [done]
   ├─ reservoir quota matching              [done]
   └─ canonical reservoir construction      [active target]
```

The current sharp remaining Lean cut is:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalNonzeroZeroReservoirArithmeticGoal
```

Once that construction is supplied, the existing V75 endpoint wrappers route it
to the full all-dimensional theorem.

## Proof Map

The repository currently organizes the proof into two large branches.

```mermaid
flowchart TD
    Seeds[D2, D3, D5, D7 seeds]
    High[High-modulus prefix-count branch]
    Successor[Small-modulus successor branch]
    Dispatch[Product and seed-semigroup dispatcher]
    Final[All d >= 2, odd m >= 3]

    Seeds --> Dispatch
    High --> Dispatch
    Successor --> Dispatch
    Dispatch --> Final
```

The current V75 small-modulus route is more explicit than the older abstract
finite-Hall route:

```mermaid
flowchart TD
    Cyl[active-block cylinder]
    Lift[primitive lower-triangular active lift]
    Res[compatible residue scheduling]
    Swap[zero/nonzero local swaps]
    Arith[three-buffer reservoir arithmetic]
    Goal[V75 direct modular-trade blocks]

    Cyl --> Lift
    Res --> Swap
    Swap --> Arith
    Lift --> Goal
    Arith --> Goal
```

## Main Lean Endpoints

Seed endpoints:

```lean
Shared.D2.shared_cayley_uniform
Shared.D3.shared_cayley_uniform
D5Odd.D5_odd_cayley_unconditional
D7Odd.D7_odd_cayley_unconditional
```

All-dimensional endpoint shape:

```lean
RoundComposite.Concrete.OddModulusToriAllDimensionsGoal
```

Current paper-facing V75 adapters:

```lean
RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_v75_directModularTrade_blocks
RoundComposite.Concrete.oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_blocks
RoundComposite.Concrete.oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
```

Current preferred open construction interface:

```lean
RoundComposite.BaseTail.Trades.SuccessorActiveBlockCanonicalNonzeroZeroReservoirArithmeticGoal
```

## Repository Layout

```text
Shared/
  Common Cayley decomposition interfaces, root-flat lifts, rank-cycle tools,
  and the D2/D3 shared seed adapters.

TorusD3Odd/
  Direct D3 odd formalization used by Shared/D3Seed.lean.

D5Odd/
  Odd D5 construction and Cayley wrapper.  Some even-modulus/Route-E files are
  retained as related work but are not the current all-odd main path.

D7Odd/
  Odd D7 construction, including handoff and bridge modules.

RoundComposite/
  All-dimensional proof architecture:
  prefix-count branch, seed semigroup, small-modulus successor branch,
  base-tail geometry, modular trades, and final concrete endpoints.

docs/
  Current research notes and paper/Lean synchronization documents.

scripts/
  Verification and audit scripts used during development.

certs/
  Finite certificates and related data.
```

The most useful files for orienting the current all-odd proof are:

```text
RoundComposite/ConcreteEndpoints.lean
RoundComposite/V75Endpoints.lean
RoundComposite/BaseTailTrades.lean
RoundComposite/BaseTailGeometry.lean
RoundComposite/PrefixCountHalfSlack.lean
RoundComposite/FiniteHoffman/SignedTrellis.lean
docs/ODD_TORI_V75_DIRECT_MODULAR_TRADE_GOAL_20260505.md
```

## Build

This project uses Lean 4 with mathlib through Lake.

```bash
lake build RoundComposite.V75Endpoints
```

Useful focused checks:

```bash
lake env lean Shared/D3Seed.lean
lake env lean RoundComposite/BaseTailTrades.lean
lake env lean RoundComposite/V75Endpoints.lean
lake build RoundComposite.BaseTailTrades
lake build RoundComposite.V75Endpoints
```

The `lakefile.toml` currently pins mathlib at:

```text
leanprover-community/mathlib v4.30.0-rc2
```

## Reading Guide

For the mathematical story, start with the latest manuscript bundle and the V75
goal note in `docs/`.  For Lean work, start from
`RoundComposite/V75Endpoints.lean` and follow the hypotheses downward.

Recommended order:

```text
1. RoundComposite/ConcreteEndpoints.lean
2. RoundComposite/V75Endpoints.lean
3. RoundComposite/BaseTailTrades.lean
4. RoundComposite/BaseTailGeometry.lean
5. RoundComposite/PrefixCountHalfSlack.lean
6. RoundComposite/FiniteHoffman/SignedTrellis.lean
```

## Development Notes

- The root README is intentionally short.  Historical handoff details live in
  `docs/` or in module comments.
- The current main route is the V75 direct modular-trade route, not the older
  abstract de Werra/Hall endpoint.
- Avoid treating every `*Goal : Prop` as an unfinished theorem.  Many are
  named interfaces or adapters used to keep the proof graph readable.
- The active mathematical task is the final canonical reservoir construction
  under the already-exposed arithmetic and quota-matching interfaces.

## AI Disclosure

This formalization project used autonomous AI assistance during proof planning,
Lean implementation, code review, documentation, and audit work.  In particular,
OpenAI Codex 5.5 with `xhigh` reasoning and OpenAI GPT-5.5 Pro with `xhigh`
reasoning were used as autonomous formalization assistants.

The mathematical statements, proof strategy, accepted code changes, and final
repository contents remain subject to human review and responsibility.

## Citation

See `CITATION.cff` for citation metadata.  The manuscript and formalization are
still under active development.
