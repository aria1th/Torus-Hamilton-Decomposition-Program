# Route E RoundY Branch Triage

Date: 2026-05-06.

Source notes added under the local reference tree:

- `Torus-Hamilton-Decomposition/RoundY/d5_join_quotient_branch_note_v1.md`
- `Torus-Hamilton-Decomposition/RoundY/d5_fresh_cyclic_branch_note_v1.md`
- `Torus-Hamilton-Decomposition/RoundY/d5_master_field_branch_note_v1.md`

These files are not B20/B16/R14e all-pair closure witnesses.  They define the
next Route-E exploration layer after the current table/certificate branch:
move from representative-color or fixed-quotient searches to a finite
cyclic-equivariant permutation field.

## Branch Split

| Branch note | Lean status | Search status | Interpretation |
| --- | --- | --- | --- |
| joined quotient | no concrete witness; quotient-enlargement target only | open CP-SAT/free-anchor search on `Theta_AB` | fixed Schema A/B anchor freedom is exhausted; enlarge quotient first |
| fresh cyclic | no concrete witness; design constraints only | open fresh family search with clean-frame hard filters | stop repairing G3 color-0 defects after the fact; build clean frames into the family |
| master field | conditional target now exposed in Lean | needs quotient-state solver output | promote to `pi_theta in S_5` with outgoing/incoming Latin and representative triangular data |

The branch notes therefore do not close the existing blocker:

```text
No B20/B16/R14e branch currently instantiates
RouteEAllPairSectionCertificate.
```

They do clarify the next proof interface once a new search supplies a finite
phase quotient and local permutation table.

## Lean Names Added

`D5Odd/EvenRouteE.lean` now contains a master-field quotient interface:

- `RouteEMasterFieldShape`
- `RouteEMasterFieldShape.toSchedule`
- `RouteEMasterFieldShape.PhaseLatin`
- `RouteEMasterFieldShape.IncomingLatin`
- `RouteEMasterFieldShape.toSchedule_latin_of_phase_latin`
- `RouteEMasterFieldShape.toSchedule_exactCover_of_incoming`
- `RouteEMasterFieldShape.CyclicEquivariance`
- `RouteEMasterFieldTarget`
- `RouteEMasterFieldTarget.toHamiltonDecomposition`
- `RouteEMasterFieldTarget.toTorusHamiltonDecomposition`
- `RouteEMasterFieldTarget.toCayleyHamiltonDecomposition`
- `RouteEMasterFieldLocalTarget`
- `RouteEMasterFieldLocalTarget.toMasterFieldTarget`
- `RouteEMasterFieldLocalTarget.toHamiltonDecomposition`
- `RouteEMasterFieldLocalTarget.toTorusHamiltonDecomposition`
- `RouteEMasterFieldLocalTarget.toCayleyHamiltonDecomposition`
- `RouteECyclicMasterFieldLocalTarget`
- `RouteECyclicMasterFieldLocalTarget.toHamiltonDecomposition`
- `RouteECyclicMasterFieldLocalTarget.toTorusHamiltonDecomposition`
- `RouteECyclicMasterFieldLocalTarget.toCayleyHamiltonDecomposition`

This interface keeps the theorem endpoint conservative.  A finite quotient
search must still prove:

1. every phase row is a permutation (`PhaseLatin`);
2. predecessor rows satisfy incoming Latin (`IncomingLatin`);
3. the induced schedule is Hamiltonian for all colors;
4. optionally, cyclic equivariance of the phase quotient and local field.

Once those are supplied, the existing `HamiltonDecompositionD5`,
`TorusHamiltonDecompositionD5`, and `CayleyHamiltonDecompositionD5` endpoints
are immediate.

## Computation Endpoints

The three notes point to solver/search work, not hand Lean arithmetic.

- Joined quotient:
  build `Theta_AB`, enumerate state/orbit counts, run free-anchor Latin search,
  then diagnose clean frame, strict clock, section cycles, monodromy, and full
  color cycle counts.
- Fresh cyclic:
  search orbit-gate families with hard clean-frame filters for every color,
  recording only clean frame, section-return cycle type, and monodromy until a
  candidate survives.
- Master field:
  search directly over finite quotient states with variables
  `Pi_theta : S_5`, outgoing Latin built in, incoming Latin as local
  predecessor constraints, and representative-color triangular data.

The current Python environment does not have `ortools` installed, so the
CP-SAT scripts in the reference tree cannot be run as-is from this checkout
without preparing that dependency.

## Next Lean Slice

There are two independent tracks now:

1. Continue the existing v3.6 closure track by instantiating concrete
   `RouteEAllPairSectionCertificate` targets for B20/B16/R14e.
2. Continue the RoundY branch track by importing or rewriting a minimal
   deterministic solver artifact into a `RouteEMasterFieldLocalTarget` or
   `RouteECyclicMasterFieldLocalTarget` instance.

The second track should not be allowed to blur the first: the master-field
interface is useful only after a quotient search produces an actual phase table
and validations.
