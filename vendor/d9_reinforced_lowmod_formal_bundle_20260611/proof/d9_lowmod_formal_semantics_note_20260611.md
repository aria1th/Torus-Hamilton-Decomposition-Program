# D9 low-modulus formal finite semantics verification (2026-06-11)

This note records the strengthened finite verification for the residual low
moduli `m = 4, 6, 8`.

The previous low-modulus verifier checked that the finite affine placement
ledger had disjoint splice supports, a separated terminal carrier, and a
separated endpoint reserve.  The new verifier

```text
scripts/verify_d9_lowmod_formal_semantics.py
```

is designed to be closer to what a Lean/finite-set formalization needs.  It does
not expand the full root-flat return permutations, but it verifies every local
finite fact used by the signed D9 anchor-realization theorem as an equality or
cardinality statement in the finite group

```text
K_{9,m} = { x in (Z/mZ)^9 : sum_i x_i = 0 }.
```

## Verified finite facts

For each `m in {4,6,8}` the verifier checks the following.

1. The 28 splice supports are explicit affine cosets in `K_{9,m}` with the
   expected sizes: pair supports have size `m`, and non-terminal triple supports
   have size `m^2`.

2. Each support is closed under every listed active direction.  This is the
   finite support-closure fact needed by the local layer-switch lemma.

3. For every affected color, the previous color forest is recomputed, contracted,
   and the printed support is verified to be a rooted coforest in the contracted
   component graph.

4. The entire finite support set is projected to the contracted quotient.  The
   active quotient-coordinate image has full cardinality `m` or `m^2`, while all
   inactive support coordinates and the omitted-component coordinate are
   singleton-valued.  This is the finite old-head transversality statement.

5. Pair rows have raw active increment exactly `+1` or `-1`.  Non-terminal triple
   rows have active vectors whose pairwise determinants are exactly `+1` or
   `-1`.

6. Supports whose heights fold to the same residue modulo `m` are pairwise
   disjoint.  The verifier also checks the finite union size at every folded
   height.

7. The terminal carrier and reserve plane are explicit rank-two affine planes of
   sizes `m^2`; both avoid all splice supports and avoid each other.

8. The standard terminal `A2` word is recomputed at `m=4,6,8`, and the three
   terminal local returns are verified to be `m^2`-cycles on the terminal plane.
   The marked comparison cycle embeds injectively in the terminal carrier.

9. The ordered endpoint reserve family

   ```text
   U0, U1, U2, U1_c, ..., U8_c, U_star
   ```

   consists of 12 distinct root-flat points in the reserve plane.  Each site has
   the recorded semantic role and lies outside the protected terminal carrier
   and every splice support.

The generated finite fact file is

```text
verification/d9_lowmod_formal_facts.json
```

and is intended as a compact formalization index: it records support sizes,
folded-height union sizes, and per-color active increments for all local pieces.

## Verification transcript

The current run reports:

```text
OK: D9 low-modulus formal finite semantics verified
m=4: formal finite semantics OK; supports=28, terminal=16, reserve=16, reserve_sites=12, folded_heights=[0, 1, 2, 3]
m=6: formal finite semantics OK; supports=28, terminal=36, reserve=36, reserve_sites=12, folded_heights=[0, 1, 2, 4, 5]
m=8: formal finite semantics OK; supports=28, terminal=64, reserve=64, reserve_sites=12, folded_heights=[0, 1, 2, 4, 5, 7]
```

## Scope

This verifier closes the low-modulus placement and local-splice hypotheses of
the signed D9 anchor-realization theorem by finite enumeration.  It is still not
a brute-force root-flat return verifier: it does not construct the full layer
permutations on all `m^8` root-flat points and compute their cycle types.  That
brute-force verifier would be a further hardening step, not a replacement for the
formal local-realization theorem.
