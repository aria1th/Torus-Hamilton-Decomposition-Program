# Reinforced D9 all-even proof summary

This reinforced bundle adds the semantic checks requested after the adversarial
audit of the D9 all-even package.

New checks:

1. `verify_d9_terminal_a2_block.py` checks that the terminal carrier is the
   standard terminal `A2` block transported to `(6,0,1)` and recomputes terminal
   return cycles/interlacing selectors on sample even moduli.
2. `verify_d9_marked_reserve_semantics.py` checks ordered endpoint-reserve roles,
   embeds the marked terminal comparison cycle in the terminal carrier, and
   verifies that reserve sites and splice supports are outside the conservative
   protected neighborhood.
3. `verify_d9_chain_fields.py` checks the D9-to-D11 label chart, terminal-carrier
   disjointness from the ordinary paired growth window, fixed-old reserve
   transport, and midpoint-collision phase avoidance for the two ordinary paired
   rows.

The older checks remain included:

* D9 active graph/coforest anchor;
* symbolic high-even splice placement;
* terminal/reserve frame separation;
* finite low-modulus placement for `m=4,6,8`.

Precise status: the bundle proves `HED(9,m)` for every even `m >= 4` via the
signed D9 anchor-realization theorem and the D9 chain-field assembly lemma.  It
is a theorem/certificate proof, not a brute-force pointwise return-permutation
certificate for low moduli.
