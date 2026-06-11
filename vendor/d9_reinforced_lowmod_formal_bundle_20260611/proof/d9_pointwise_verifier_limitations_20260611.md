# Pointwise verifier limitation note

The reinforced bundle does not contain a full pointwise root-flat layer-map
verifier for `D9(4)`, `D9(6)`, or `D9(8)`.  The reason is structural: the D9
certificates in this bundle are realization certificates.  They list the active
anchor, quotient/coforest supports, affine support cosets, terminal carrier, and
endpoint reserve, but they do not list a complete overridden layer table on all
`m^8` root-flat points.

The low-modulus verifier therefore checks the hypotheses of the signed
anchor-realization theorem inside the finite groups `K_{9,m}` rather than
constructing the final nine return permutations explicitly.  A future independent
pointwise verifier would need an additional expansion layer that materializes all
localized row overrides from the realization theorem and then checks:

```text
RF1, RF2, RF3;
cycle type [m^8] for each of the nine returns;
marked comparison cycle and endpoint reserve semantics.
```

The present proof is unconditional in the theorem-proving sense once the signed
anchor-realization theorem is admitted as a proved lemma.  It is not yet an
independent brute-force permutation certificate in the style of the older
`D7(4)` and `D7(6)` pointwise certificates.
