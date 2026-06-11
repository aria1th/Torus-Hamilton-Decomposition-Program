# D9 all-even proof bundle (2026-06-11)

This bundle packages the replacement D9 route for the even-modulus proof program.
It proves

\[
  \mathrm{HED}(9,m)\quad\text{for every even }m\ge4.
\]

The high-even part covers \(m>9\).  The finite low-modulus certificate covers
\(m=4,6,8\).  Combined with the corrected midpoint-collision paired growth, this
closes the odd branch \(d\ge9\) without the old chained \(7\to9\) step.

## Reproduce

From the bundle root, run:

```bash
bash scripts/run_all_verifications.sh
```

Expected final line:

```text
ALL D9 ALL-EVEN CERTIFICATES VERIFIED
```

## Important scope note

This bundle proves the D9 anchor theorem and the D9 input needed for the paired
growth route.  It does not use the failed pointwise-preserving chained
\(7\to9\) construction.
