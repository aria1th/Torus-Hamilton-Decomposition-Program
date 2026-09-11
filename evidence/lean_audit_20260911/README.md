# Lean audit artifacts for the even-modulus formalization (2026-09-11)

Per-stage `#print axioms` audits produced during the E4/E5 formalization, copied from the
execution node's working directories. Each stage lists the commit on branch `even-modulus`
whose sources were built and audited. Included per stage: the audit source (`*Audit.lean`),
its output (`axioms.log`), the isolation-check output, declaration lists/summaries where they
were produced, and `sources-sha256.json` (toolchain versions plus per-file SHA256 of the built
Lean sources, extracted from the execution receipt). Excluded on purpose: full build logs
(mathlib output), git recovery bundles, execution-node receipts and manifests (they carry
host and path information with no mathematical content). The final stage was re-run on the
source checkout; see `final-control-check/`.

| Stage | Commit | Content | Files |
|---|---|---|---|
| `preparation` | `d335aa4` | E0-E3 endpoint re-audit; collar component lemmas (cde2173) | `CollarAudit.lean`, `EndpointAudit.lean`, `axiom-counts.json`, `collar-axioms.log`, `endpoint-audit.log`, `collar-sources-sha256.json` |
| `selector` | `916118d` | E4 pinned coherent selection | `SelectorAudit.lean`, `axioms.log`, `isolation.log`, `sources-sha256.json` |
| `closure` | `dd44c09` | E4 relative collar closure, even degrees | `ClosureAudit.lean`, `axioms.log`, `isolation.log`, `sources-sha256.json` |
| `entry` | `2a9594c` | E5 near core, anchors, entry interfaces | `EntryAudit.lean`, `axioms.log`, `isolation.log`, `sources-sha256.json` |
| `star` | `fb6f5e8` | E5 anchored cyclic star: factorization, return reduction | `StarAudit.lean`, `axioms.log`, `isolation.log`, `sources-sha256.json` |
| `star-return` | `7deb298` | E5 cyclic star, 3 | m | `DivisibleAudit.lean`, `axioms.log`, `isolation.log`, `sources-sha256.json` |
| `star-nondiv` | `6f16b8d` | E5 cyclic star, 3 does not divide m (uniform theorem) | `NondivAudit.lean`, `audit-declarations.json`, `audit-validation.json`, `axioms.log`, `isolation.log`, `sources-sha256.json` |
| `shell` | `72adf0d` | E5 auxiliary shell and seed assembly | `ShellAudit.lean`, `audit-declarations.json`, `axioms.log`, `isolation.log`, `sources-sha256.json` |
| `incidence` | `e8a269c` | E5 seed incidence parity | `IncidenceAudit.lean`, `audit-declarations.json`, `axioms.log`, `isolation.log`, `small-certificate-generation.txt`, `sources-sha256.json` |
| `matched` | `5e63262` | E5 matched selection | `MatchedAudit.lean`, `axioms.log`, `isolation.log`, `new-declarations.txt`, `sources-sha256.json` |
| `residual` | `7e9fbd5` | E5 residual parity, entry, final assembly | `FinalAudit.lean`, `axiom-summary.json`, `axioms.log`, `isolation.log`, `new-declarations.txt`, `sources-sha256.json` |
