#!/usr/bin/env bash
#
# EvenV11 progress gate (replaces the retired closure-first gate).
#
# Philosophy: conventional Lean formalization. The main theorem is stated
# UNCONDITIONALLY and open obligations are honest `sorry`s exposed as `sorryAx`
# in `#print axioms`. This gate verifies the skeleton compiles, forbids `axiom`
# and `admit`, allows `native_decide` only in inventoried finite witnesses, and
# REPORTS the remaining hole count as the live progress metric. Open holes do
# NOT fail the gate — `sorry` is the legitimate in-progress marker; the build
# staying green is what matters.
#
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

fail() { echo "progress gate failed: $*" >&2; exit 1; }

# 1) The whole EvenV11 library + the unconditional main theorem must compile.
echo "== building EvenV11 (umbrella imports EvenV11.Main) =="
lake build EvenV11

# 2) The low-base holes H2/H3/H4 are intentionally closed by inventoried finite
#    existence witnesses.  Keep the inventory explicit so new generated blobs do
#    not silently become part of the proof spine.
echo "== checking inventoried finite witnesses =="
for witness in LowD5M4Finite LowD7M4Finite LowD7M6Finite; do
  [[ -f "EvenV11/${witness}.lean" ]] ||
    fail "inventoried finite witness missing: EvenV11/${witness}.lean"
done
[[ -f "EvenV11/V28Hard/D3M4DirectRootFlat.lean" ]] ||
  fail "inventoried finite witness missing: EvenV11/V28Hard/D3M4DirectRootFlat.lean"
# G3 HED base witnesses: native_decide audits over the inventoried
# LowD7M4Finite/LowD7M6Finite dir blobs (selector closure + reserve clauses).
[[ -f "EvenV11/V28Hard/HEDBaseWitnesses.lean" ]] ||
  fail "inventoried finite witness missing: EvenV11/V28Hard/HEDBaseWitnesses.lean"
unexpected_finite_imports="$(
  grep -rnE '^import[[:space:]]+EvenV11\.Low.*Finite([[:space:]]|$)' \
    EvenV11.lean EvenV11/ \
    | grep -vE 'EvenV11\.LowD(5M4|7M4|7M6)Finite([[:space:]]|$)' \
    || true
)"
if [[ -n "$unexpected_finite_imports" ]]; then
  echo "$unexpected_finite_imports"
  fail "unexpected generated finite witness imported into EvenV11"
fi

# 3) Forbid the real cheats. `sorry` is allowed (honest, warns + shows as
#    sorryAx); `axiom`/`admit` are never allowed. `native_decide` is rejected in
#    structural modules but allowed in the explicitly inventoried finite/archive
#    witnesses.
echo "== scanning for forbidden tokens (axiom / admit) =="
if grep -rnE '^[[:space:]]*axiom[[:space:]]' EvenV11/ ; then
  fail "axiom declaration found in EvenV11 — use a \`sorry\`-backed theorem instead"
fi
if grep -rnE '\badmit\b' EvenV11/ ; then
  fail "\`admit\` found in EvenV11 — use \`sorry\` so it is reported as sorryAx"
fi

native_excludes=(
  --exclude='D3EvenM4.lean'
  --exclude='D3EvenM4RootFlat.lean'
  --exclude='D3M4DirectRootFlat.lean'
  --exclude='LowD5M4Finite.lean'
  --exclude='LowD7M4Finite.lean'
  --exclude='LowD7M6Finite.lean'
  --exclude='HEDBaseWitnesses.lean'
)

echo "== scanning structural modules for native_decide =="
if grep -rnE "${native_excludes[@]}" \
    '(^[[:space:]]*native_decide\b|[[:space:]]by[[:space:]]+native_decide\b)' \
    EvenV11/ ; then
  fail "\`native_decide\` found outside the inventoried finite/archive witnesses"
fi

# 4) The main theorem must stay UNCONDITIONAL (the Goal predicate, no extra
#    hypothesis bundle). Guards against regressing to a checklist-conditional form.
grep -qE '^def EvenModulusToriAllDimensionsGoal : Prop :=' EvenV11/Main.lean \
  || fail "EvenV11/Main.lean must define EvenModulusToriAllDimensionsGoal"
grep -qE \
  '2 ≤ d → Even m → 4 ≤ m → Shared\.CayleyHamiltonDecomposition d m' \
  EvenV11/Main.lean \
  || fail "EvenModulusToriAllDimensionsGoal must be the unconditional even-range target"
grep -qE \
  '^theorem evenModulusToriAllDimensions : EvenModulusToriAllDimensionsGoal' \
  EvenV11/Main.lean \
  || fail "EvenV11/Main.lean must prove the unconditional main theorem"

# 5) Progress metric: open obligations are the `assume_*` theorems still proved
#    by `sorry` in Main.lean. Also surface any stray sorry elsewhere.
holes="$(python3 - <<'PY'
from pathlib import Path
import re

count = 0
in_assume = False
for line in Path("EvenV11/Main.lean").read_text().splitlines():
    if re.match(r"^theorem assume_[A-Za-z0-9_]+", line):
        in_assume = True
    elif in_assume and re.match(r"^(theorem|def|abbrev|structure|end|namespace)\b", line):
        in_assume = False

    if in_assume and re.search(r"\bsorry\b", line):
        count += 1
        in_assume = False

print(count)
PY
)"
stray="$(grep -rlnE ':= sorry|by sorry' EvenV11/ | grep -v 'EvenV11/Main.lean' || true)"

echo "=================================================="
echo "  EvenV11 OPEN HOLES (assume_* := sorry): ${holes}"
if [[ -n "$stray" ]]; then
  echo "  note: sorry found outside Main.lean (expected only during active proofs):"
  echo "$stray" | sed 's/^/    - /'
fi
if [[ "$holes" -eq 0 ]]; then
  echo "  ALL HOLES CLOSED — verify with: #print axioms evenModulusToriAllDimensions"
  echo "  (expect no sorryAx)"
fi
echo "=================================================="
echo "progress gate passed (build green, no axiom/admit, no structural native_decide)"
