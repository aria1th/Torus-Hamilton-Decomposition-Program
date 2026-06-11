#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$ROOT/verification"
cd "$ROOT"
{
  echo "== D9 reinforced verification run =="
  date -u '+UTC %Y-%m-%d %H:%M:%S'
  echo
  echo "[1/8] active graph/coforest anchor"
  python3 scripts/verify_d9_active_anchor_candidate.py certificates/d9_active_anchor_candidate_v1.json
  echo
  echo "[2/8] symbolic affine splice placement"
  python3 scripts/verify_d9_affine_splice_placement.py
  echo
  echo "[3/8] terminal/reserve frame separation"
  python3 scripts/verify_d9_terminal_reserve_frame.py
  echo
  echo "[4/8] low-modulus finite placement"
  python3 scripts/verify_d9_lowmod_finite_placement.py
  echo
  echo "[5/8] low-modulus formal finite semantics"
  python3 scripts/verify_d9_lowmod_formal_semantics.py
  echo
  echo "[6/8] terminal A2 semantics"
  python3 scripts/verify_d9_terminal_a2_block.py
  echo
  echo "[7/8] marked comparison / endpoint reserve semantics"
  python3 scripts/verify_d9_marked_reserve_semantics.py
  echo
  echo "[8/8] D9 -> D11 chain fields"
  python3 scripts/verify_d9_chain_fields.py
  echo
  echo "ALL D9 REINFORCED CERTIFICATES VERIFIED"
} | tee verification/run_all_reinforced_verifications_output.txt
