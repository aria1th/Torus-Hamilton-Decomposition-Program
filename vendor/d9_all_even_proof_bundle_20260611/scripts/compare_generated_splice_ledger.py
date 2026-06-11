#!/usr/bin/env python3
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
cert=json.loads((ROOT/'certificates'/'d9_affine_splice_placement_ledger.json').read_text())
gen=json.loads((ROOT/'verification'/'generated_d9_affine_splice_placement_ledger.json').read_text())
# The generated ledger has a different source string/path in some environments; compare mathematical stages.
assert cert['D']==gen['D']==9
assert cert['stages']==gen['stages']
print('OK: generated splice ledger matches certificate stages')
