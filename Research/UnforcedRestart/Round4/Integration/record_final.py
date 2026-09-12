#!/usr/bin/env python3
"""Separate opt-in receipt generation; verifier itself never writes."""
import json, tempfile, sys
sys.dont_write_bytecode = True
from pathlib import Path
from verify_final import verify, HERE
result=verify()
out=Path(tempfile.mkdtemp(prefix='final-verification-',dir=HERE))
(out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(out/'receipt.json')
raise SystemExit(0 if result['preservation_status']=='PASS' else 1)
