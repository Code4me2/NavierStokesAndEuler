#!/usr/bin/env python3
"""Strictly rebuild only Round4 sources against the pinned clean historical tree."""
import json, subprocess, sys, tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
out=Path(tempfile.mkdtemp(prefix='chain-',dir=HERE))
receipts=[]
for name in ['PressureIntegral/Main','PressureIntegral/Components','LaplacianIntegral/Main',
             'LaplacianIntegral/Regularity','PeriodizationTransport/Main',
             'PeriodizationTransport/Residual','PeriodizationTransport/Cell','Integration/Main',
             'Integration/Assembly','Integration/Acceptance','Integration/FinalAudit']:
    source='Research/UnforcedRestart/Round4/'+name+'.lean'
    run=subprocess.run([sys.executable,str(HERE/'check.py'),source,*receipts],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/(name.replace('/','-')+'.log')).write_text(run.stdout)
    print(name,run.returncode,flush=True)
    if run.returncode: print(run.stdout);sys.exit(run.returncode)
    receipt=str(Path(run.stdout.splitlines()[0])/'receipt.json')
    receipts.append(receipt)
    (out/'receipt.json').write_text(json.dumps({'status':'BUILDING','receipts':receipts},indent=2)+'\n')
(out/'receipt.json').write_text(json.dumps({'status':'PASS','receipts':receipts},indent=2)+'\n')
print(out/'receipt.json')
