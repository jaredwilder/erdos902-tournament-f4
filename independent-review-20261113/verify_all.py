#!/usr/bin/env python3
"""Independent exhaustive f(4)>=49 certificate check (C++17, Python stdlib).
No model, Lean or network. Published 37-class classification remains an external theorem.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import tempfile

HOME=Path(__file__).resolve().parent
DATA=HOME/'drtourn23.txt'
EXPECTED_SHA='20dbad06e128f968e87ce5bec9ca3128b8d2e9a9f25152b29d82c48c967b45d0'
assert hashlib.sha256(DATA.read_bytes()).hexdigest()==EXPECTED_SHA, 'Catalogue bytes mismatch'
report={'schema':'ERDOS902_F4_GE49_INDEPENDENT_REVIEW_20261113',
        'data_sha256':EXPECTED_SHA,'source':'37 candidate DRT23 representatives (classified source)',
        'classification_input':'Published enumeration exactly 37 nonisomorphic DRT(23,11,5); external named theorem',
        'structural_bridge':'F4Struct.lean: no_S4_of_card_le_48 conditional on finite hExt; independent paper proof included',
        'checks':{}}
with tempfile.TemporaryDirectory(prefix='erdos902-court-') as td:
    binpath=Path(td)
    for name in ('independent_f4','classify_signature','compare8'):
        source=HOME/(name+'.cpp')
        binary=binpath/name
        subprocess.run(['g++','-std=c++17','-O3',str(source),'-o',str(binary)],check=True)
        p=subprocess.run([str(binary),str(DATA)],check=True,capture_output=True,text=True)
        print(f'== {name} ==\n{p.stdout}{p.stderr}')
        report['checks'][name]={'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
    paley=subprocess.run(['python',str(HOME/'verify_paley67.py')],check=True,capture_output=True,text=True)
    print('== independent Paley67 control ==\n'+paley.stdout)
    report['checks']['paley67']={'exit_code':0,'stdout':paley.stdout}
    altered=DATA.read_text().splitlines()
    altered[0]=('0' if altered[0][0]=='1' else '1')+altered[0][1:]
    bad=binpath/'mutated.txt';bad.write_text('\n'.join(altered)+'\n')
    proc=subprocess.run([str(binpath/'independent_f4'),str(bad)],capture_output=True,text=True)
    assert proc.returncode!=0, 'Mutated tournament was incorrectly admitted'
    report['checks']['negative_control']={'caught':True,'return_code':proc.returncode,
                                         'stderr':proc.stderr.strip()}
    print('== negative control ==\ncorrupted catalogue rejected')
    report['verdict']='FINITE_AND_DISTINCTNESS_AUDITS_PASS'
    report['limit']='Mathematical theorem uses a published 37-class classification; external specialist review needed.'
(HOME/'independent_audit_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print('COURT: PASS')
