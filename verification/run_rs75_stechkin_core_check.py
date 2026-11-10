"""Compile and audit the selective unchanged-body Stechkin analytic APIs."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / 'verification'
files = ['RSBounds/RS75StechkinCore.lean',
         'verification/rs75-stechkin-core-port.json',
         '.lake/packages/TernaryGoldbach/TernaryGoldbach/Explicit/ZeroFreeRegion.lean',
         'verification/RS75StechkinCoreAudit.lean',
         'verification/run_rs75_stechkin_core_check.py']
data = {
    'kind': 'fresh-local-compilation-and-transitive-axiom-audit',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'source_sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest()
                      for f in files},
    'runs': [],
}
receipt = OUT / 'rs75-stechkin-core-run.json'

def save():
    receipt.write_text(json.dumps(data, indent=2) + '\n')

save()
jobs = [
    (['lake', 'env', 'lean', '-j1', '-Dprofiler=true', '-o',
      '.lake/build/lib/lean/RSBounds/RS75StechkinCore.olean', 'RSBounds/RS75StechkinCore.lean'],
     'rs75-stechkin-core-build.log'),
    (['lake', 'env', 'lean', '-j1', 'verification/RS75StechkinCoreAudit.lean'],
     'rs75-stechkin-core-axioms.log'),
]
for command, logname in jobs:
    print('Checking ' + command[-1], flush=True)
    started = time.monotonic()
    with (OUT / logname).open('wb') as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    data['runs'].append({'command': command, 'log': logname,
                         'exit_code': result.returncode,
                         'seconds': time.monotonic() - started})
    save()
    if result.returncode:
        data.update(exit_code=result.returncode,
                    finished_utc=datetime.now(timezone.utc).isoformat())
        save()
        print((OUT / logname).read_text(), flush=True)
        raise SystemExit(result.returncode)
groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]',
                    (OUT / 'rs75-stechkin-core-axioms.log').read_text(), re.S)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert len(groups) == 4 and all(
    {x.strip() for x in g.split(',') if x.strip()} <= allowed for g in groups)
data['axiom_audit'] = {'declarations': len(groups), 'only_standard_axioms': True}
data.update(exit_code=0, finished_utc=datetime.now(timezone.utc).isoformat())
save()
print(json.dumps(data, indent=2), flush=True)
