"""Compile and audit the finite weighted rectangle residue identity."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess

project = Path(__file__).resolve().parents[1]
workspace = project.parent
tools_dir = workspace / ".tools"
elan = tools_dir / "elan-home"
env = os.environ.copy()
env.update(ELAN_HOME=str(elan), PATH=str(elan / "bin") + os.pathsep + env["PATH"],
           LEAN_NUM_THREADS="1", TMPDIR=str(tools_dir / "tmp"))
files = ["RSBounds/PolynomialResidue.lean", "verification/PolynomialResidueAudit.lean"]
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_sha256": {f: hashlib.sha256((project / f).read_bytes()).hexdigest() for f in files},
    "runs": [],
}
commands = [
    (["lake", "build", "RSBounds.PolynomialResidue"], "polynomial-residue-build.log"),
    (["lake", "env", "lean", "verification/PolynomialResidueAudit.lean"], "polynomial-residue-axioms.log"),
]
result = 0
for command, filename in commands:
    with (project / "verification" / filename).open("w") as output:
        completed = subprocess.run(command, cwd=project, env=env, stdout=output,
                                   stderr=subprocess.STDOUT, check=False)
    record["runs"].append({"command": command, "log": filename, "exit_code": completed.returncode})
    print(f"{filename}: exit {completed.returncode}", flush=True)
    if completed.returncode:
        result = completed.returncode
        break
record["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record["exit_code"] = result
(project / "verification" / "polynomial-residue-run.json").write_text(json.dumps(record, indent=2) + "\n")
raise SystemExit(result)
