"""Fresh compilation and axiom audit of dilation and left-line kernels."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

project = Path(__file__).resolve().parents[1]
workspace = project.parent
elan = workspace / ".tools" / "elan-home"
env = os.environ.copy()
env.update(ELAN_HOME=str(elan), PATH=str(elan / "bin") + os.pathsep + env["PATH"],
           LEAN_NUM_THREADS="1", RAYON_NUM_THREADS="1",
           TMPDIR=str(workspace / ".tools" / "tmp"))
modules = ["PolynomialKernelScaling", "PolynomialLeftKernel"]
files = [f"RSBounds/{m}.lean" for m in modules] + [f"verification/{m}Audit.lean" for m in modules]
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_sha256": {f: hashlib.sha256((project / f).read_bytes()).hexdigest() for f in files},
    "runs": [],
}
commands = [(["lake", "build"] + [f"RSBounds.{m}" for m in modules], "kernel-scaling-left-build.log")]
commands += [(["lake", "env", "lean", f"verification/{m}Audit.lean"],
              f"kernel-scaling-left-{m}-axioms.log") for m in modules]
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
(project / "verification" / "kernel-scaling-left-run.json").write_text(json.dumps(record, indent=2) + "\n")
raise SystemExit(result)
