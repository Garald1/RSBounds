"""Compile and audit the global totient reduction (one Lean process at a time)."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
record = {
    "kind": "fresh-local-compilation-and-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/TotientGlobalReduction.lean",
            "RSBounds/Totient.lean",
            "RSBounds/TotientAnalyticReduction.lean",
            "RSBounds/SmallTotientProduct.lean",
            "verification/TotientGlobalReductionAudit.lean",
        ]
    },
    "runs": [],
}
jobs = [
    (["lake", "build", "RSBounds.TotientGlobalReduction"], "totient-global-build.log"),
    (["lake", "env", "lean", "verification/TotientGlobalReductionAudit.lean"],
     "totient-global-axioms.log"),
]
for command, name in jobs:
    path = root / "verification" / name
    with path.open("w") as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name, "exit_code": result.returncode})
    if result.returncode:
        break
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = result.returncode
(root / "verification/totient-global-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
