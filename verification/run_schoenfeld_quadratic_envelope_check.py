"""Compile and audit the uniform actual quadratic zero-sum envelope for Schoenfeld Theorem 11."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

root = Path(__file__).resolve().parent.parent
lean_environment = os.environ.copy()
assert lean_environment.get("LEAN_PATH"), "Source ../lean-env.sh before this check"

output = root / "verification/schoenfeld-quadratic-envelope-run.json"
record = {
    "kind": "fresh-local-compilation-and-transitive-axiom-audit",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in [
            "RSBounds/SchoenfeldQuadraticEnvelope.lean", "RSBounds/SchoenfeldQuadraticPairing.lean", "RSBounds/SchoenfeldWeightedZeros.lean", "RSBounds/SchoenfeldCoefficientPairing.lean", "RSBounds/SchoenfeldZeroWeights.lean", "RSBounds/SchoenfeldSquareCutoffs.lean", "RSBounds/QuadraticCoefficientBounds.lean", "RSBounds/QuadraticZeroKernel.lean", "RSBounds/QuadraticKernelScaling.lean", "RSBounds/QuadraticLowerKernel.lean", "RSBounds/PolynomialZeroPairing.lean", "RSBounds/RS75ZeroPowerDecay.lean", "RSBounds/RS75ZeroFree1975.lean", "verification/SchoenfeldQuadraticEnvelopeAudit.lean",
            "verification/run_schoenfeld_quadratic_envelope_check.py",
            "lean-toolchain", "lake-manifest.json",
        ]
    },
    "runs": [],
    "LEAN_PATH": lean_environment["LEAN_PATH"],
}

def save():
    output.write_text(json.dumps(record, indent=2) + "\n")

save()
source_text = (root / "RSBounds/SchoenfeldQuadraticEnvelope.lean").read_text()
audit_text = (root / "verification/SchoenfeldQuadraticEnvelopeAudit.lean").read_text()
combined_input = source_text + "\n" + "\n".join(
    line for line in audit_text.splitlines() if not line.startswith("import ")) + "\n"
record["stdin_sources"] = ["RSBounds/SchoenfeldQuadraticEnvelope.lean", "verification/SchoenfeldQuadraticEnvelopeAudit.lean"]
record["stdin_sha256"] = hashlib.sha256(combined_input.encode()).hexdigest()
save()
jobs = [
    (["lean", "-j1", "-Dprofiler=true", "--stdin", "-o",
      ".lake/build/lib/lean/RSBounds/SchoenfeldQuadraticEnvelope.olean",
      "RSBounds/SchoenfeldQuadraticEnvelope.lean"], "schoenfeld-quadratic-envelope-build.log"),
]
for command, name in jobs:
    started = time.monotonic()
    with (root / "verification" / name).open("w") as log:
        result = subprocess.run(command, cwd=root, env=lean_environment, input=combined_input, text=True, stdout=log, stderr=subprocess.STDOUT)
    record["runs"].append({"command": command, "log": name,
        "exit_code": result.returncode, "seconds": time.monotonic() - started})
    save()
    if result.returncode:
        record["exit_code"] = result.returncode
        save()
        raise SystemExit(result.returncode)

groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]",
    (root / "verification/schoenfeld-quadratic-envelope-build.log").read_text(), re.S)
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert len(groups) == 3 and all(
    {a.strip() for a in group.split(",") if a.strip()} <= allowed for group in groups
), "Transitive axiom audit failed"
record["axiom_audit"] = {"declarations": 3, "only_standard_axioms": True}
record["finished_utc"] = datetime.now(timezone.utc).isoformat()
record["exit_code"] = 0
save()
print(json.dumps(record, indent=2))
