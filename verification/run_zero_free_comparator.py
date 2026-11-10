"""Independent native Comparator run for RS75 Theorem 1 (zero-free region).

Modelled on run_rs62_global_comparator.py, with three differences:
- the challenge and solution wrappers are built by Lake (lean_lib entries
  RSZeroFreeChallenge / RSZeroFreeSolution), never by bare `lean -o`;
- the transitive axiom audit is run fresh against the Lake-built objects;
- the process sandbox (bwrap) is used unless --inadvisably-no-sandbox is given,
  and the run record says which.

Stages: pins and wrapper checks, `lake build` of both wrappers, fresh axiom audit,
leanexport of both wrappers, `lake comparator` with both from-export flags, and
before/after hash checks of sources, objects, tools and exports. Writes
verification/zero-free-comparator/<run id>/run.json. Not an IEANTN receipt.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT / "comparator-zero-free.json"
TOOLCHAIN = "leanprover/lean4:v4.35.0"
THEOREMS = [
    "TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free_high",
    "TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free",
]
SOLUTION_MODULES = ["RSBounds.RS75ZeroFree1975"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LOCAL = {"RSBounds", "TernaryGoldbach", "Zeta23", "ZetaLean", "RHHeight", "RHHeight100",
         "HardyFirstZero", "HardyTenZeros"}
# Same builtin and primitive roots as run_rs62_global_comparator.py.
BUILTINS = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
    "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def label(path: Path) -> str:
    return str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)


def snapshot(paths: set[Path]) -> dict[str, str]:
    return {label(p): sha(p) for p in sorted(paths)}


def imports(path: Path) -> list[str]:
    text = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
    return re.findall(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)", text, re.M)


def axiom_entries(text: str) -> dict[str, set[str]]:
    found = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    return {name: {a.strip() for a in group.split(",") if a.strip()} for name, group in found}


def closure(start: list[str]) -> tuple[set[Path], set[Path]]:
    roots = [ROOT, ROOT / "vendor/rh100", ROOT / ".lake/packages/TernaryGoldbach"]
    sources, objects, seen = set(), set(), set()

    def visit(module: str) -> None:
        if module in seen or module.split(".")[0] not in LOCAL:
            return
        seen.add(module)
        rel = Path(module.replace(".", "/") + ".lean")
        root = next((r for r in roots if (r / rel).is_file()), None)
        require(root is not None, f"Unresolved local module: {module}")
        sources.add(root / rel)
        build = root if module.startswith("TernaryGoldbach.") else ROOT
        obj = build / ".lake/build/lib/lean" / rel.with_suffix(".olean")
        require(obj.is_file(), f"Missing Lake-built object: {module}")
        objects.add(obj)
        for dep in imports(root / rel):
            visit(dep)

    for module in start:
        visit(module)
    return sources, objects


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain-dir", type=Path, required=True)
    parser.add_argument("--inadvisably-no-sandbox", action="store_true")
    args = parser.parse_args()
    tc = args.toolchain_dir.resolve()
    cfg = json.loads(CONFIG.read_text())
    require(set(cfg) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"},
            "Unexpected configuration field")
    require(cfg["challenge_module"] == "RSZeroFreeChallenge" and cfg["solution_module"] == "RSZeroFreeSolution"
            and cfg["theorem_names"] == THEOREMS, "Comparator target/module mismatch")
    require(set(cfg["permitted_axioms"]) == ALLOWED and len(cfg["permitted_axioms"]) == 3,
            "The permitted axioms must be exactly the standard three")
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain pin changed")
    challenge, solution = ROOT / "comparator/RSZeroFreeChallenge.lean", ROOT / "comparator/RSZeroFreeSolution.lean"
    require(imports(challenge) == ["Mathlib"], "Challenge must import Mathlib only")
    require(imports(solution) == SOLUTION_MODULES, "Solution must import only RSBounds.RS75ZeroFree1975")
    lakefile = (ROOT / "lakefile.lean").read_text()
    for lib in ("RSZeroFreeChallenge", "RSZeroFreeSolution"):
        require(f"lean_lib {lib} where" in lakefile, f"lakefile lacks lean_lib {lib}")
    binaries = {name: tc / "bin" / name for name in ["lean", "lake", "leanexport", "leanchecker"]}
    require(all(p.is_file() for p in binaries.values()), "Pinned toolchain binaries are incomplete")
    expected_bins = json.loads((ROOT.parents[1] / "evidence/toolchain-binaries.json").read_text())
    require(all(sha(binaries[n]) == h for n, h in expected_bins.items()), "Toolchain binaries differ from evidence")

    env = os.environ.copy()
    env.update(LEAN_SYSROOT=str(tc), ELAN="", LEAN_NUM_THREADS="1")
    env["PATH"] = str(tc / "bin") + os.pathsep + env.get("PATH", "")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    revisions = {}
    for p in manifest["packages"]:
        d = ROOT / ".lake/packages" / p["name"]
        rev = subprocess.run(["git", "-C", str(d), "rev-parse", "HEAD"], capture_output=True, text=True,
                             check=True).stdout.strip()
        require(rev == p["rev"], f"Package revision differs from manifest: {p['name']}")
        require(subprocess.run(["git", "-C", str(d), "diff", "--quiet", "HEAD", "--"]).returncode == 0,
                f"Tracked package sources are modified: {p['name']}")
        revisions[p["name"]] = rev

    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = ROOT / "verification/zero-free-comparator" / run_id
    exports = ROOT / ".lake/zero-free-exports" / run_id
    output.mkdir(parents=True, exist_ok=False)
    exports.mkdir(parents=True, exist_ok=False)
    export_targets = BUILTINS + THEOREMS + cfg["permitted_axioms"] + PRIMITIVES
    data = {"kind": "local-independent-zero-free-comparator", "status": "running",
            "official_ieantn_receipt": False, "started_utc": datetime.now(timezone.utc).isoformat(),
            "sandbox_disabled": args.inadvisably_no_sandbox, "definition_holes_permitted": False,
            "wrapper_build": "lake build (lean_lib RSZeroFreeChallenge, RSZeroFreeSolution)",
            "permitted_axioms": sorted(ALLOWED), "toolchain": TOOLCHAIN,
            "tool_binary_sha256": snapshot(set(binaries.values())), "package_revisions": revisions,
            "export_targets": export_targets, "runs": []}
    record = output / "run.json"

    def save() -> None:
        tmp = record.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(data, indent=2) + "\n")
        tmp.replace(record)

    def run(command: list[str], name: str, export: Path | None = None) -> None:
        log = output / (name + ".log")
        started = time.monotonic()
        print("START", name, flush=True)
        with log.open("wb") as errors:
            stream = export.open("wb") if export is not None else errors
            try:
                code = subprocess.run(command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL, stdout=stream,
                                      stderr=errors if export is not None else subprocess.STDOUT).returncode
            finally:
                if export is not None:
                    stream.close()
        entry = {"command": command, "log": label(log), "log_sha256": sha(log), "exit_code": code,
                 "seconds": time.monotonic() - started}
        if export is not None:
            entry.update(export=label(export), export_sha256=sha(export), export_bytes=export.stat().st_size)
        data["runs"].append(entry)
        save()
        print("END", name, code, flush=True)
        require(code == 0, f"Stage did not complete successfully: {name} ({code})")

    save()
    try:
        run([str(binaries["lean"]), "--version"], "toolchain-version")
        run([str(binaries["lake"]), "build", "RSZeroFreeChallenge", "RSZeroFreeSolution"], "wrapper-build")
        run([str(binaries["lake"]), "env", "lean", "verification/RSZeroFreeSolutionAudit.lean"], "solution-axiom-audit")
        entries = axiom_entries((output / "solution-axiom-audit.log").read_text())
        require(set(entries) == set(THEOREMS) and all(a <= ALLOWED for a in entries.values()),
                "Fresh solution transitive axiom audit failed")
        data["solution_axiom_audit"] = {name: sorted(a) for name, a in entries.items()}
        sources, objects = closure(SOLUTION_MODULES)
        sources |= {challenge, solution, CONFIG, Path(__file__).resolve(), ROOT / "lean-toolchain",
                    ROOT / "lakefile.lean", ROOT / "lake-manifest.json",
                    ROOT / "verification/RSZeroFreeSolutionAudit.lean"}
        objects |= {ROOT / ".lake/build/lib/lean/RSZeroFreeChallenge.olean",
                    ROOT / ".lake/build/lib/lean/RSZeroFreeSolution.olean"}
        data["source_sha256"], data["object_sha256"] = snapshot(sources), snapshot(objects)
        save()
        for module in (cfg["challenge_module"], cfg["solution_module"]):
            run([str(binaries["lake"]), "env", str(binaries["leanexport"]), module, "--", *export_targets],
                module + "-export", export=exports / (module + ".export"))

        def unchanged() -> None:
            for category in ("source_sha256", "object_sha256", "tool_binary_sha256"):
                for name, expected in data[category].items():
                    path = Path(name) if Path(name).is_absolute() else ROOT / name
                    require(sha(path) == expected, f"Changed {category}: {name}")

        unchanged()
        command = [str(binaries["lake"]), "comparator", "--config", str(CONFIG),
                   "--challenge-from-export", str(exports / "RSZeroFreeChallenge.export"),
                   "--solution-from-export", str(exports / "RSZeroFreeSolution.export")]
        if args.inadvisably_no_sandbox:
            command.append("--inadvisably-no-sandbox")
        run(command, "comparator")
        require("Your solution is okay!" in (output / "comparator.log").read_text(),
                "Comparator returned without its successful comparison verdict")
        unchanged()
        for stage in data["runs"]:
            if "export" in stage:
                require(sha(ROOT / stage["export"]) == stage["export_sha256"], "Export changed during comparison")
        data.update(status="passed", exit_code=0)
    except (Exception, KeyboardInterrupt) as error:
        data.update(status="failed-or-incomplete", exit_code=1, error=str(error) or "Interrupted")
        raise
    finally:
        data["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    print("Zero-free comparison and native kernel replay passed:", record, flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print("Zero-free comparator not completed:", error, file=sys.stderr)
        raise SystemExit(1)
