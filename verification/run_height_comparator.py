"""Independent native Comparator run for one configuration (height change, 2026-11-07).

Generalises run_zero_free_comparator.py to the psi, RS62 and zero-free configurations.
Usage: python3 verification/run_height_comparator.py --config comparator-psi.json \
           --toolchain-dir <lean-4.35.0 dir> [--inadvisably-no-sandbox]

Stages: pin checks; wrapper build; fresh transitive axiom audit of the solution
theorems; leanexport of both wrappers; `lake comparator` with both from-export flags
(bwrap sandbox on unless --inadvisably-no-sandbox); before/after hash checks of sources,
objects, tools and exports. Writes verification/height-comparator/<config stem>/<run id>/run.json.

Wrapper build: wrappers registered as lean_libs (RSZeroFree*) are built by Lake. The
psi and RS62 wrappers are not registered; they are compiled with the pinned `lean`
into a fresh directory under .lake/height-comparator-exports/, prepended to LEAN_PATH,
exactly as run_rs62_global_comparator.py does. No project object under
.lake/build is written by this script, and no mathematical module is compiled here:
those must already be built by `lake build`.

Differences from run_zero_free_comparator.py: the tool binaries' hashes are recorded,
not compared with ../../evidence/toolchain-binaries.json (absent from this project).
Not an IEANTN receipt.
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
TOOLCHAIN = "leanprover/lean4:v4.35.0"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LOCAL = {"RSBounds", "TernaryGoldbach", "Zeta23", "ZetaLean", "RHHeight", "RHHeight100",
         "HardyFirstZero", "HardyTenZeros", "RSPsiChallenge", "RSPsiSolution",
         "RS62GlobalChallenge", "RS62GlobalSolution", "RSZeroFreeChallenge", "RSZeroFreeSolution",
         "Schoenfeld1976Challenge", "Schoenfeld1976Solution", "Schoenfeld1976CondChallenge",
         "Schoenfeld1976CondSolution"}
# Same builtin and primitive roots as run_rs62_global_comparator.py / run_zero_free_comparator.py.
BUILTINS = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
    "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
]
EXPECTED = {
    "comparator-psi.json": ("RSPsiChallenge", "RSPsiSolution", ["RSBounds.RosserSchoenfeld1975"]),
    "comparator-rs62-global.json": ("RS62GlobalChallenge", "RS62GlobalSolution",
                                    ["RSBounds.RS62MertensFromFiniteRH", "RSBounds.RS62TotientFromFiniteRH"]),
    "comparator-zero-free.json": ("RSZeroFreeChallenge", "RSZeroFreeSolution", ["RSBounds.RS75ZeroFree1975"]),
    "comparator-schoenfeld-cond.json": ("Schoenfeld1976CondChallenge", "Schoenfeld1976CondSolution",
                                        ["RSBounds.Schoenfeld1976Theorem7Proved",
                                         "RSBounds.Schoenfeld1976Theorem11Proved"]),
    "comparator-schoenfeld.json": ("Schoenfeld1976Challenge", "Schoenfeld1976Solution",
                                   ["RSBounds.Schoenfeld1976Final"]),
}


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
    parser.add_argument("--config", required=True, choices=sorted(EXPECTED))
    parser.add_argument("--toolchain-dir", type=Path, required=True)
    parser.add_argument("--inadvisably-no-sandbox", action="store_true")
    args = parser.parse_args()
    config_path = ROOT / args.config
    challenge_mod, solution_mod, solution_imports = EXPECTED[args.config]
    tc = args.toolchain_dir.resolve()
    cfg = json.loads(config_path.read_text())
    require(set(cfg) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"},
            "Unexpected configuration field")
    require(cfg["challenge_module"] == challenge_mod and cfg["solution_module"] == solution_mod,
            "Comparator module mismatch")
    theorems = cfg["theorem_names"]
    require(set(cfg["permitted_axioms"]) == ALLOWED and len(cfg["permitted_axioms"]) == 3,
            "The permitted axioms must be exactly the standard three")
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain pin changed")
    challenge = ROOT / "comparator" / (challenge_mod + ".lean")
    solution = ROOT / "comparator" / (solution_mod + ".lean")
    require(imports(challenge) == ["Mathlib"], "Challenge must import Mathlib only")
    require(imports(solution) == solution_imports, f"Solution must import only {solution_imports}")
    lakefile = (ROOT / "lakefile.lean").read_text()
    lake_libs = all(f"lean_lib {m} where" in lakefile for m in (challenge_mod, solution_mod))
    binaries = {n: tc / "bin" / n for n in ["lean", "lake", "leanexport", "leanchecker"]}
    require(all(p.is_file() for p in binaries.values()), "Pinned toolchain binaries are incomplete")

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
    stem = Path(args.config).stem
    output = ROOT / "verification/height-comparator" / stem / run_id
    exports = ROOT / ".lake/height-comparator-exports" / stem / run_id
    fresh = exports / "objects"
    output.mkdir(parents=True, exist_ok=False)
    fresh.mkdir(parents=True, exist_ok=False)
    export_targets = BUILTINS + theorems + cfg["permitted_axioms"] + PRIMITIVES
    data = {"kind": "local-independent-comparator-after-height-change", "config": args.config,
            "status": "running", "official_ieantn_receipt": False,
            "started_utc": datetime.now(timezone.utc).isoformat(),
            "sandbox_disabled": args.inadvisably_no_sandbox, "definition_holes_permitted": False,
            "wrapper_build": ("lake build (lean_lib)" if lake_libs else
                              "pinned lean -j1 -R comparator -o into a fresh directory"),
            "permitted_axioms": sorted(ALLOWED), "toolchain": TOOLCHAIN,
            "tool_binary_sha256": snapshot(set(binaries.values())), "package_revisions": revisions,
            "theorems": theorems, "export_targets": export_targets, "runs": []}
    record = output / "run.json"

    def save() -> None:
        tmp = record.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(data, indent=2) + "\n")
        tmp.replace(record)

    def run(command: list[str], name: str, export: Path | None = None, run_env: dict | None = None) -> None:
        log = output / (name + ".log")
        started = time.monotonic()
        print("START", name, flush=True)
        with log.open("wb") as errors:
            stream = export.open("wb") if export is not None else errors
            try:
                code = subprocess.run(command, cwd=ROOT, env=run_env or env, stdin=subprocess.DEVNULL,
                                      stdout=stream,
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
        lake_path = subprocess.run([str(binaries["lake"]), "env", "printenv", "LEAN_PATH"], cwd=ROOT, env=env,
                                   capture_output=True, text=True, check=True).stdout.strip()
        wenv = dict(env)
        if lake_libs:
            run([str(binaries["lake"]), "build", challenge_mod, solution_mod], "wrapper-build")
            wrapper_objects = {ROOT / ".lake/build/lib/lean" / (m + ".olean") for m in (challenge_mod, solution_mod)}
            wenv["LEAN_PATH"] = lake_path
        else:
            wenv["LEAN_PATH"] = str(fresh) + os.pathsep + lake_path
            for module, source in ((challenge_mod, challenge), (solution_mod, solution)):
                run([str(binaries["lean"]), "-j1", "-R", str(ROOT / "comparator"), "-o",
                     str(fresh / (module + ".olean")), str(source)], module + "-build", run_env=wenv)
            wrapper_objects = {fresh / (m + ".olean") for m in (challenge_mod, solution_mod)}
        data["lean_path"] = wenv["LEAN_PATH"]
        audit = output / "SolutionAxiomAudit.lean"
        audit.write_text(f"import {solution_mod}\n" + "".join(f"#print axioms {t}\n" for t in theorems))
        run([str(binaries["lean"]), "-j1", str(audit)], "solution-axiom-audit", run_env=wenv)
        entries = axiom_entries((output / "solution-axiom-audit.log").read_text())
        require(set(entries) == set(theorems) and all(a <= ALLOWED for a in entries.values()),
                "Fresh solution transitive axiom audit failed")
        data["solution_axiom_audit"] = {name: sorted(a) for name, a in entries.items()}
        sources, objects = closure(solution_imports)
        sources |= {challenge, solution, config_path, Path(__file__).resolve(), ROOT / "lean-toolchain",
                    ROOT / "lakefile.lean", ROOT / "lake-manifest.json", audit}
        objects |= wrapper_objects
        data["source_sha256"], data["object_sha256"] = snapshot(sources), snapshot(objects)
        save()
        for module in (challenge_mod, solution_mod):
            run([str(binaries["leanexport"]), module, "--", *export_targets],
                module + "-export", export=exports / (module + ".export"), run_env=wenv)

        def unchanged() -> None:
            for category in ("source_sha256", "object_sha256", "tool_binary_sha256"):
                for name, expected in data[category].items():
                    path = Path(name) if Path(name).is_absolute() else ROOT / name
                    require(sha(path) == expected, f"Changed {category}: {name}")

        unchanged()
        command = [str(binaries["lake"]), "comparator", "--config", str(config_path),
                   "--challenge-from-export", str(exports / (challenge_mod + ".export")),
                   "--solution-from-export", str(exports / (solution_mod + ".export"))]
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
    print(f"{args.config}: comparison and native kernel replay passed:", record, flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print("Comparator not completed:", error, file=sys.stderr)
        raise SystemExit(1)
