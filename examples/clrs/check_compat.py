#!/usr/bin/env python3
"""Compile unchanged CLRS sources in an existing, version-matched Lake environment."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


TARGETS = [
    "CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations.Refinement",
    "CLRSLean.FourthEdition.Chapter_19.Section_19_3_Disjoint_Set_Forests",
    "CLRSLean.FourthEdition.Chapter_20.Section_20_2_BFS",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", type=Path, required=True)
    parser.add_argument("--environment", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--check-file", type=Path, action="append", default=[])
    parser.add_argument("--checks-only", action="store_true")
    args = parser.parse_args()
    checkout, environment, output = (
        path.resolve() for path in (args.checkout, args.environment, args.output)
    )
    source = checkout / "src"
    output.mkdir(parents=True, exist_ok=True)
    library = output / "lib"
    library.mkdir(exist_ok=True)

    def lake_output(*command):
        return subprocess.check_output(
            ["lake", "env", *command], cwd=environment, text=True
        ).strip()

    lean = lake_output("which", "lean")
    lean_path = lake_output("printenv", "LEAN_PATH")
    env = dict(os.environ, LEAN_PATH=str(library) + os.pathsep + lean_path)
    report = {
        "source_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=checkout, text=True
        ).strip(),
        "lean_version": lake_output("lean", "--version"),
        "environment": str(environment),
        "targets": TARGETS,
        "modules": [],
    }
    manifest = environment / "lake-manifest.json"
    if manifest.exists():
        report["dependencies"] = json.loads(manifest.read_text())["packages"]
    (output / "environment.json").write_text(
        json.dumps({"lean": lean, "LEAN_PATH": env["LEAN_PATH"]}, indent=2) + "\n"
    )

    if args.checks_only:
        if not args.check_file:
            parser.error("--checks-only requires --check-file")
        previous = json.loads((output / "results.json").read_text())
        keys = ("source_commit", "lean_version", "dependencies")
        if any(previous.get(key) != report.get(key) for key in keys):
            parser.error("existing results do not match this source, compiler, and dependencies")
        for row in previous["modules"]:
            path = source / (row["module"].replace(".", "/") + ".lean")
            if hashlib.sha256(path.read_bytes()).hexdigest() != row["source_sha256"]:
                parser.error("source changed since compilation: " + row["module"])
        report = previous

    order, dependencies = [], {}

    def visit(module):
        if module in dependencies:
            return
        path = source / (module.replace(".", "/") + ".lean")
        imports = re.findall(r"^import\s+(CLRSLean\.[\w.]+)", path.read_text(), re.M)
        dependencies[module] = imports
        for imported in imports:
            visit(imported)
        order.append(module)

    if not args.checks_only:
        for target in TARGETS:
            visit(target)
    statuses = {}
    for module in order:
        path = source / (module.replace(".", "/") + ".lean")
        result = {
            "module": module,
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        }
        blocked = [dep for dep in dependencies[module] if statuses[dep] != "passed"]
        if blocked:
            result.update(status="blocked", dependencies=blocked)
        else:
            olean = library / (module.replace(".", "/") + ".olean")
            olean.parent.mkdir(parents=True, exist_ok=True)
            command = [
                lean, "-Dpp.unicode.fun=true", "-Ddoc.verso=true",
                "-R", str(source), "-o", str(olean), str(path),
            ]
            log = output / (module + ".log")
            start = time.monotonic()
            print("Checking " + module, flush=True)
            with log.open("w") as stream:
                try:
                    completed = subprocess.run(
                        command, cwd=environment, env=env, stdout=stream,
                        stderr=subprocess.STDOUT, timeout=args.timeout,
                    )
                    result["returncode"] = completed.returncode
                    result["status"] = "passed" if completed.returncode == 0 else "failed"
                except subprocess.TimeoutExpired:
                    result["status"] = "timeout"
            result["seconds"] = round(time.monotonic() - start, 2)
            result["log"] = str(log)
            # Do not accept a successful elaboration that used a placeholder proof.
            if "declaration uses 'sorry'" in log.read_text():
                result["status"] = "sorry"
        statuses[module] = result["status"]
        report["modules"].append(result)
        (output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        print(result["status"] + ": " + module, flush=True)
    checks = []
    for path in args.check_file:
        path = path.resolve()
        log = output / (path.stem + ".log")
        start = time.monotonic()
        print("Checking " + str(path), flush=True)
        with log.open("w") as stream:
            try:
                completed = subprocess.run(
                    [lean, "-Ddoc.verso=true", "-R", str(path.parent), str(path)],
                    cwd=environment, env=env, stdout=stream,
                    stderr=subprocess.STDOUT, timeout=args.timeout,
                )
                status = "passed" if completed.returncode == 0 else "failed"
            except subprocess.TimeoutExpired:
                status = "timeout"
        contents = log.read_text()
        if "sorryAx" in contents or "declaration uses 'sorry'" in contents:
            status = "sorry"
        check = {
            "file": str(path), "status": status, "log": str(log),
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "seconds": round(time.monotonic() - start, 2),
        }
        checks.append(check)
        print(status + ": " + str(path), flush=True)
    if checks:
        report["checks"] = checks
        (output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    passed = all(row["status"] == "passed" for row in report["modules"] + checks)
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
