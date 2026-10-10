"""Rebuild the submitted source closure without the development project cache.

Only pinned OpenAI and package libraries are reused. All Cycle25 modules and
the three copied, independent moment modules are compiled from frozen source.
The original proof and all earlier acceptance evidence remain read-only.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "formalization"
PREVIOUS = ROOT.parent / "zeta-formalization"
LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, obj):
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n")


def imports(path):
    names = []
    for line in path.read_text().splitlines():
        match = re.match(r"\s*(?:public\s+|private\s+|meta\s+)?import\s+(.*)", line)
        if match:
            names.extend(match.group(1).split("--")[0].split())
    return names


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", required=True)
    parser.add_argument("--entry", action="append", required=True)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    assert re.fullmatch(r"clean-[0-9]{3}", args.run)
    assert 1 <= args.jobs <= 4
    work = ROOT / "evidence" / args.run
    work.mkdir()
    for name in ("src", "lib", "logs", "upstream-lib"):
        (work / name).mkdir()
    started = time.monotonic()
    pending = list(args.entry)
    modules = {}
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        path = PROJECT / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise RuntimeError("Missing local source " + module)
        deps = [name for name in imports(path)
                if name.startswith(("Cycle25.", "OAI.", "ZetaZeroFree."))]
        rel = path.relative_to(PROJECT)
        target = work / "src" / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        modules[module] = {"module": module, "path": str(rel),
                           "sha256": digest(path), "bytes": path.stat().st_size,
                           "imports": deps}
        pending.extend(deps)
    oai_inventory = json.loads((ROOT / "evidence/oai-source-inventory.json").read_text())
    expected_oai = {item["module"]: item for item in oai_inventory["modules"]}
    reused = []
    for module, item in modules.items():
        if not module.startswith("OAI."):
            continue
        assert item["sha256"] == expected_oai[module]["sha256"]
        base = PREVIOUS / ".lake/build/lib/lean" / Path(item["path"]).with_suffix("")
        for suffix in (".olean", ".ilean"):
            source = base.with_suffix(suffix)
            destination = work / "upstream-lib" / Path(item["path"]).with_suffix(suffix)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
            reused.append({"path": str(destination.relative_to(work)),
                           "sha256": digest(destination), "bytes": destination.stat().st_size})
    packages = sorted((PREVIOUS / ".lake/packages").iterdir())
    libraries = [(p / ".lake/build/lib/lean").resolve() for p in packages
                 if (p / ".lake/build/lib/lean").is_dir()]
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(map(str, [work / "lib", work / "upstream-lib", *libraries]))
    env["LEAN_SRC_PATH"] = str(work / "src")
    env["LEAN_NUM_THREADS"] = "1"
    inventory = {"entries": args.entry, "sources": sorted(modules.values(), key=lambda i: i["path"]),
                 "upstream_artifacts": reused, "package_library_roots": list(map(str, libraries)),
                 "source_compiler": subprocess.check_output([str(LEAN), "--version"], text=True).strip(),
                 "source_compiler_sha256": digest(LEAN),
                 "cache_scope": "Pinned OAI and third-party packages only; no development Cycle25 or old endpoint cache"}
    write(work / "input-inventory.json", inventory)
    rebuild = {name for name in modules if not name.startswith("OAI.")}
    done = set(modules) - rebuild
    outcomes = {}

    def compile_module(module):
        rel = Path(modules[module]["path"])
        output = (work / "lib" / rel).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(LEAN), "-j1", "-M8192", "-DautoImplicit=false",
                   "-o", str(output), "-i", str(output.with_suffix(".ilean")), str(rel)]
        begin = time.monotonic()
        proc = subprocess.run(command, cwd=work / "src", env=env,
                              capture_output=True, text=True, timeout=1800)
        log = work / "logs" / (module + ".log")
        log.write_text(proc.stdout + proc.stderr)
        return {"module": module, "returncode": proc.returncode,
                "elapsed_seconds": round(time.monotonic() - begin, 3),
                "log": str(log.relative_to(work)), "log_sha256": digest(log)}

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running = {}
        remaining = set(rebuild)
        while remaining or running:
            for module in sorted(remaining):
                if len(running) == args.jobs:
                    break
                if set(modules[module]["imports"]) <= done:
                    running[pool.submit(compile_module, module)] = module
                    remaining.remove(module)
            if not running:
                raise RuntimeError("Cyclic or unresolved imports: " + repr(sorted(remaining)))
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                module = running.pop(future)
                result = future.result()
                outcomes[module] = result
                write(work / "progress.json", {"compiled": len(outcomes), "total": len(rebuild),
                      "last": result, "running": list(running.values())})
                if result["returncode"]:
                    raise RuntimeError("Compilation failed: " + result["log"])
                done.add(module)
                if len(outcomes) % 25 == 0:
                    print(f"Compiled {len(outcomes)}/{len(rebuild)}", flush=True)
    for item in modules.values():
        if digest(PROJECT / item["path"]) != item["sha256"]:
            raise RuntimeError("Source changed during build: " + item["path"])
    artifacts = [{"path": str(p.relative_to(work)), "bytes": p.stat().st_size, "sha256": digest(p)}
                 for p in sorted((work / "lib").rglob("*.olean"))]
    report = {"passed": True, "entries": args.entry, "sources": inventory["sources"],
              "artifacts": artifacts, "outcomes": list(outcomes.values()),
              "compiled_modules": len(outcomes), "reused_upstream_modules": len(modules) - len(rebuild),
              "elapsed_seconds": round(time.monotonic() - started, 3),
              "completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "input_inventory_sha256": digest(work / "input-inventory.json")}
    write(work / "result.json", report)
    print(json.dumps({key: report[key] for key in ("passed", "compiled_modules", "elapsed_seconds")}), flush=True)


if __name__ == "__main__":
    main()
