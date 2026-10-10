"""Run official Comparator with its own kernel sandboxes and cgroup limits.

This uses the official, sandbox-enabled CLI on already exported proof data.
It does not load candidate Lean/Lake code or alter any AppArmor policy.
The extra outer Palomar Bubblewrap layer is not used for the trusted judge;
the official Comparator still creates its normal sandbox for every kernel.
"""
from pathlib import Path
import json
import os
import subprocess
import sys

def judge_exports(*, lake, config, challenge_export, solution_export, scratch,
                  bwrap, lean_prefix, environment, tools, timeout, verifier):
    verifier.verify_tool_snapshot(tools)
    project, home, temporary = (scratch / part for part in ("project", "home", "tmp"))
    for directory in (project, home, temporary):
        directory.mkdir(parents=True)
    env = {"PATH": str(lean_prefix / "bin") + ":/usr/bin:/bin",
           "HOME": str(home), "TMPDIR": str(temporary), "LANG": "C.UTF-8",
           "COMPARATOR_BWRAP": str(bwrap), "LEAN_ABORT_ON_PANIC": "1"}
    command = [str(lake), "comparator", "--config", str(config),
               "--challenge-from-export", str(challenge_export),
               "--solution-from-export", str(solution_export)]
    timeout = verifier._deadline_timeout(timeout, command)
    properties = ("MemoryHigh=28G", "MemoryMax=32G", "MemorySwapMax=1G",
                  "CPUQuota=400%", "TasksMax=512", "LimitNOFILE=65536", "LimitFSIZE=17179869184")
    limits = verifier.translate_resource_properties(properties)
    status_path = scratch / "supervisor.json"
    liveness_path = scratch / "controller-alive.fifo"
    os.mkfifo(liveness_path, 0o600)
    args = [*verifier.supervisor_bootstrap(project), str(Path(sys.executable).resolve()),
            str(verifier.ROOT / "scripts/supervise_cgroup.py"), "--parent", "self", "--collect",
            "--deadline", str(timeout), "--grace", "30", "--cwd", str(project),
            "--status", str(status_path), "--liveness", str(liveness_path)]
    for key, value in limits.cgroup.items():
        args += ["--limit", f"{key}={value}"]
    for key, value in limits.rlimits.items():
        args += ["--rlimit", f"{key}={value}"]
    for key, value in env.items():
        args += ["--setenv", f"{key}={value}"]
    args += ["--", *command]
    (scratch / "execution.json").write_text(json.dumps({"argv": args,
        "mode": "official Comparator built-in kernel sandboxes; cgroup-supervised parent",
        "host_security_settings_changed": False}, indent=2) + "\n")
    log_path = scratch / "live.log"
    liveness = os.open(liveness_path, os.O_RDWR | os.O_CLOEXEC)
    try:
        with log_path.open("w") as stream:
            proc = subprocess.run(args, cwd=project, env=os.environ.copy(), stdout=stream,
                                  stderr=subprocess.STDOUT, timeout=timeout + 45)
    except BaseException:
        try:
            verifier.supervisor_outcome(status_path, supervisor_timeout=True)
        except verifier.VerificationError:
            pass
        raise
    finally:
        os.close(liveness)
        liveness_path.unlink()
    outcome = json.loads(status_path.read_text())
    if (outcome.get("state") != "finished" or not outcome.get("placement_ok")
            or outcome.get("launch_error") or outcome.get("populated_after_kill")):
        raise RuntimeError("Native Comparator cgroup supervision failed: " + json.dumps(outcome))
    if outcome.get("deadline_fired") or outcome.get("memory_events", {}).get("oom_kill", 0):
        raise RuntimeError("Native Comparator exceeded a resource limit: " + json.dumps(outcome))
    for name in limits.cgroup:
        if outcome.get("limits_applied", {}).get(name) is not True:
            raise RuntimeError("Native Comparator resource limit not established: " + name)
    verifier.verify_tool_snapshot(tools)
    return subprocess.CompletedProcess(command, proc.returncode, log_path.read_text(), "")
