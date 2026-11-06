"""Final receipt statistics for the QR baseline rebuild."""
import collections
import json
import pathlib
import re

WS = pathlib.Path("/tmp/qr_rebuild/workspace")
OUT = pathlib.Path("/tmp/qr_rebuild")

# 1. olean inventory
lib = WS / ".lake/build/lib"
oleans = sorted(lib.rglob("*.olean"))
subs = [o for o in oleans if "Submissions/openai_baseline" in str(o)]
cand = [o for o in oleans if "/Candidate/" in str(o)]
sol = lib / "lean/Solution.olean"
cha = lib / "lean/Challenge.olean"

# built-modules list (module names)
mods = [str(o.relative_to(lib / "lean"))[:-6].replace("/", ".") for o in oleans]
(OUT / "built-modules.txt").write_text("\n".join(sorted(mods)) + "\n")

# 2. timing histogram from the final build log
raw = (OUT / "build.log").read_bytes().decode("utf8", "replace")
raw = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", raw).replace("\r", "\n")
times = sorted(float(m) for m in re.findall(r"\(([\d.]+)s\)", raw))
n = len(times)
timing = {
    "modules_timed": n,
    "min_s": times[0], "median_s": times[n // 2],
    "p90_s": times[int(n * 0.9)], "max_s": times[-1],
    "sum_compiler_minutes": round(sum(times) / 60, 1),
}

# 3. job/error totals
jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", raw)
errors = len(re.findall(r"^error:", raw, re.M))
exits = re.findall(r"=== (\w+) EXIT (\d+) ([\dT:Z-]+) ===", raw)

stats = {
    "root_package_oleans": len(oleans),
    "submission_oleans": len(subs),
    "candidate_olean": len(cand) == 1,
    "solution_olean": sol.exists(),
    "challenge_olean": cha.exists(),
    "build_jobs_by_phase": jobs,
    "error_lines_final_log": errors,
    "phase_exits": exits,
    "timing": timing,
}
print(json.dumps(stats, indent=1))
(OUT / "final-stats.json").write_text(json.dumps(stats, indent=2) + "\n")
