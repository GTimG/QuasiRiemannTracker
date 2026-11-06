"""Stage the QR baseline rebuild workspace from tracker git blobs (LF-exact).

Mirrors verifier/standard/prepare.mjs semantics: read submission Git blobs as
data (git archive), assemble the QRH lake workspace per verifier/standard/
lakefile.lean, and render Challenge.lean/Solution.lean byte-exactly per
core/standard-challenge.mjs + verifier/challenge.mjs (theta = 7/8).
"""
import hashlib
import pathlib
import shutil
import subprocess
import sys

TRACKER = pathlib.Path("/tmp/qr_rebuild/tracker")
WS = pathlib.Path("/tmp/qr_rebuild/workspace")
STAGE = pathlib.Path("/tmp/qr_rebuild/stage")
SRC_PREFIX = "submissions/2026-10-06-openai-baseline/src"


def git(*args, binary=False):
    r = subprocess.run(["/usr/bin/git", "-C", str(TRACKER), *args],
                       capture_output=True, check=True)
    return r.stdout if binary else r.stdout.decode()


def blob(path):
    return git("cat-file", "blob", f"HEAD:{path}", binary=True)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    if WS.exists():
        sys.exit(f"workspace already exists: {WS}")
    if STAGE.exists():
        shutil.rmtree(STAGE)
    STAGE.mkdir(parents=True)
    WS.mkdir(parents=True)

    # 1. Extract submission src (Candidate/, Submissions/) via git archive.
    with open(STAGE / "src.tar", "wb") as f:
        subprocess.run(["/usr/bin/git", "-C", str(TRACKER), "archive", "HEAD", SRC_PREFIX],
                       stdout=f, check=True)
    subprocess.run(["tar", "-xf", str(STAGE / "src.tar"), "-C", str(STAGE)], check=True)
    src = STAGE / SRC_PREFIX
    shutil.copytree(src / "Candidate", WS / "Candidate")
    shutil.copytree(src / "Submissions", WS / "Submissions")

    # 2. Worker scaffolding: lakefile.lean, lake-manifest.json (blob bytes).
    (WS / "lakefile.lean").write_bytes(blob("verifier/standard/lakefile.lean"))
    (WS / "lake-manifest.json").write_bytes(blob("verifier/standard/lake-manifest.json"))
    (WS / "lean-toolchain").write_bytes(b"leanprover/lean4:v4.34.1\n")

    # 3. Render Challenge.lean + Solution.lean (standardChallenge recipe, 7/8).
    tpl = blob("verifier/upstream-challenge.lean").decode()
    assert sha(tpl.encode()) == "8fb13ad977bca104591fcbc6ef01a58496e7385053c9b1445f95749afc0eff54", \
        "template sha != pins.json challenge_sha256"
    challenge = (tpl
                 .replace("namespace OAI\n\nnamespace DirichletCharacter", "namespace QRH")
                 .replace("LFunction_ne_zero_of_seven_eighths_lt_re", "canonical_bound")
                 .replace("(7 / 8 : \u211d)", "(7 / 8 : \u211d)")  # exactBound('7/8').lean == '7 / 8'
                 .replace("end DirichletCharacter\n\nend OAI", "end QRH"))
    (WS / "Challenge.lean").write_bytes(challenge.encode())
    # Receipt cross-check: byte-identical to pr69 BaselineChallenge.lean.
    pr69 = blob("verifier/standard/receipts/pr69-ac76d5ef-20261023/BaselineChallenge.lean")
    assert challenge.encode() == pr69, "rendered challenge != pr69 BaselineChallenge.lean"

    solution = ("import Candidate.Main\n\n"
                + challenge.replace("import Mathlib\n", "")
                .replace("  sorry", "  exact Candidate.bound \u03c7 hs hpole"))
    (WS / "Solution.lean").write_bytes(solution.encode())

    # 4. Axioms probe script (run post-build via `lake env lean`).
    (WS / "Axioms.lean").write_bytes(
        ("import Solution\n"
         "import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Nonvanishing\n\n"
         "#print axioms QRH.canonical_bound\n"
         "#print axioms Submissions.openai_baseline.bound\n"
         "#print axioms OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re\n"
         "#print axioms OAI.DirichletCharacter.riemannZeta_ne_zero_of_seven_eighths_lt_re\n"
         ).encode())

    # 5. Inventory: file counts + root hashes for the receipt.
    n_cand = len(list((WS / "Candidate").rglob("*.lean")))
    n_subs = len(list((WS / "Submissions").rglob("*.lean")))
    print(f"Candidate modules: {n_cand}")
    print(f"Submissions modules: {n_subs}")
    print(f"baseline tree git-sha: {git('rev-parse', 'HEAD:submissions/2026-10-06-openai-baseline').strip()}")
    print(f"Challenge.lean sha256: {sha((WS / 'Challenge.lean').read_bytes())}")
    print(f"Solution.lean sha256: {sha((WS / 'Solution.lean').read_bytes())}")
    print(f"Candidate/Main.lean sha256: {sha((WS / 'Candidate' / 'Main.lean').read_bytes())}")
    blob_sha = sha(blob(f"{SRC_PREFIX}/Candidate/Main.lean"))
    assert blob_sha == sha((WS / "Candidate" / "Main.lean").read_bytes()), "archive != blob"
    print("archive-vs-blob integrity: OK")


if __name__ == "__main__":
    main()
