"""Explicit mathematical contract shared by the independent challenge/solution.

The challenge imports standard L-functions and pinned upstream presentation
definitions, never a Cycle25 result. Its algebraic endpoint is stated directly
in terms of the quartic and the interval (1/6, 1/5).
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NAMES = ["Cycle25Verification." + name for name in (
    "allDirichlet", "zeta", "allHecke", "exactAllDirichlet", "exactZeta", "exactAllHecke", "plainMoment")]

ENDPOINTS = r'''
namespace Cycle25Verification
open scoped _root_.DirichletCharacter

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (683505193 / 781250000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  DIRICHLET_PROOF

theorem zeta {s : ℂ} (hs : (683505193 / 781250000 : ℝ) < s.re) (_hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  ZETA_PROOF

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (683505193 / 781250000 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  HECKE_PROOF

theorem exactAllDirichlet (ell : ℝ) (hlo : 1/6 ≤ ell) (hhi : ell ≤ 1/5)
    (hpoly : 927*ell^4-3135*ell^3+2433*ell^2+275*ell-100 = 0)
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 11/12-ell/4 < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  EXACT_DIRICHLET_PROOF

theorem exactZeta (ell : ℝ) (hlo : 1/6 ≤ ell) (hhi : ell ≤ 1/5)
    (hpoly : 927*ell^4-3135*ell^3+2433*ell^2+275*ell-100 = 0)
    {s : ℂ} (hs : 11/12-ell/4 < s.re) (_hpole : s ≠ 1) : riemannZeta s ≠ 0 := by
  EXACT_ZETA_PROOF

theorem exactAllHecke (ell : ℝ) (hlo : 1/6 ≤ ell) (hhi : ell ≤ 1/5)
    (hpoly : 927*ell^4-3135*ell^3+2433*ell^2+275*ell-100 = 0)
    (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : 11/12-ell/4 < s.re) (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  EXACT_HECKE_PROOF
end Cycle25Verification
'''


def sources():
    # Copy only the inspected theorem signature; none of its proof is trusted
    # by the challenge. The local mesh definition below has an explicit body.
    text = (ROOT / "formalization/Cycle25/Energy/Endpoint.lean").read_text()
    signature = text.split("theorem terminal_positive_at", 1)[1].split(" := by", 1)[0]
    prelude = r'''
namespace Cycle25Verification
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
local notation "O" => HeckeFamily.O
def commonMesh (Mcap Bmask L ε : ℝ) : ℝ := fineMesh Mcap Bmask L (3/4) ε
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
'''
    moment = prelude + "theorem plainMoment" + signature + " := by\n  MOMENT_PROOF\nend\nend Cycle25Verification\n"
    statements = ENDPOINTS + moment
    imports = """import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
import OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
import OAI.NumberTheory.DirichletL.Energy.WidthRanges

"""
    challenge = imports + statements
    solution = "import Cycle25.Assembly.Final.Endpoint\n\n" + statements
    isolate = """have he : ell = Cycle25.Arithmetic.ell0 :=
    Cycle25.Arithmetic.quartic_root_unique ⟨hlo,hhi⟩ hpoly
  subst ell
  """
    proofs = {
        "DIRICHLET_PROOF": "exact Cycle25.dirichlet_nonzero_catalogue χ s hs hpole",
        "ZETA_PROOF": "exact Cycle25.zeta_nonzero_catalogue s hs",
        "HECKE_PROOF": "exact Cycle25.hecke_nonzero_catalogue χ s hs (by tauto)",
        "EXACT_DIRICHLET_PROOF": isolate + "exact Cycle25.dirichlet_nonzero χ s hs hpole",
        "EXACT_ZETA_PROOF": isolate + "exact Cycle25.zeta_nonzero s hs",
        "EXACT_HECKE_PROOF": isolate + "exact Cycle25.hecke_nonzero χ s hs (by tauto)",
        "MOMENT_PROOF": """simpa only [commonMesh, Cycle25.Energy.commonMesh] using
    (Cycle25.Energy.terminal_positive_at (α := α) M H hH W aslot bslot a b radial
      Bmask L lo hi Mcap κ ε haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap
      hκlo hκhi hε hbeta hκbeta)""",
    }
    # Long markers must be replaced first because some contain shorter ones.
    for key in sorted(proofs, key=len, reverse=True):
        challenge = challenge.replace(key, "sorry")
        solution = solution.replace(key, proofs[key])
    return {"Challenge": challenge, "Solution": solution}
