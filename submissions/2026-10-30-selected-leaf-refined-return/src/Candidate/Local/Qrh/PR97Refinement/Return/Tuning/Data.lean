/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
import Candidate.Local.Qrh.PR97Refinement.Return.Tuning.Guards
import Candidate.Local.Qrh.PR97Refinement.Return.Constants

/-!
# The return's data over `ℚ`

Only the base constants are literals: the count face, the physical face, `c` (`theta = 1 - c`), `h`,
the reserve, the numerator cap and the switch `dm`. Everything else (`theta, ell, y, kappa`, the four
conductor edges and their capacities, the branch data) is computed from them by the same formulas as
`Constants.lean` and `Formulas.lean`; the `cast_*` lemmas identify each with its real counterpart.

The fixed target uses theta = 1746764287/2000000000 and h = 809686724723/10^12.
The count and physical source faces share B = 99999/100000 and L = 200001/100000;
their count and physical caps are 671447/5000000 and 3/25 respectively.
-/

set_option autoImplicit false

namespace QRH.PR97Refinement.ReturnTuning

open QRH.PR97Refinement.Return QRH.ArviReturnTuning

/-! ### Base constants (the literals of `Constants.lean`) -/

def cQ : ℚ := 253235713 / 2000000000
def hQ : ℚ := 809686724723 / 1000000000000
def reserveQ : ℚ := 1 / 100000000
def countBQ : ℚ := 99999 / 100000
def countLQ : ℚ := 200001 / 100000
def countCapQ : ℚ := 671447 / 5000000
def physBQ : ℚ := 99999 / 100000
def physLQ : ℚ := 200001 / 100000
def physCapQ : ℚ := 3 / 25
def numCapQ : ℚ := 3 / 40
def dmQ : ℚ := 19 / 25

/-! ### Derived constants -/

def thetaQ : ℚ := 1 - cQ
def ellQ : ℚ := 4 * cQ - 1 / 3
def yQ : ℚ := hQ - 2 * ellQ
def kappaQ : ℚ := 1 - 2 * cQ
def dpQ : ℚ := hQ + 1 / 10000000000
def d0Q : ℚ := 1 / 200
def oldCapQ (d : ℚ) : ℚ := min d (2 * yQ - d) / (6 * kappaQ)
def newCapQ (d : ℚ) : ℚ := min (numCapQ * d) ((2 * yQ - (2 - physBQ) * d) / physLQ)

def edgeDQ : Edge → ℚ
  | .oldSmall => d0Q
  | .oldSwitch | .newSwitch => dmQ
  | .newTop => dpQ

def edgeCQ (e : Edge) : ℚ :=
  match e with
  | .oldSmall | .oldSwitch => oldCapQ (edgeDQ e)
  | .newSwitch | .newTop => newCapQ (edgeDQ e)

/-- The rational data of the count branches (`branchB, branchL, branchCap, isCap`). -/
def toQ : CountBranch → BranchQ
  | .C => ⟨countBQ, countLQ, countCapQ, false⟩
  | .capC => ⟨countBQ, countLQ, countCapQ, true⟩
  | .weakC7 => ⟨countBQ - 7 / 4000, countLQ, countCapQ, false⟩
  | .capP => ⟨physBQ, physLQ, physCapQ, true⟩
  | .old => ⟨0, 1, 1 / 25, false⟩

/-! ### Identification with `Constants.lean` -/

theorem cast_c : ((cQ : ℚ) : ℝ) = c := by norm_num [cQ, c]
theorem cast_h : ((hQ : ℚ) : ℝ) = h := by norm_num [hQ, h]
theorem cast_reserve : ((reserveQ : ℚ) : ℝ) = reserve := by norm_num [reserveQ, reserve]
theorem cast_theta : ((thetaQ : ℚ) : ℝ) = theta := by simp [thetaQ, theta, cast_c]
theorem cast_ell : ((ellQ : ℚ) : ℝ) = ell := by simp [ellQ, ell, cast_c]
theorem cast_y : ((yQ : ℚ) : ℝ) = y := by simp [yQ, y, cast_h, cast_ell]
theorem cast_kappa : ((kappaQ : ℚ) : ℝ) = kappa := by simp [kappaQ, kappa, cast_c]

theorem cast_edgeD (e : Edge) : ((edgeDQ e : ℚ) : ℝ) = edgeD e := by
  cases e <;> simp [edgeDQ, edgeD, d0Q, d0, dmQ, dm, dpQ, dp, cast_h]

theorem cast_edgeC (e : Edge) : ((edgeCQ e : ℚ) : ℝ) = edgeC e := by
  have hb : ((physBQ : ℚ) : ℝ) = physicalB := by norm_num [physBQ, physicalB]
  have hl : ((physLQ : ℚ) : ℝ) = physicalLambda := by norm_num [physLQ, physicalLambda]
  have hn : ((numCapQ : ℚ) : ℝ) = numeratorCap := by norm_num [numCapQ, numeratorCap]
  cases e <;>
    simp [edgeCQ, edgeC, oldCapQ, oldCapacity, newCapQ, newCapacity, cast_edgeD, cast_y, cast_kappa,
      hb, hl, hn]

theorem cast_toQ (b : CountBranch) (hb : b ≠ .old) :
    ((toQ b).B : ℝ) = branchB b ∧ ((toQ b).L : ℝ) = branchL b ∧ ((toQ b).cap : ℝ) = branchCap b ∧
      (toQ b).capped = isCap b := by
  cases b
  · exact (hb rfl).elim
  all_goals
    refine ⟨?_, ?_, ?_, rfl⟩ <;>
      norm_num [toQ, branchB, branchL, branchCap, countBQ, countLQ, countCapQ, physBQ, physLQ, physCapQ,
        countCB, countCL, countCap, physicalB, physicalLambda, physicalCap]

/-- The guards of `Formulas.lean` from a passed window check. -/
theorem admission_of_check (b : CountBranch) (hb : b ≠ .old) (k : ℕ) (dlo dhi plo : ℚ)
    (h : windowCheck (toQ b) k dlo dhi plo = true) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (dlo : ℝ) dhi) (hp : p ∈ Set.Icc (plo : ℝ) (1 / 2)) (j : Fin 15) :
    0 < admissionGuard b δ p j := by
  obtain ⟨h1, h2, h3, h4⟩ := cast_toQ b hb
  have := window_admitted (toQ b) k dlo dhi plo h hδ hp j
  rw [h1, h2, h3, h4] at this
  rwa [admissionGuard_eq b hb]

end QRH.PR97Refinement.ReturnTuning
