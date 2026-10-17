import Candidate.Cycle63.Assembly.Geometry
import Candidate.Cycle63.Physical.WitnessGeometry

namespace Cycle63.Assembly.Count
noncomputable section
open Arithmetic

/-- The new exact slot total supplies the generic whole-slot detector selector. -/
theorem count_slot_supply : (7/37:ℝ)*(7/8)≤ell := by norm_num [ell, theta]
/-- The manuscript's weaker inverse capacity is also supplied at the largest row norm. -/
theorem manuscript_slot_supply : (4/21:ℝ)*(7/8)≤ell := by norm_num [ell, theta]
theorem ell_pos : 0<ell := Arithmetic.ell_pos

theorem relative_slot_supply {N : ℕ} (length : Fin N→ℝ)
    (hsum : ∑j,length j=ell) {d : ℝ} (hd : 0<d) (hdmax : d≤7/8) :
    7/37≤∑j,length j/d := by
  rw [←Finset.sum_div,hsum]
  apply (le_div_iff₀ hd).mpr
  have hm:=mul_le_mul_of_nonneg_left hdmax (show (0:ℝ)≤7/37 by norm_num)
  linarith [count_slot_supply]
end
end Cycle63.Assembly.Count
