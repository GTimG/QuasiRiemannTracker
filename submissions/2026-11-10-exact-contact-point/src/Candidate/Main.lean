import Candidate.Notices
import Candidate.Local.Qrh.PositiveGap.BestEndpoint
set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : ((777 - Real.sqrt 1081) / 852 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact _root_.Qrh.PositiveGap.bound χ hs hpole

/-- The ranked rational upper bound: the bound of closest-fraction-contact. -/
theorem bound_le :
    ((777 - Real.sqrt 1081) / 852 : ℝ) ≤
      (2804966284017490358030969257914123810640482798488248385236764587735806455694206308975383836842958115341512355256943573632654341 /
        3211614609922119834694179379888743028634953588197852962423516288191911449231164741438582626063161096341458934143644085157872271 : ℝ) := by
  have h :
      777 - 852 * (2804966284017490358030969257914123810640482798488248385236764587735806455694206308975383836842958115341512355256943573632654341 /
        3211614609922119834694179379888743028634953588197852962423516288191911449231164741438582626063161096341458934143644085157872271 : ℝ) ≤ Real.sqrt 1081 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  rw [div_le_iff₀ (by norm_num)]
  linarith
end Candidate
#print axioms Candidate.bound
#print axioms Candidate.bound_le
