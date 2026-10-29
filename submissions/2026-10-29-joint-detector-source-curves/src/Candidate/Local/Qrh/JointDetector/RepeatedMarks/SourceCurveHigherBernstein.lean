/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.BernsteinBox
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionArithmetic

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherCertificate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 60000
open scoped BigOperators
open BernsteinBox FractionArithmetic

def eval (a : Fin 16→ℝ) (x : ℝ) : ℝ := ∑i,a i*x^i.val

def coeff (a : Fin 16→ℝ) (lo hi : ℝ) (i : Fin 16) : ℝ :=
  coefficients (fun j (_k : Fin 1) => a j) lo hi i 0

theorem reconstruct (a : Fin 16→ℝ) (lo hi x : ℝ) :
    eval a (lo+(hi-lo)*x)=bernEval (fun i (_j : Fin 1)=>coeff a lo hi i) x 0 := by
  norm_num [eval,bernEval,coeff,coefficients,intervalPower,Fin.sum_univ_succ,Nat.choose]
  ring

theorem positive {a : Fin 16→ℝ} {lo hi x : ℝ} (hw : lo<hi)
    (hx : x∈Set.Icc lo hi) (ha : ∀i,0<coeff a lo hi i) : 0<eval a x := by
  let t := (x-lo)/(hi-lo)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hw).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hw)).2 (by linarith [hx.2])
  have heq : lo+(hi-lo)*t=x := by dsimp [t]; field_simp [(sub_pos.mpr hw).ne']; ring
  rw [←heq,reconstruct]
  unfold bernEval
  simp only [Fin.sum_univ_one,Nat.choose_zero_right,pow_zero,mul_one,sub_zero]
  apply Finset.sum_pos'
  · intro i _
    have hai := (ha i).le
    have htm : 0 ≤ 1-t := by linarith
    positivity
  · by_cases ht : t<1
    · refine ⟨0,Finset.mem_univ _,?_⟩
      have hp := mul_pos (ha 0) (pow_pos (show 0<1-t by linarith) 15)
      simpa using hp
    · have ht : t=1 := le_antisymm ht1 (le_of_not_gt ht)
      refine ⟨15,Finset.mem_univ _,?_⟩
      norm_num [ht]
      exact ha 15

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherCertificate
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveHigherCertificate.positive
