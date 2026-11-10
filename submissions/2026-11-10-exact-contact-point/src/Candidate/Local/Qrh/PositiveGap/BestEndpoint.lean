import Candidate.Local.Qrh.PositiveGap.SourceComposition
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.Endpoint
set_option autoImplicit false
namespace Qrh.PositiveGap
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source QRH.PositiveGap.Return
theorem return_source [TargetC] (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (1 - eps) (2 + 10 * eps) (671447/5000000) := by
  apply QRH.PositiveGap.Return.Tuning.uniform_restrict
    (strong := globalFace (1 - eps) (2 + 10 * eps) (QRH.PositiveGapTightSelected.rCap (2 + 10 * eps)))
  · constructor <;> (dsimp [globalFace, QRH.PositiveGapTightSelected.rCap,
      QRH.PositiveGapTightSelected.rGamma, QRH.PositiveGapTightSelected.rTop]; linarith [eps_pos, eps_le])
  · exact QRH.PositiveGap.source eps eps_pos eps_le hβ
theorem beta_le_theta_c [TargetC] : HeckeZeroSupremum.beta ≤ theta :=
  QRH.PositiveGap.Return.Tuning.beta_le_target_of_global_source return_source
lemma sqrt_1081_bounds : (3287856 / 100000 : ℝ) < Real.sqrt 1081 ∧ Real.sqrt 1081 < 3287857 / 100000 := by
  constructor
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3287856 / 100000)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3287857 / 100000)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
theorem beta_le_theta :
    HeckeZeroSupremum.beta ≤ (777 - Real.sqrt 1081) / 852 := by
  have hsq : Real.sqrt 1081 ^ 2 = 1081 := Real.sq_sqrt (by norm_num)
  have hsqrt := sqrt_1081_bounds
  have hb0 : HeckeZeroSupremum.beta ≤ 1 - 1266180 / 10000000 :=
    @beta_le_theta_c ⟨1266180 / 10000000, le_rfl, by norm_num⟩
  by_contra hlt
  push Not at hlt
  set c1 : ℝ := (1 - HeckeZeroSupremum.beta + (75 + Real.sqrt 1081) / 852) / 2
  have hc1_lo : (1266180 / 10000000 : ℝ) ≤ c1 := by unfold c1; linarith [hb0, hsqrt.1]
  have hc1_quad : (852 * c1 - 75) ^ 2 < 1081 := by
    have h1 : 0 < 852 * c1 - 75 := by unfold c1; linarith [hb0, hsqrt.1]
    have h2 : 852 * c1 - 75 < Real.sqrt 1081 := by unfold c1; linarith [hlt]
    nlinarith [hsq, h1, h2]
  have hb1 : HeckeZeroSupremum.beta ≤ 1 - c1 :=
    @beta_le_theta_c ⟨c1, hc1_lo, hc1_quad⟩
  unfold c1 at hb1
  linarith [hb1, hlt]
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : ((777 - Real.sqrt 1081) / 852 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  have hsqrt := sqrt_1081_bounds
  exact Cycle25.dirichlet_of_hecke (by linarith [hsqrt.2])
    (fun η s hs hpole => HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η
      (beta_le_theta.trans_lt hs) hpole) χ s hs hpole
end
end Qrh.PositiveGap
