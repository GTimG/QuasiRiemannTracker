/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact numerical Lambda assembly from native class/frame bounds. -/
import Candidate.C092.transport.PairedRetainedBudgetPay
set_option autoImplicit false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
open OAI OAI.SevenEighths CenteredMomentSecondWindowBudget

def windowHeightConstant (J : ℕ) : ℝ :=
  (1+2*Real.pi)^(4*J)*profileMoment J^2

theorem windowHeightConstant_nonneg (J : ℕ) : 0 ≤ windowHeightConstant J := by
  unfold windowHeightConstant
  positivity

theorem window_height_le (J : ℕ) (t : ℝ) :
    (heightEnvelope t^J*profileMoment J)^2 ≤ windowHeightConstant J*(1+‖t‖)^(2*J) := by
  have he : heightEnvelope t ≤ (1+2*Real.pi)^2*(1+‖t‖) := by
    have h0 : 1+‖t‖+2*Real.pi ≤ (1+2*Real.pi)*(1+‖t‖) := by
      nlinarith [mul_nonneg (norm_nonneg t) Real.pi_pos.le]
    have h1 := mul_le_mul_of_nonneg_right h0 (show 0 ≤ 1+2*Real.pi by positivity)
    convert h1 using 1 <;> (try dsimp only [heightEnvelope]) <;> ring
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (heightEnvelope_pos t).le he (2*J)) (sq_nonneg (profileMoment J))
  apply (le_of_eq ?_).trans (hp.trans_eq ?_)
  · rw [mul_pow,←pow_mul,Nat.mul_comm J 2]
  · unfold windowHeightConstant
    rw [mul_pow,←pow_mul,show 2*(2*J)=4*J by omega]
    ring

/-- The real finite box count, original class-image multiplicity, a^-2,
    grouped Fourier constant and profile-moment mass each occur once. -/
def classLambda (boxes Cg Mm Cb a : ℝ) (J : ℕ) : ℝ :=
  boxes*Cg*Mm*Cb*windowHeightConstant J/a^2

theorem classLambda_nonneg (boxes Cg Mm Cb a : ℝ) (J : ℕ)
    (hb : 0 ≤ boxes) (hg : 0 ≤ Cg) (hm : 0 ≤ Mm) (hc : 0 ≤ Cb) :
    0 ≤ classLambda boxes Cg Mm Cb a J := by
  unfold classLambda
  have := windowHeightConstant_nonneg J
  positivity

/-- Apply this to prime's literal actual_split_bound, with its actual
    rs.vol and numeric fixed-frame bound B0. It produces exactly the
    Lambda shape required by colored_label_budget. -/
theorem lambda_of_class_bound (F boxes Cg V Mm B₀ Cb NV₀ Psel a t : ℝ) (J : ℕ)
    (hboxes : 0 ≤ boxes) (hCg : 0 ≤ Cg) (hV : 0 ≤ V) (hMm : 0 ≤ Mm)
    (hCb : 0 ≤ Cb) (hNV₀ : 0 ≤ NV₀) (hPsel : 0 ≤ Psel)
    (hB₀ : B₀ ≤ Cb*V*NV₀*Psel)
    (hphysical : F ≤ boxes*Cg*((V/a^2)*Mm*B₀)*(heightEnvelope t^J*profileMoment J)^2) :
    F ≤ (classLambda boxes Cg Mm Cb a J*V^2*Psel*NV₀)*(1+‖t‖)^(2*J) := by
  have h1 := mul_le_mul_of_nonneg_left hB₀
    (show 0 ≤ boxes*Cg*(V/a^2)*Mm by positivity)
  have hphysical' : F ≤ (boxes*Cg*(V/a^2)*Mm*B₀)*(heightEnvelope t^J*profileMoment J)^2 := by
    convert hphysical using 1 <;> ring
  have h2 := hphysical'.trans (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
  have hCoeff : 0 ≤ boxes*Cg*(V/a^2)*Mm*(Cb*V*NV₀*Psel) := by positivity
  exact h2.trans ((mul_le_mul_of_nonneg_left (window_height_le J t) hCoeff).trans_eq
    (by unfold classLambda;ring))

#print axioms window_height_le
#print axioms lambda_of_class_bound
end
end QRH.Cycle092.PairedRetainedBudget
