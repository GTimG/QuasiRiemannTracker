/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowCompletePayment

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open Cycle63InitialMass

/-- The native all-height source constant is affine in the pointwise
physical coefficient. Its degree and splice threshold have no dependence
on that coefficient. This identity makes a whole returned forest pass
through the existing all-height consumer without modifying its degree. -/
theorem native_low_height_constant_affine
    (N degree : ℕ) (e supply ap Cg extra Cu Cfirst Cbox b Cs Kcoarse : ℝ) :
    mainLowCompleteHeightConstant N degree e supply ap (Cg+extra) Cu Cfirst Cbox b Cs Kcoarse =
      mainLowCompleteHeightConstant N degree e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse+
      (2+4*Real.pi)^degree*mainLowCompleteFee N e supply ap 1 Cu Cfirst Cbox b Cs*extra := by
  unfold mainLowCompleteHeightConstant mainLowCompleteFee
  ring

/-- Exact pointwise returned-source split. No eventual theorem is
specialized to a moving coefficient: the existing pointwise physical and
all-height receipts can be applied at the given Z, then this identity
separates the fixed old coefficient and the SAME whole returned forest. -/
theorem native_low_height_return_split
    (N degree : ℕ) (e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse Z target Ret : ℝ)
    (hZ : 0<Z) :
    mainLowCompleteHeightConstant N degree e supply ap (Cg+Z^(-target)*Ret)
      Cu Cfirst Cbox b Cs Kcoarse*Z^target =
      mainLowCompleteHeightConstant N degree e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse*Z^target+
      (2+4*Real.pi)^degree*mainLowCompleteFee N e supply ap 1 Cu Cfirst Cbox b Cs*Ret := by
  rw [native_low_height_constant_affine]
  have hcancel : Z^(-target)*Z^target=(1:ℝ) := by
    rw [←Real.rpow_add hZ]
    simp only [neg_add_cancel,Real.rpow_zero]
  calc
    _ = mainLowCompleteHeightConstant N degree e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse*Z^target+
        (2+4*Real.pi)^degree*mainLowCompleteFee N e supply ap 1 Cu Cfirst Cbox b Cs*
          Ret*(Z^(-target)*Z^target) := by ring
    _ = _ := by rw [hcancel,mul_one]

/-- Localize the actual native all-height receipt to a fixed parent. The
small-height return uses one normalized whole-forest scalar, while the old
term retains its first-seed reciprocal until the true norm gate is used.
The degree and coarse absorption are chosen before `Z`, `Ret`, or the
source configuration. In particular no eventual theorem is applied to a
coefficient depending on `Z`. -/
theorem native_low_returned_height_splice
    (coarse targetMin tau : ℝ) (htau : 0<tau) (smallDegree : ℕ) :
    ∃degree : ℕ, ∀(Z target v height t u E Cs Cc control seedNorm Ret : ℝ),
      1 ≤ Z → targetMin ≤ target → 0 ≤ height → 0 ≤ Cs → 0 ≤ Cc → 0 ≤ control →
      1 ≤ seedNorm → 0 ≤ Ret →
      (2*(1+|v|+height+2*Real.pi*(|t|+|u|)) ≤ Z^tau →
        E ≤ (Cs*control*Z^target/seedNorm+Ret*control)*
          (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^smallDegree) →
      E ≤ Cc*control*Z^coarse →
      E ≤ ((2+4*Real.pi)^degree*(Cs+Cc)*control*Z^target+
        (2+4*Real.pi)^degree*Ret*control)*
        (1+|v|+height)^degree*(1+|t|)^degree*(1+|u|)^degree := by
  obtain ⟨degree,hsplice⟩ := geometry_uniform_shifted_height_splice coarse targetMin tau htau smallDegree
  refine ⟨degree,?_⟩
  intro Z target v height t u E Cs Cc control seedNorm Ret hZ htarget hheight hCs hCc hcontrol
    hseed hRet hsmall hcoarse
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hcoeff : 0 ≤ Cs+Z^(-target)*Ret :=
    add_nonneg hCs (mul_nonneg (Real.rpow_nonneg hZ0.le _) hRet)
  have hcancel : Z^(-target)*Z^target=(1:ℝ) := by
    rw [←Real.rpow_add hZ0]
    simp only [neg_add_cancel,Real.rpow_zero]
  have hidentity : (Cs+Z^(-target)*Ret)*control*Z^target =
      Cs*control*Z^target+Ret*control := by
    calc
      _ = Cs*control*Z^target+Ret*control*(Z^(-target)*Z^target) := by ring
      _ = _ := by rw [hcancel,mul_one]
  have hsmall' : 2*(1+|v|+height+2*Real.pi*(|t|+|u|)) ≤ Z^tau →
      E ≤ (Cs+Z^(-target)*Ret)*control*Z^target*
        (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^smallDegree := by
    intro hH
    apply (hsmall hH).trans
    rw [hidentity]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hfrac : Cs*control*Z^target/seedNorm ≤ Cs*control*Z^target :=
      div_le_self (mul_nonneg (mul_nonneg hCs hcontrol) (Real.rpow_nonneg hZ0.le _)) hseed
    exact add_le_add hfrac le_rfl
  have hout := hsplice Z target v height t u E (Cs+Z^(-target)*Ret) Cc control
    hZ htarget hheight hcoeff hCc hcontrol hsmall' hcoarse
  apply hout.trans_eq
  have heq : (2+4*Real.pi)^degree*(Cs+Z^(-target)*Ret+Cc)*control*Z^target =
      (2+4*Real.pi)^degree*(Cs+Cc)*control*Z^target+
        (2+4*Real.pi)^degree*Ret*control := by
    calc
      _ = (2+4*Real.pi)^degree*(Cs+Cc)*control*Z^target+
          (2+4*Real.pi)^degree*Ret*control*(Z^(-target)*Z^target) := by ring
      _ = _ := by rw [hcancel,mul_one]
  rw [heq]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_low_height_return_split

#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_low_returned_height_splice
