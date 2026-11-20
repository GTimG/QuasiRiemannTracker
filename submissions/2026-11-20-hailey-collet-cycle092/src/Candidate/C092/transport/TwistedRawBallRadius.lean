/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual retained first child radii satisfy the original second-Q range. -/
import Candidate.C092.transport.TwistedRawBallGeometry
set_option autoImplicit false
namespace QRH.Cycle092.TwistedRawBall
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedFirstRetainedFixed MixedFirstCutoffs MixedFirstActualBandGeometry
open MixedFirstExceptionalWindow MixedInnerExceptionalBlock
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

theorem actual_child_Q_range (s : Source ι a b) (C D : Id)
    (E : Finset (CommonIndex C D)) (cRad Z ξ κ H : ℝ)
    (hcRad : 1 ≤ cRad) (hZ : 2 ≤ Z) (hpad : 2 ≤ Z^κ)
    (hsmall : ξ/2+κ ≤ 22) (hvol : sourceVolume s ≤ Z^(8:ℝ))
    (n : Blocks (effectiveScale C D E (cRad*Z)) (firstRadius s C D E (cRad*Z) Z ξ)
      (H/C.absNorm) (H/D.absNorm)) (hdy : 1/2 ≤ dyadicScale (n 1)) :
    1/2 ≤ childScale Z κ (n 1) ∧ childScale Z κ (n 1) ≤ Z^(40:ℝ) := by
  have hZ1 : 1 < Z := by linarith
  have hz : 0 < Z := by linarith
  have hK1 : 1 ≤ cRad*Z := one_le_mul_of_one_le_of_one_le hcRad hZ1.le
  have hK : 0 < cRad*Z := zero_lt_one.trans_le hK1
  have hlive := childScale_live Z κ hZ1 hpad (n 1) hdy
  refine ⟨(by linarith [hlive.1]),?_⟩
  have hc : firstCutoff C D E (cRad*Z) (sourceVolume s) ≤ Z^(16:ℝ) := by
    calc
      _ ≤ (sourceVolume s)^2/(cRad*Z) := firstCutoff_upper C D E _ _ hK
      _ ≤ (sourceVolume s)^2 := div_le_self (sq_nonneg _) hK1
      _ ≤ (Z^(8:ℝ))^2 := pow_le_pow_left₀ (sourceVolume_pos s).le hvol 2
      _ = _ := by rw [←Real.rpow_mul_natCast hz.le]; norm_num
  have hn := retained_scale_le _ (n 1 : ℤ)
    (block_retained (effectiveScale C D E (cRad*Z)) (firstRadius s C D E (cRad*Z) Z ξ)
      (H/C.absNorm) (H/D.absNorm) n)
  simp only [actual_radius_eq,frequencyRadius] at hn
  have he : childScale Z κ (n 1)=dyadicScale (n 1)*Z^κ := by
    unfold childScale
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ1.ne' (dyadicScale_pos _)]
  have h4 : (4:ℝ) ≤ Z^(2:ℝ) := by rw [Real.rpow_two];nlinarith
  calc
    _ = dyadicScale (n 1)*Z^κ := he
    _ ≤ (4*(Z^(16:ℝ)*Z^(ξ/2)))*Z^κ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact hn.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hz.le _)) (by norm_num))
    _ ≤ (Z^(2:ℝ)*(Z^(16:ℝ)*Z^(ξ/2)))*Z^κ := by gcongr
    _ = Z^(18+ξ/2+κ) := by rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)

#print axioms actual_child_Q_range
end
end QRH.Cycle092.TwistedRawBall
