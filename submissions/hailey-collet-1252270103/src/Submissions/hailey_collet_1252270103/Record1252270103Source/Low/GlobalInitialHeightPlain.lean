/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact height transport through the original ordinary squarefree/small-prime hole. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialProjectedRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.SlotHeight
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentLattice CenteredMomentTwist CenteredMomentEnergySlotHeight
open HeckePrimeAnnular CenteredMomentCommonMaskEnergy
open QRH.Record1252270103Restoration
local notation "O"=>HeckeFamily.O

lemma rowWeight_height (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I=rowWeight η m A z 0 I*(I.absNorm:ℂ)^(Complex.I*t) := by
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,Complex.ofReal_zero,
    mul_zero,Complex.cpow_zero,mul_one]

lemma rowWeight_profile_height (η : Character) (m A z : O) (t : ℝ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) (I : Ideal O) :
    rowWeight η m A z t I*W ((I.absNorm:ℝ)/X)=
      (X:ℂ)^(Complex.I*t)*rowWeight η m A z 0 I*
        normPowerProfile W a b ha hs hW t ((I.absNorm:ℝ)/X) := by
  have hphase : (I.absNorm:ℂ)^(Complex.I*t)=
      (X:ℂ)^(Complex.I*t)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(Complex.I*t) := by
    have h:=Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg I.absNorm) hX.le) (Complex.I*t)
    have he : X*((I.absNorm:ℝ)/X)=(I.absNorm:ℝ) := by field_simp
    rw [←Complex.ofReal_mul,he,Complex.ofReal_natCast] at h
    exact h
  rw [rowWeight_height,hphase,normPowerProfile_apply]
  ring

/-- Both projectors are unchanged term by term; no coefficient norm comparison. -/
theorem squarefreePlainSum_height (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        squarefreePlainSum (rowWeight η m A z 0)
          (normPowerProfile W₁ a b ha hs₁ hW₁ t)
          (normPowerProfile W₂ a b ha hs₂ hW₂ t) b X₁ X₂ := by
  unfold squarefreePlainSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hh : ordinarySmallHole n.1 n.2
  · simp only [hh,ite_true,map_mul]
    have h₁:=rowWeight_profile_height η m A z t W₁ a b ha hs₁ hW₁ X₁ hX₁ n.1
    have h₂:=rowWeight_profile_height η m A z t W₂ a b ha hs₂ hW₂ X₂ hX₂ n.2
    calc
      _ = (QRH.Record1252270103KernelMass.squarefreeIndicator (n.1*n.2):ℂ)*
          (rowWeight η m A z t n.1*W₁ ((n.1.absNorm:ℝ)/X₁))*
          (rowWeight η m A z t n.2*W₂ ((n.2.absNorm:ℝ)/X₂)) := by ring
      _ = _ := by rw [h₁,h₂];ring
  · simp only [hh,ite_false,mul_zero]

lemma annular_rowWeight_height (η : Character) (m A z : O)
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P σ v t : ℝ) (hP : 0<P)
    (I : Ideal O) (hI : I≠0) :
    (ν I*annularWeight W P σ v I)*rowWeight η m A z t I=
      (P:ℂ)^(Complex.I*t)*
        ((ν I*annularWeight W P σ (t+v) I)*rowWeight η m A z 0 I) := by
  have h:=height_coefficient ν W P σ v t hP I hI
  change (ν I*annularWeight W P σ v I)*(I.absNorm:ℂ)^(Complex.I*t)=_ at h
  rw [rowWeight_height]
  calc
    _ = ((ν I*annularWeight W P σ v I)*(I.absNorm:ℂ)^(Complex.I*t))*
      rowWeight η m A z 0 I := by ring
    _ = _ := by rw [h];ring

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.squarefreePlainSum_height
#print axioms QRH.Record1252270103Low.annular_rowWeight_height
