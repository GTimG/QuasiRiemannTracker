/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Remove each arm's OWN outside norm phase before installing a reference.
The native convention is NI^(+I*t), profile x^(+I*t), outside X^(+I*t). -/
import Candidate.C092.transport.ReferenceShortP3Root

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairPhase
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight CenteredMomentHeckeExpansion
open CenteredMomentLattice CenteredMomentTwist
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.ReferenceShortP3
local notation "O" => HeckeFamily.O

/-- Exact original positive height convention, before taking a norm. -/
theorem rowWeight_height (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A z 0 I*(I.absNorm:ℂ)^(Complex.I*t) := by
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,Complex.ofReal_zero,
    mul_zero,Complex.cpow_zero,mul_one]

theorem rowWeight_profile_height (η : Character) (m A z : O) (t : ℝ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    rowWeight η m A z t I*W ((I.absNorm:ℝ)/X) =
      (X:ℂ)^(Complex.I*t)*rowWeight η m A z 0 I*
        normPowerProfile W a b ha hs hW t ((I.absNorm:ℝ)/X) := by
  have hphase : (I.absNorm:ℂ)^(Complex.I*t) =
      (X:ℂ)^(Complex.I*t)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(Complex.I*t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg I.absNorm) hX.le) (Complex.I*t)
    have he : X*((I.absNorm:ℝ)/X) = (I.absNorm:ℝ) := by field_simp
    rw [←Complex.ofReal_mul,he,Complex.ofReal_natCast] at h
    exact h
  rw [rowWeight_height,hphase,normPowerProfile_apply]
  ring

/-- The exact complex column identity: divide by X^(+I*t), not its inverse
sign, to obtain the native normPowerProfile at height zero. -/
theorem original_height_profile (η : Character) (m A z : O) (t : ℝ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    original η m A z W t X = (X:ℂ)^(Complex.I*t)*
      original η m A z (normPowerProfile W a b ha hs hW t) 0 X := by
  have ht : rowTwistedSum η m A z W t X = (X:ℂ)^(Complex.I*t)*
      rowTwistedSum η m A z (normPowerProfile W a b ha hs hW t) 0 X := by
    rw [rowTwistedSum_eq_weight,rowTwistedSum_eq_weight,←tsum_mul_left]
    apply tsum_congr
    intro I
    rw [rowWeight_profile_height η m A z t W a b ha hs hW X hX I]
    ring
  unfold original
  rw [ht]
  ring

def outsidePhase (t₁ t₂ X₁ X₂ : ℝ) : ℂ :=
  (X₁:ℂ)^(Complex.I*t₁)*(X₂:ℂ)^(Complex.I*t₂)

theorem outsidePhase_norm (t₁ t₂ : ℝ) {X₁ X₂ : ℝ} (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ‖outsidePhase t₁ t₂ X₁ X₂‖ = 1 := by
  rw [outsidePhase,norm_mul,norm_real_imaginary_power X₁ t₁ hX₁,
    norm_real_imaginary_power X₂ t₂ hX₂,one_mul]

theorem outsidePhase_ne_zero (t₁ t₂ : ℝ) {X₁ X₂ : ℝ} (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    outsidePhase t₁ t₂ X₁ X₂ ≠ 0 := by
  intro hz
  have hn := outsidePhase_norm t₁ t₂ hX₁ hX₂
  rw [hz,norm_zero] at hn
  norm_num at hn

def alignedRowOn {ι : Type} (T : Finset ι) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : ι→FreeRow→ℂ) (u : FreeRow) : ℂ :=
  (outsidePhase t₁ t₂ X₁ X₂)⁻¹*pairRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark u

def alignedPairOn {ι : Type} (T : Finset ι) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ) (mark : ι→FreeRow→ℂ) (u : FreeRow) : ℂ :=
  alignedRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark u -
    alignedRowOn T η₁ η₂ W₁ W₂ t₁ t₂ Y₁ Y₂ mark u

def alignedPairEnergyOn {ι : Type} (T : Finset ι) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (mark : ι→FreeRow→ℂ) : ℝ :=
  ∑ u∈s,‖alignedPairOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark u‖^2

theorem alignedRow_norm {ι : Type} (T : Finset ι) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : ι→FreeRow→ℂ) (u : FreeRow)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ‖alignedRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark u‖ =
      ‖pairRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark u‖ := by
  rw [alignedRowOn,norm_mul,norm_inv,outsidePhase_norm t₁ t₂ hX₁ hX₂,inv_one,one_mul]

theorem alignedRow_energy {ι : Type} [Fintype ι] (T : Finset ι) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ)
    (mark : ι→FreeRow→ℂ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    (∑ u∈s,‖alignedRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark u‖^2) =
      finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  simp_rw [alignedRow_norm T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark _ hX₁ hX₂]
  exact pairRow_energy T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark

/-- Uncentered original energy and the TRUE short-reference bound are
unchanged. The signed difference compares individually phase-aligned arms. -/
theorem phase_root_triangle {ι : Type} [Fintype ι] (T : Finset ι) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (mark : ι→FreeRow→ℂ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (_hprod : Y₁*Y₂ = X₁*X₂) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      2*alignedPairEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark +
      2*finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ Y₁ Y₂ mark := by
  have h := finite_uncentered_of_centered s
    (alignedRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark)
    (alignedRowOn T η₁ η₂ W₁ W₂ t₁ t₂ Y₁ Y₂ mark) (le_refl _) (le_refl _)
  rw [alignedRow_energy T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark hX₁ hX₂,
    alignedRow_energy T s η₁ η₂ W₁ W₂ t₁ t₂ Y₁ Y₂ mark hY₁ hY₂] at h
  exact h

/-- Exact native profile dictionary for each entire aligned arm. No equality
between different X/Y outside phases is asserted or needed. -/
theorem alignedRow_eq_profile {ι : Type} (T : Finset ι) (η₁ η₂ : Character)
    (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : ι→FreeRow→ℂ) (u : FreeRow)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    alignedRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark u =
      pairRowOn T η₁ η₂ (normPowerProfile W₁ a b ha hs₁ hW₁ t₁)
        (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) 0 0 X₁ X₂ mark u := by
  unfold alignedRowOn pairRowOn
  rw [original_height_profile η₁ _ _ _ t₁ W₁ a b ha hs₁ hW₁ X₁ hX₁,
    original_height_profile η₂ _ _ _ t₂ W₂ a b ha hs₂ hW₂ X₂ hX₂]
  have hn := outsidePhase_ne_zero t₁ t₂ hX₁ hX₂
  unfold outsidePhase at hn ⊢
  have h₁ := (mul_ne_zero_iff.mp hn).1
  have h₂ := (mul_ne_zero_iff.mp hn).2
  field_simp [h₁,h₂]
  <;> ring

#print axioms original_height_profile
#print axioms phase_root_triangle
#print axioms alignedRow_eq_profile
end
end QRH.Cycle092.OrderedPairPhase
