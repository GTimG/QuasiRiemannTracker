/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Height transport for the actual squarefree energy and marked finite norm. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialHeightSlots
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentLattice CenteredMomentTwist HeckePrimeAnnular
open QRH.Record1252270103Restoration
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]
variable (η : Character) (m A : O) (t : ℝ)
variable (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
variable (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
variable (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
variable (S : ι→Finset (Ideal O)) (ν : ι→Ideal O→ℂ) (W : ι→ℝ→ℂ) (P σ v : ι→ℝ)
variable (hP : ∀i,0<P i) (hS : ∀i I,I∈S i→I≠0)
variable (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
include hP hS hX₁ hX₂

lemma squarefree_row_height_norm (z : O) :
    ‖squarefreePositiveSlotRow η m A z W₁ W₂ b S
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (v i) I) P t X₁ X₂‖=
    ‖squarefreePositiveSlotRow η m A z
      (normPowerProfile W₁ a b ha hs₁ hW₁ t) (normPowerProfile W₂ a b ha hs₂ hW₂ t) b S
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+v i) I) P 0 X₁ X₂‖ := by
  rw [squarefreePositiveSlotRow_height η m A z t W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂
    S ν W P σ v hP hS X₁ X₂ hX₁ hX₂]
  simp only [norm_mul,norm_prod,norm_real_imaginary_power X₁ t hX₁,
    norm_real_imaginary_power X₂ t hX₂,norm_real_imaginary_power _ t (hP _),
    Finset.prod_const_one,one_mul]

lemma marked_row_height_norm (z : O) :
    ‖markedPositiveRow η m A z W₁ W₂ b S
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (v i) I) P t X₁ X₂‖=
    ‖markedPositiveRow η m A z
      (normPowerProfile W₁ a b ha hs₁ hW₁ t) (normPowerProfile W₂ a b ha hs₂ hW₂ t) b S
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+v i) I) P 0 X₁ X₂‖ := by
  rw [markedPositiveRow_height η m A z t W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂
    S ν W P σ v hP hS X₁ X₂ hX₁ hX₂]
  simp only [norm_mul,norm_prod,norm_real_imaginary_power X₁ t hX₁,
    norm_real_imaginary_power X₂ t hX₂,norm_real_imaginary_power _ t (hP _),
    Finset.prod_const_one,one_mul]

/-- Same character, element mask, keep predicate and radial weight, at every
positive pair of raw scales. Only exact norm phases have been removed. -/
theorem squarefreeEnergy_height (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    squarefreeEnergy η m A t W₁ W₂ b S
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (v i) I) P X₁ X₂ keep Φ K=
    squarefreeEnergy η m A 0
      (normPowerProfile W₁ a b ha hs₁ hW₁ t) (normPowerProfile W₂ a b ha hs₂ hW₂ t) b S
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+v i) I) P X₁ X₂ keep Φ K := by
  unfold squarefreeEnergy
  apply tsum_congr
  intro z
  rw [squarefree_row_height_norm η m A t W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂
    S ν W P σ v hP hS X₁ X₂ hX₁ hX₂ z]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.squarefreeEnergy_height
#print axioms QRH.Record1252270103Low.marked_row_height_norm
