/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialHeightPlain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialProjectedDictionary
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentLattice CenteredMomentTwist HeckePrimeAnnular
open QRH.Record1252270103Restoration QRH.Record1252270103TwoIdeal
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem annular_slot_height (η : Character) (m A z : O) (t : ℝ)
    (S : Finset (Ideal O)) (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P σ v : ℝ)
    (hP : 0<P) (hS : ∀I∈S,I≠0) :
    rowSlot η m A z S (fun I=>ν I*annularWeight W P σ v I) t=
      (P:ℂ)^(Complex.I*t)*rowSlot η m A z S
        (fun I=>ν I*annularWeight W P σ (t+v) I) 0 := by
  rw [rowSlot_eq_weight,rowSlot_eq_weight,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun I hI=>annular_rowWeight_height η m A z ν W P σ v t hP I (hS I hI))

/-- Marked collisions and every zero coefficient survive the height shift. -/
theorem annular_markedSlot_height (η : Character) (m A z : O) (t : ℝ)
    (S : ι→Finset (Ideal O)) (ν : ι→Ideal O→ℂ) (W : ι→ℝ→ℂ) (P σ v : ι→ℝ)
    (hP : ∀i,0<P i) (hS : ∀i I,I∈S i→I≠0) :
    markedSlotSum η m A z t S (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (v i) I)=
      (∏i,(P i:ℂ)^(Complex.I*t))*markedSlotSum η m A z 0 S
        (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+v i) I) := by
  rw [markedSlotSum_eq_pool,markedSlotSum_eq_pool,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  have he (i : ι) := annular_rowWeight_height η m A z (ν i) (W i) (P i) (σ i) (v i) t
    (hP i) (f i) (hS i (f i) (Fintype.mem_piFinset.mp hf i))
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  ring

variable (η : Character) (m A z : O) (t : ℝ)
variable (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
variable (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
variable (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
variable (S : ι→Finset (Ideal O)) (ν : ι→Ideal O→ℂ) (W : ι→ℝ→ℂ) (P σ v : ι→ℝ)
variable (hP : ∀i,0<P i) (hS : ∀i I,I∈S i→I≠0)
variable (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)

include hP hS hX₁ hX₂

/-- Exact common phase for the squarefree initial row, with the fixed hole retained. -/
theorem squarefreePositiveSlotRow_height :
    squarefreePositiveSlotRow η m A z W₁ W₂ b S
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (v i) I) P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t)*(∏i,(P i:ℂ)^(Complex.I*t)))*
        squarefreePositiveSlotRow η m A z
          (normPowerProfile W₁ a b ha hs₁ hW₁ t) (normPowerProfile W₂ a b ha hs₂ hW₂ t) b S
          (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+v i) I) P 0 X₁ X₂ := by
  unfold squarefreePositiveSlotRow
  rw [squarefreePlainSum_height η m A z t W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ X₁ X₂ hX₁ hX₂]
  simp_rw [annular_slot_height η m A z t _ _ _ _ _ _ (hP _) (hS _)]
  rw [Finset.prod_mul_distrib]
  ring

theorem markedPositiveRow_height :
    markedPositiveRow η m A z W₁ W₂ b S
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (v i) I) P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t)*(∏i,(P i:ℂ)^(Complex.I*t)))*
        markedPositiveRow η m A z
          (normPowerProfile W₁ a b ha hs₁ hW₁ t) (normPowerProfile W₂ a b ha hs₂ hW₂ t) b S
          (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+v i) I) P 0 X₁ X₂ := by
  unfold markedPositiveRow
  rw [squarefreePlainSum_height η m A z t W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ X₁ X₂ hX₁ hX₂,
    annular_markedSlot_height η m A z t S ν W P σ v hP hS]
  ring

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.annular_markedSlot_height
#print axioms QRH.Record1252270103Low.squarefreePositiveSlotRow_height
#print axioms QRH.Record1252270103Low.markedPositiveRow_height
