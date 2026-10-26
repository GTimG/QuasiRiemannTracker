/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.HolePositive

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentPositiveSummability
open CenteredMomentAbsoluteEnergy Record1252270103KernelMass
local notation "O" => HeckeFamily.O

def holeDeletionMass : ℝ := ∑D∈mobiusPool,(Real.sqrt (pairNorm (mobiusPair D)))⁻¹

theorem holeDeletionMass_nonneg : 0≤holeDeletionMass :=
  Finset.sum_nonneg (fun D _=>inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem ordinary_finite_energy_le {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (R : Finset O) :
    (∑z∈R,‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)) ≤
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  obtain ⟨B,hB⟩ := product_bounded η m A t (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b b X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hs := bounded_radial_summable (fun z=>positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
    B hB keep Φ K hK
  unfold energy
  simp_rw [mul_ite,mul_zero]
  exact hs.sum_le_tsum R (fun z _=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl)

theorem hole_energy_transfer {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (E : ℝ)
    (hE : ∀D∈mobiusPool,energy η m A t W₁ W₂ S β P
      (X₁/Ideal.absNorm (mobiusPair D).1) (X₂/Ideal.absNorm (mobiusPair D).2) keep Φ K ≤ E) :
    ordinaryHoleEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ K ≤ holeDeletionMass^2*E := by
  let w := fun D : Finset PrimeIdeal×Finset PrimeIdeal=>(Real.sqrt (pairNorm (mobiusPair D)))⁻¹
  let c := fun (D : Finset PrimeIdeal×Finset PrimeIdeal) (z : O)=>
    mobiusSign D*rowWeight η m A z t ((mobiusPair D).1*(mobiusPair D).2)/(Real.sqrt (pairNorm (mobiusPair D)):ℂ)
  let f := fun (D : Finset PrimeIdeal×Finset PrimeIdeal) (z : O)=>positiveSlotRow η m A z W₁ W₂ S β P t
    (X₁/Ideal.absNorm (mobiusPair D).1) (X₂/Ideal.absNorm (mobiusPair D).2)
  let u := fun z : O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hw : ∀D∈mobiusPool,0≤w D := fun D _=>inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hu : ∀z,0≤u z := by intro z;dsimp [u];split_ifs;exact hΦ _;exact le_rfl
  have hc : ∀D∈mobiusPool,∀z,‖c D z‖≤w D := by
    intro D hD z
    dsimp [c,w,mobiusSign]
    rw [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_div_of_nonneg_right (rowWeight_norm_le_one_all η m A z t _) (Real.sqrt_nonneg _)).trans_eq (one_div _)
  have he : ∀D∈mobiusPool,∀R : Finset O,∑z∈R,‖f D z‖^2*u z≤E := by
    intro D hD R
    have hi := shorten_positive hX₁ (subsetProduct_nonzero D.1)
    have hj := shorten_positive hX₂ (subsetProduct_nonzero D.2)
    exact (ordinary_finite_energy_le η m A W₁ W₂ b hs₁ hs₂ S β P t _ _ hi.1 hj.1 keep Φ K hK hΦ R).trans (hE D hD)
  have h := Record1252270103Source.weighted_sum_energy_le_uniform mobiusPool w E c f u hw hu hc he
  change _ ≤ holeDeletionMass^2*E at h
  apply le_trans (le_of_eq ?_) h
  unfold ordinaryHoleEnergy
  apply tsum_congr
  intro z
  rw [hole_positive_row η m A z W₁ W₂ b hs₁ hs₂ S β P hP t X₁ X₂ hX₁ hX₂]
  dsimp [c,f,u]
  split_ifs <;> simp

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.hole_energy_transfer
