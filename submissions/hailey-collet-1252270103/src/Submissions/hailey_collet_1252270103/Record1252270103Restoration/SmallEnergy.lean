/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.SmallRows

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability CenteredMomentInductionEnergy
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem ordinary_hole_plain_norm (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    ‖ordinaryHolePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂‖ ≤
      ∑ n ∈ holePairPool b X₁ X₂, ‖pairProfile W₁ W₂ X₁ X₂ n‖ := by
  unfold ordinaryHolePlainSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t _)

theorem ordinary_hole_row_bounded {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    ∃ B : ℝ, ∀ z : O, ‖ordinaryHolePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂‖ ≤ B := by
  refine ⟨‖(Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹‖ *
    ((∑n∈holePairPool b X₁ X₂,‖pairProfile W₁ W₂ X₁ X₂ n‖)*
      ∏i,∑I∈S i,‖β i I‖),?_⟩
  intro z
  unfold ordinaryHolePositiveSlotRow
  rw [norm_mul,norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact ordinary_hole_plain_norm η m A z t W₁ W₂ b X₁ X₂
  · exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      (fun i _=>slot_finite_norm η m A z t (S i) (β i))
  · positivity
  · positivity

theorem ordinary_hole_energy_summable {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O=>if keep z then
      ‖ordinaryHolePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB⟩ := ordinary_hole_row_bounded η m A W₁ W₂ b S β P t X₁ X₂
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem ordinary_hole_finite_energy_le {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (R : Finset O) :
    (∑z∈R,‖ordinaryHolePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂‖^2*
      (if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)) ≤
    ordinaryHoleEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ K := by
  have hs := ordinary_hole_energy_summable η m A W₁ W₂ b S β P t X₁ X₂ keep Φ K hK
  unfold ordinaryHoleEnergy
  simp_rw [mul_ite,mul_zero]
  exact hs.sum_le_tsum R (fun z _=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl)
theorem small_mass_bound (b X₁ X₂ : ℝ) :
    (∑d∈smallPool (plainPairPool b X₁ X₂),(Real.sqrt (pairNorm d))⁻¹) ≤
      ordinaryPrimeMassBound smallPrimes := by
  apply le_trans (le_of_eq ?_) (ordinary_supported_finite_mass smallPrimes
    (smallPool (plainPairPool b X₁ X₂)) (fun d hd=>smallPool_nonzero hd)
      (fun d hd=>smallPool_support hd))
  apply Finset.sum_congr rfl
  intro d hd
  have hdn := smallPool_nonzero hd
  have hi : 0≤(Ideal.absNorm d.1:ℝ) := Nat.cast_nonneg _
  have hj : 0≤(Ideal.absNorm d.2:ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_eq_rpow,←Real.rpow_neg (pairNorm_pos hdn.1 hdn.2).le]
  unfold pairNorm normWeight
  rw [Real.mul_rpow hi hj]

theorem small_energy_transfer {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (E : ℝ) (hEn : 0≤E)
    (hE : ∀d∈smallPool (plainPairPool b X₁ X₂),
      ordinaryHoleEnergy η m A t W₁ W₂ b S β P
        (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) keep Φ K ≤ E) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≤
      (ordinaryPrimeMassBound smallPrimes)^2*E := by
  let D := smallPool (plainPairPool b X₁ X₂)
  let w := fun d : IdealPair=>(Real.sqrt (pairNorm d))⁻¹
  let c := fun (d : IdealPair) (z : O)=>rowWeight η m A z t (d.1*d.2)/(Real.sqrt (pairNorm d):ℂ)
  let f := fun (d : IdealPair) (z : O)=> ordinaryHolePositiveSlotRow η m A z W₁ W₂ b S β P t
    (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)
  let u := fun z : O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hw : ∀d∈D,0≤w d := fun d _=>inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hu : ∀z,0≤u z := by intro z;dsimp [u];split_ifs;exact hΦ _;exact le_rfl
  have hc : ∀d∈D,∀z,‖c d z‖≤w d := by
    intro d hd z
    dsimp [c,w]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_div_of_nonneg_right (rowWeight_norm_le_one_all η m A z t _) (Real.sqrt_nonneg _)).trans_eq (one_div _)
  have he : ∀d∈D,∀R : Finset O,∑z∈R,‖f d z‖^2*u z≤E := by
    intro d hd R
    exact (ordinary_hole_finite_energy_le η m A W₁ W₂ b S β P t _ _ keep Φ K hK hΦ R).trans (hE d hd)
  have h := Record1252270103Source.weighted_sum_energy_le_uniform D w E c f u hw hu hc he
  have hre : energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K =
      ∑'z,‖∑d∈D,c d z*f d z‖^2*u z := by
    unfold energy
    apply tsum_congr
    intro z
    rw [small_positive_row η m A z W₁ W₂ b hs₁ hs₂ S β P hP t X₁ X₂ hX₁ hX₂]
    dsimp [c,f,u,D]
    split_ifs <;> simp
  rw [hre]
  apply h.trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg hw) (small_mass_bound b X₁ X₂) 2) hEn

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.small_energy_transfer
