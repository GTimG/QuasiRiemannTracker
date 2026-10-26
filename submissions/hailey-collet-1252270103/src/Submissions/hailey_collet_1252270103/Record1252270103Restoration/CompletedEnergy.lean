/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.InverseRows
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.WeightedEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem squarefree_plain_norm (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    ‖squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂‖ ≤
      ∑ n ∈ holePairPool b X₁ X₂, ‖pairProfile W₁ W₂ X₁ X₂ n‖ := by
  rw [squarefreePlainSum_eq_hole_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul,norm_mul]
  have hs : ‖(squarefreeIndicator (n.1*n.2):ℂ)‖ ≤ 1 := by
    unfold squarefreeIndicator
    split_ifs <;> norm_num
  have hw := rowWeight_norm_le_one_all η m A z t (n.1*n.2)
  exact mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) hs).trans hw)

theorem squarefree_row_bounded {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    ∃ B : ℝ, ∀ z : O, ‖squarefreePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂‖ ≤ B := by
  refine ⟨‖(Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹‖ *
    ((∑n∈holePairPool b X₁ X₂,‖pairProfile W₁ W₂ X₁ X₂ n‖)*
      ∏i,∑I∈S i,‖β i I‖),?_⟩
  intro z
  unfold squarefreePositiveSlotRow
  rw [norm_mul,norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact squarefree_plain_norm η m A z t W₁ W₂ b X₁ X₂
  · exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      (fun i _=>slot_finite_norm η m A z t (S i) (β i))
  · positivity
  · positivity

theorem squarefree_energy_summable {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O=>if keep z then
      ‖squarefreePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB⟩ := squarefree_row_bounded η m A W₁ W₂ b S β P t X₁ X₂
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem squarefree_finite_energy_le {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (R : Finset O) :
    (∑z∈R,‖squarefreePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂‖^2*
      (if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)) ≤
    squarefreeEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ K := by
  have hs := squarefree_energy_summable η m A W₁ W₂ b S β P t X₁ X₂ keep Φ K hK
  unfold squarefreeEnergy
  simp_rw [mul_ite,mul_zero]
  exact hs.sum_le_tsum R (fun z _=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl)

def inverseDivisorMass (b X₁ X₂ : ℝ) : ℝ :=
  ∑d∈divisorPool (holePairPool b X₁ X₂), |(inverseKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d)

theorem inverse_hole_energy_transfer {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (E : ℝ)
    (hE : ∀d∈divisorPool (holePairPool b X₁ X₂),
      squarefreeEnergy η m A t W₁ W₂ b S β P
        (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) keep Φ K ≤ E) :
    ordinaryHoleEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ K ≤
      (inverseDivisorMass b X₁ X₂)^2*E := by
  let D := divisorPool (holePairPool b X₁ X₂)
  let w := fun d : IdealPair=>|(inverseKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d)
  let c := fun (d : IdealPair) (z : O)=>
    (inverseKernel d.1 d.2:ℂ)*rowWeight η m A z t (d.1*d.2)/(Real.sqrt (pairNorm d):ℂ)
  let f := fun (d : IdealPair) (z : O)=> squarefreePositiveSlotRow η m A z W₁ W₂ b S β P t
    (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)
  let u := fun z : O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hw : ∀d∈D,0≤w d := fun d _=>div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hu : ∀z,0≤u z := by intro z;dsimp [u];split_ifs;exact hΦ _;exact le_rfl
  have hc : ∀d∈D,∀z,‖c d z‖≤w d := by
    intro d hd z
    dsimp [c,w]
    rw [norm_div,norm_mul,Complex.norm_intCast,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (rowWeight_norm_le_one_all η m A z t _))
      (Real.sqrt_nonneg _)
  have he : ∀d∈D,∀R : Finset O,∑z∈R,‖f d z‖^2*u z≤E := by
    intro d hd R
    exact (squarefree_finite_energy_le η m A W₁ W₂ b S β P t _ _ keep Φ K hK hΦ R).trans (hE d hd)
  have h := Record1252270103Source.weighted_sum_energy_le_uniform D w E c f u hw hu hc he
  change _ ≤ (inverseDivisorMass b X₁ X₂)^2*E at h
  apply le_trans (le_of_eq ?_) h
  unfold ordinaryHoleEnergy
  apply tsum_congr
  intro z
  rw [inverse_hole_positive_row η m A z W₁ W₂ b S β P hP t X₁ X₂ hX₁ hX₂]
  dsimp [c,f,u,D]
  split_ifs <;> simp

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.inverse_hole_energy_transfer
