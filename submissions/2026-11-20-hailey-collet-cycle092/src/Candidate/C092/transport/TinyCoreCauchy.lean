/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact Cauchy split of the original retained energy, duplicating true marks. -/
import Candidate.C092.transport.TinyCoreMiddle

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentWholeSlotDeletion CenteredMomentHeckeHeight
open QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

/-- Infinite nonnegative Cauchy, derived from finite sums and real
summability. There is no new assumed estimate for either arm. -/
theorem nonnegative_tsum_cauchy {Index : Type*} (f g h : Index → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hh : ∀ i, 0 ≤ h i)
    (hsq : ∀ i, (f i)^2 ≤ g i*h i) (hgs : Summable g) (hhs : Summable h) :
    (∑' i, f i) ≤ Real.sqrt (∑' i, g i)*Real.sqrt (∑' i, h i) := by
  apply Real.tsum_le_of_sum_le hf
  intro s
  calc
    _ ≤ ∑ i ∈ s, Real.sqrt (g i)*Real.sqrt (h i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [←Real.sqrt_mul (hg i)]
      exact Real.le_sqrt_of_sq_le (hsq i)
    _ ≤ Real.sqrt (∑ i ∈ s, g i)*Real.sqrt (∑ i ∈ s, h i) := Real.sum_sqrt_mul_sqrt_le s hg hh
    _ ≤ _ := by
      gcongr
      · exact hgs.sum_le_tsum s (fun i _ => hg i)
      · exact hhs.sum_le_tsum s (fun i _ => hh i)

def duplicated {Slot : Type*} (F : Finset Slot) : Finset (Fin 2×Slot) := Finset.univ×ˢF

theorem duplicated_product {Slot : Type*} (F : Finset Slot) (f : Slot → ℂ) :
    (∏ j ∈ duplicated F, f j.2) = (∏ i ∈ F, f i)^2 := by
  simp [duplicated,Finset.prod_product,Fin.prod_univ_two,pow_two]

def ordinaryFactor (η : Character) (mask A z : O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹*rowTwistedSum η mask A z W t X

theorem selected_factor {Slot : Type*} (F : Finset Slot)
    (η : Character) (mask A z : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) :
    selectedProduct F η mask A z W₁ W₂ pool coeff P t X₁ X₂ =
      ordinaryFactor η mask A z W₁ t X₁*ordinaryFactor η mask A z W₂ t X₂*
        (∏ i ∈ F, normalizedSlot η mask A z (pool i) (coeff i) t (P i)) := by
  unfold selectedProduct ordinaryFactor
  rw [Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

/-- The two Cauchy arms are the original long ordinary squared and the
original short ordinary plus exactly two copies of each retained whole mark. -/
theorem retained_row_square {Slot : Type*} (F : Finset Slot)
    (η : Character) (mask A z : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    (‖selectedProduct F η mask A z W₁ W₂ pool coeff P t X₁ X₂‖^2)^2 =
      ‖selectedProduct (∅ : Finset Slot) η mask A z W₁ W₁ pool coeff P t X₁ X₁‖^2*
      ‖selectedProduct (duplicated F) η mask A z W₂ W₂
        (fun j => pool j.2) (fun j => coeff j.2) (fun j => P j.2) t X₂ X₂‖^2 := by
  rw [selected_factor F η mask A z t W₁ W₂ pool coeff P X₁ X₂ hX₁,
    selected_factor (∅ : Finset Slot) η mask A z t W₁ W₁ pool coeff P X₁ X₁ hX₁,
    selected_factor (duplicated F) η mask A z t W₂ W₂ _ _ _ X₂ X₂ hX₂,
    duplicated_product F (fun i => normalizedSlot η mask A z (pool i) (coeff i) t (P i))]
  simp only [Finset.prod_empty,mul_one,norm_mul,norm_pow]
  ring

/-- Authentic positive-energy Cauchy on the original same keep and mask.
Summability is inherited from the actual finite ordinary/prime polynomials. -/
theorem retained_energy_cauchy {Slot : Type*} (F : Finset Slot)
    (η : Character) (mask A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ b₁ b₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (hP : ∀ i, 0 ≤ P i) :
    subsetEnergy F η mask A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K ≤
      Real.sqrt (subsetEnergy (∅ : Finset Slot) η mask A t W₁ W₁ pool coeff P X₁ X₁ keep Φ K)*
      Real.sqrt (subsetEnergy (duplicated F) η mask A t W₂ W₂
        (fun j => pool j.2) (fun j => coeff j.2) (fun j => P j.2) X₂ X₂ keep Φ K) := by
  have hlong := subset_summable (∅ : Finset Slot) η mask A t W₁ W₁ pool coeff P X₁ X₁ b₁ b₁
    hX₁ hX₁ hs₁ hs₁ keep Φ K hK hP
  have hshort := subset_summable (duplicated F) η mask A t W₂ W₂
    (fun j => pool j.2) (fun j => coeff j.2) (fun j => P j.2) X₂ X₂ b₂ b₂
    hX₂ hX₂ hs₂ hs₂ keep Φ K hK (fun j => hP j.2)
  rw [subsetEnergy_eq_selected_tsum F η mask A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K (mul_pos hX₁ hX₂).le hP,
    subsetEnergy_eq_selected_tsum (∅ : Finset Slot) η mask A t W₁ W₁ pool coeff P X₁ X₁ keep Φ K
      (mul_pos hX₁ hX₁).le hP,
    subsetEnergy_eq_selected_tsum (duplicated F) η mask A t W₂ W₂ _ _ _ X₂ X₂ keep Φ K
      (mul_pos hX₂ hX₂).le (fun j => hP j.2)]
  apply nonnegative_tsum_cauchy
  · intro z; have hweight := hΦ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K); split_ifs <;> positivity
  · intro z; have hweight := hΦ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K); split_ifs <;> positivity
  · intro z; have hweight := hΦ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K); split_ifs <;> positivity
  · intro z
    split_ifs with hk
    · have hid := retained_row_square F η mask A z t W₁ W₂ pool coeff P X₁ X₂ hX₁ hX₂
      have he := congrArg (fun x : ℝ => x*(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re^2) hid
      nlinarith only [he]
    · norm_num
  · exact hlong
  · exact hshort

end
end QRH.Cycle092.TinyCore
