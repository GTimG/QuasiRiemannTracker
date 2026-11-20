/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Uses Sil's whole-slot greedy selection and the OpenAI normalized marked product. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.C092.transport.NativeStrip
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotNormalization

set_option autoImplicit false
namespace QRH.Cycle092.WholeSlot
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentHeckeHeight
open CenteredMomentWholeSlotDeletion CenteredMomentSlotNormalization
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability ConcreteTraceCRT
local notation "O" => HeckeFamily.O

/- The finite greedy proof below is Sil's Apache-2.0 proof from
`MarkedAnchor/Inverse/Select/Choice.lean`, SHA256
923eb43ef8f3604e2f5e9155bfee50f7ef2f73237eaf21eba96ccae188a39820.
That supplied module has an unavailable `Mathlib.Basic.Real.Basic` import;
the proof is checked here against the installed, pinned imports. -/
private theorem greedy_selection {σ : Type*} [DecidableEq σ] (w : σ → ℝ) (mesh : ℝ)
    (J : Finset σ) (hw : ∀ i ∈ J, 0 ≤ w i) (hmesh : ∀ i ∈ J, w i ≤ mesh) (u : ℝ) (hu : 0 ≤ u) :
    ∃ R ⊆ J, (∑ i ∈ R, w i) ≤ u ∧ (u-mesh ≤ ∑ i ∈ R, w i ∨ R = J) := by
  induction J using Finset.induction_on with
  | empty => exact ⟨∅,le_rfl,by simpa using hu,Or.inr rfl⟩
  | insert a J ha ih =>
    have hw' : ∀ i ∈ J, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hm' : ∀ i ∈ J, w i ≤ mesh := fun i hi => hmesh i (Finset.mem_insert_of_mem hi)
    obtain ⟨R,hRJ,hRu,hR⟩ := ih hw' hm'
    rcases hR with hR | rfl
    · exact ⟨R,hRJ.trans (Finset.subset_insert a J),hRu,Or.inl hR⟩
    · by_cases hfit : (∑ i ∈ R, w i)+w a ≤ u
      · refine ⟨insert a R,le_rfl,?_,Or.inr rfl⟩
        rw [Finset.sum_insert ha]
        linarith
      · have hfit' := lt_of_not_ge hfit
        have hwa := hmesh a (Finset.mem_insert_self a R)
        exact ⟨R,Finset.subset_insert a R,hRu,Or.inl (by linarith)⟩

/-- Selection depends only on the original width descriptor and its target.
If the available width is exhausted, every whole slot is retained. -/
theorem select_before_rows {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (w : Slot → ℝ) (mesh target : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ i, w i ≤ mesh) (_hmesh : 0 ≤ mesh) (htarget : 0 ≤ target) :
    ∃ F : Finset Slot, (∑ i ∈ F, w i) ≤ target ∧
      (∑ i ∈ Finset.univ \ F, w i) ≤ max 0 ((∑ i, w i)-target+mesh) ∧
      ((∑ i, w i) ≤ target → F = Finset.univ) := by
  by_cases htotal : (∑ i, w i) ≤ target
  · refine ⟨Finset.univ,htotal,?_,fun _ => rfl⟩
    simp only [Finset.sdiff_self,Finset.sum_empty]
    exact le_max_left _ _
  · obtain ⟨F,hF,hhi,hnear⟩ := greedy_selection w mesh
      Finset.univ (fun i _ => hw i) (fun i _ => hm i) target htarget
    have hlo : target-mesh ≤ ∑ i ∈ F, w i := by
      rcases hnear with h | h
      · exact h
      · subst F
        exact False.elim (htotal hhi)
    refine ⟨F,hhi,?_,fun h => False.elim (htotal h)⟩
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
    exact le_max_of_le_right (by linarith)

/-- The actual positive energy with precisely the retained original slots.
Pools, coefficients, scales, mask, ordinary factors and keep are unchanged. -/
def subsetEnergy {Slot : Type*} (F : Finset Slot)
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  energy η m A t W₁ W₂ (fun i : F => pool i.val) (fun i : F => coeff i.val)
    (fun i : F => P i.val) X₁ X₂ keep Φ K

/-- Restricting the normalized whole-slot product changes only its finite
index set, and equals the source's exact normalized positive row. -/
theorem selectedProduct_eq_subset_row {Slot : Type*} (F : Finset Slot)
    (η : Character) (m A z : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ : ℝ) (hX : 0 ≤ X₁*X₂) (hP : ∀ i, 0 ≤ P i) :
    selectedProduct F η m A z W₁ W₂ pool coeff P t X₁ X₂ =
      positiveSlotRow η m A z W₁ W₂ (fun i : F => pool i.val)
        (fun i : F => coeff i.val) (fun i : F => P i.val) t X₁ X₂ := by
  rw [←selectedProduct_univ η m A z W₁ W₂ (fun i : F => pool i.val)
    (fun i : F => coeff i.val) (fun i : F => P i.val) t X₁ X₂ hX (fun i => hP i.val)]
  unfold selectedProduct
  congr 1
  exact (Finset.prod_coe_sort F (fun i => normalizedSlot η m A z (pool i) (coeff i) t (P i))).symm

/-- Exact tsum representation; in particular no new row family or Fourier
summand is introduced by retaining whole slots. -/
theorem subsetEnergy_eq_selected_tsum {Slot : Type*} (F : Finset Slot)
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hX : 0 ≤ X₁*X₂) (hP : ∀ i, 0 ≤ P i) :
    subsetEnergy F η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K =
      ∑' z : O, if keep z then ‖selectedProduct F η m A z W₁ W₂ pool coeff P t X₁ X₂‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
  unfold subsetEnergy energy
  apply tsum_congr
  intro z
  rw [selectedProduct_eq_subset_row F η m A z t W₁ W₂ pool coeff P X₁ X₂ hX hP]

/-- The exact finite full product recovers the original source energy. -/
theorem subsetEnergy_univ {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hX : 0 ≤ X₁*X₂) (hP : ∀ i, 0 ≤ P i) :
    subsetEnergy Finset.univ η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K =
      energy η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K := by
  rw [subsetEnergy_eq_selected_tsum Finset.univ η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K hX hP]
  unfold energy
  apply tsum_congr
  intro z
  rw [selectedProduct_univ η m A z W₁ W₂ pool coeff P t X₁ X₂ hX hP]

/-- The genuine low-response class, measured on the original normalized
whole slots and their original coefficients and mask. -/
def LowRows {Slot : Type*} (J : Finset Slot) (η : Character) (m A : O) (t U e pay : ℝ)
    (w : Slot → ℝ) (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ)
    (P : Slot → ℝ) (z : O) : Prop :=
  ∀ i ∈ J, ‖normalizedSlot η m A z (pool i) (coeff i) t (P i)‖^2 ≤ pay*U^(e*w i)

/-- Absolute summability is inherited from the actual finite ordinary and
slot polynomials, not postulated as an extra source hypothesis. -/
theorem subset_summable {Slot : Type*} (F : Finset Slot)
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ b₁ b₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hP : ∀ i, 0 ≤ P i) :
    Summable (fun z : O => if keep z then
      ‖selectedProduct F η m A z W₁ W₂ pool coeff P t X₁ X₂‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB⟩ := product_bounded η m A t
    (Real.sqrt (X₁*X₂*∏ i : F, P i.val) : ℂ)⁻¹ W₁ W₂ b₁ b₂ X₁ X₂
    hs₁ hs₂ hX₁ hX₂ (fun i : F => pool i.val) (fun i : F => coeff i.val)
  have hbound : ∀ z, ‖selectedProduct F η m A z W₁ W₂ pool coeff P t X₁ X₂‖ ≤ B := by
    intro z
    rw [selectedProduct_eq_subset_row F η m A z t W₁ W₂ pool coeff P X₁ X₂ (mul_pos hX₁ hX₂).le hP]
    exact hB z
  exact bounded_radial_summable _ B hbound keep Φ K hK

/-- The original positive low-row energy is bounded by the retained genuine
source energy on the same keep. No lower bound on a Fourier summand is used. -/
theorem low_energy_erasure {Slot : Type*} [DecidableEq Slot] (J F : Finset Slot) (hF : F ⊆ J)
    (η : Character) (m A : O) (t U e pay : ℝ) (w : Slot → ℝ)
    (W₁ W₂ : ℝ → ℂ) (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ)
    (P : Slot → ℝ) (X₁ X₂ b₁ b₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x, 0 ≤ (Φ x).re)
    (K : ℝ) (hK : 0 < K) (hU : 0 < U) (hpay : 0 ≤ pay) (hP : ∀ i, 0 ≤ P i) :
    subsetEnergy J η m A t W₁ W₂ pool coeff P X₁ X₂
      (fun z => keep z ∧ LowRows J η m A t U e pay w pool coeff P z) Φ K ≤
      (pay^(J\F).card*U^(e*∑ i ∈ J\F, w i))*
        subsetEnergy F η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K := by
  classical
  have hp0 : 0 ≤ pay^(J\F).card*U^(e*∑ i ∈ J\F, w i) := by positivity
  have hsleft := subset_summable J η m A t W₁ W₂ pool coeff P X₁ X₂ b₁ b₂ hX₁ hX₂ hs₁ hs₂
    (fun z => keep z ∧ LowRows J η m A t U e pay w pool coeff P z) Φ K hK hP
  have hsright := subset_summable F η m A t W₁ W₂ pool coeff P X₁ X₂ b₁ b₂ hX₁ hX₂ hs₁ hs₂ keep Φ K hK hP
  rw [subsetEnergy_eq_selected_tsum J η m A t W₁ W₂ pool coeff P X₁ X₂ _ Φ K (mul_pos hX₁ hX₂).le hP,
    subsetEnergy_eq_selected_tsum F η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K (mul_pos hX₁ hX₂).le hP,
    ←tsum_mul_left]
  apply hsleft.tsum_le_tsum _ (hsright.mul_left _)
  intro z
  by_cases hk : keep z
  · by_cases hl : LowRows J η m A t U e pay w pool coeff P z
    · simp only [hk,hl,and_self,ite_eq_left]
      have hrow : ‖selectedProduct J η m A z W₁ W₂ pool coeff P t X₁ X₂‖^2 ≤
          (pay^(J\F).card*U^(e*∑ i ∈ J\F, w i))*
            ‖selectedProduct F η m A z W₁ W₂ pool coeff P t X₁ X₂‖^2 := by
        have heq : selectedProduct J η m A z W₁ W₂ pool coeff P t X₁ X₂ =
            (∏ i ∈ J\F, normalizedSlot η m A z (pool i) (coeff i) t (P i))*
              selectedProduct F η m A z W₁ W₂ pool coeff P t X₁ X₂ := by
          unfold selectedProduct
          rw [←Finset.prod_sdiff hF]
          ring
        rw [heq,norm_mul,mul_pow,norm_prod,←Finset.prod_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        calc
          _ ≤ ∏ i ∈ J\F, pay*U^(e*w i) := Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
            (fun i hi => hl i (Finset.mem_sdiff.mp hi).1)
          _ = _ := by
            rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hU,←Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_right hrow (hΦ _)).trans_eq (by ring)
    · simp only [hk,hl,and_false,ite_eq_left]
      exact mul_nonneg hp0 (mul_nonneg (sq_nonneg _) (hΦ _))
  · simp [hk]

end
end QRH.Cycle092.WholeSlot
