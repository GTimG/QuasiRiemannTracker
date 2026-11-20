/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterGlobal

/-! Uniform subpower control of the genuine full coefficient mass, including
all permitted exceptional valuation polynomials. -/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily

lemma finsetProductSum_le_exp {α : Type*} (f : α → ℝ) (hf : ∀ a,0 ≤ f a) (hs : Summable f) :
    (∑' S : Finset α,∏ a ∈ S,f a) ≤ Real.exp (∑' a,f a) := by
  apply Real.tsum_le_of_sum_le (fun S => Finset.prod_nonneg (fun a _ => hf a))
  intro T
  calc
    _ ≤ ∑ S ∈ (T.biUnion id).powerset,∏ a ∈ S,f a :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun S hS => Finset.mem_powerset.mpr
        (Finset.subset_biUnion_of_mem id hS)) (fun S _ _ => Finset.prod_nonneg (fun a _ => hf a))
    _ = ∏ a ∈ T.biUnion id,(1+f a) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ a ∈ T.biUnion id,f a) := Real.prod_one_add_le_exp_sum _ hf
    _ ≤ _ := Real.exp_le_exp.mpr (hs.sum_le_tsum _ (fun a _ => hf a))

def primeMajorant (P : PrimeIdeal) : ℝ := 7*(Ideal.absNorm P.val : ℝ)^(-(6/5 : ℝ))

lemma primeMajorant_nonneg (P : PrimeIdeal) : 0 ≤ primeMajorant P := by unfold primeMajorant; positivity

lemma primeMajorant_summable : Summable primeMajorant := by
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (6/5 : ℂ)
    (by norm_num)).comp_injective
      (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal => P.val))
  have hm : Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val : ℝ)^(-(6/5 : ℝ))) := by
    apply hs.congr
    intro P
    rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right P.property.ne_zero]
    change ‖((Ideal.absNorm P.val : ℝ) : ℂ)^(-(6/5 : ℂ))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P)]
    norm_num
  exact hm.mul_left 7

def universalGoodMass : ℝ := Real.exp (∑' P : PrimeIdeal,primeMajorant P)

lemma universalGoodMass_pos : 0 < universalGoodMass := Real.exp_pos _

lemma primeTerm_mass_le (ψ₁ ψ₂ : Character) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) (P : PrimeIdeal) :
    (∑ j : Fin 7,‖primeTerm ψ₁ ψ₂ s₁ s₂ P j‖) ≤ primeMajorant P := by
  calc
    _ ≤ ∑ _j : Fin 7,(Ideal.absNorm P.val : ℝ)^(-(6/5 : ℝ)) :=
      Finset.sum_le_sum (fun j _ => primeTerm_norm_le ψ₁ ψ₂ s₁ s₂ hs₁ hs₂ P j)
    _ = _ := by simp [primeMajorant]

/-- A single constant controls every good coefficient series, independently of
the characters, the omitted finite exceptional set, and both vertical heights. -/
theorem goodSeries_mass_le (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    (∑' k : GoodIndex bad,‖goodSeriesTerm ψ₁ ψ₂ bad s₁ s₂ k‖) ≤ universalGoodMass := by
  have hlocal := (primeTerm_mass_summable ψ₁ ψ₂ s₁ s₂ hs₁ hs₂).subtype (fun P => P ∉ bad)
  have hmain := goodSeries_summable_norm ψ₁ ψ₂ bad s₁ s₂ hs₁ hs₂
  have hmajor := primeMajorant_summable.subtype (fun P => P ∉ bad)
  have hprod := summable_finsetProd_of_summable_nonneg
    (fun P : GoodPrimes bad => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hlocal
  have hmajorprod := summable_finsetProd_of_summable_nonneg
    (fun P : GoodPrimes bad => primeMajorant_nonneg P.val) hmajor
  calc
    _ = ∑' S : Finset (GoodPrimes bad),∏ P ∈ S,∑ j : Fin 7,‖primeTerm ψ₁ ψ₂ s₁ s₂ P.val j‖ := by
      rw [hmain.tsum_sigma]
      apply tsum_congr
      intro S
      rw [tsum_fintype,←Finset.prod_coe_sort S,Fintype.prod_sum]
      simp only [goodSeriesTerm,norm_prod]
    _ ≤ ∑' S : Finset (GoodPrimes bad),∏ P ∈ S,primeMajorant P.val :=
      hprod.tsum_le_tsum (fun S => Finset.prod_le_prod₀
        (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        (fun P _ => primeTerm_mass_le ψ₁ ψ₂ s₁ s₂ hs₁ hs₂ P.val)) hmajorprod
    _ ≤ Real.exp (∑' P : GoodPrimes bad,primeMajorant P.val) :=
      finsetProductSum_le_exp _ (fun P => primeMajorant_nonneg P.val) hmajor
    _ ≤ universalGoodMass := Real.exp_le_exp.mpr
      (primeMajorant_summable.tsum_subtype_le _ (fun P => P ∉ bad) primeMajorant_nonneg)

lemma exceptionalLocal_mass_le_six (ψ₁ ψ₂ : Character) (P : PrimeIdeal)
    (allowed : Finset (ℕ×ℕ)) (hallowed : allowed ⊆ residualPairs true true)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    (∑ ij ∈ allowed,‖(eulerVariable ψ₁ P s₁)^ij.1*(eulerVariable ψ₂ P s₂)^ij.2‖) ≤ 6 := by
  have hone : (Ideal.absNorm P.val : ℝ)^(-(2/5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (prime_norm_one_le P) (by norm_num)
  have hx := (eulerVariable_norm_bound ψ₁ P s₁ hs₁).trans hone
  have hy := (eulerVariable_norm_bound ψ₂ P s₂ hs₂).trans hone
  calc
    _ ≤ ∑ _ij ∈ allowed,(1 : ℝ) := by
      apply Finset.sum_le_sum
      intro ij _hij
      rw [norm_mul,norm_pow,norm_pow]
      have hxpow := pow_le_one₀ (norm_nonneg _) hx (n := ij.1)
      have hypow := pow_le_one₀ (norm_nonneg _) hy (n := ij.2)
      simpa only [one_mul] using mul_le_mul hxpow hypow (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    _ = (allowed.card : ℝ) := by simp
    _ ≤ 6 := by exact_mod_cast (Finset.card_le_card hallowed).trans_eq residualPairs_card

theorem badSeries_mass_le (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hallowed : ∀ P ∈ bad,allowed P ⊆ residualPairs true true)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    (∑ k : BadIndex bad allowed,‖badSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k‖) ≤ (6 : ℝ)^bad.card := by
  calc
    _ = ∏ P : bad,∑ ij : allowed P.val,
        ‖(eulerVariable ψ₁ P.val s₁)^ij.val.1*(eulerVariable ψ₂ P.val s₂)^ij.val.2‖ := by
      rw [Fintype.prod_sum]
      simp only [badSeriesTerm,norm_prod]
    _ ≤ ∏ _P : bad,(6 : ℝ) := Finset.prod_le_prod₀
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (fun P _ => by
        exact (Finset.sum_coe_sort (allowed P.val) (fun ij : ℕ×ℕ =>
          ‖(eulerVariable ψ₁ P.val s₁)^ij.1*(eulerVariable ψ₂ P.val s₂)^ij.2‖)).trans_le
          (exceptionalLocal_mass_le_six ψ₁ ψ₂ P.val (allowed P.val)
            (hallowed P.val P.property) s₁ s₂ hs₁ hs₂))
    _ = _ := by simp

lemma coefficientMass_eq_product (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) :
    coefficientMass ψ₁ ψ₂ bad allowed =
      (∑ k : BadIndex bad allowed,‖badSeriesTerm ψ₁ ψ₂ bad allowed (2/5 : ℂ) (2/5 : ℂ) k‖)*
      (∑' k : GoodIndex bad,‖goodSeriesTerm ψ₁ ψ₂ bad (2/5 : ℂ) (2/5 : ℂ) k‖) := by
  have he (k : FullIndex bad allowed) :
      ‖fullCoefficient ψ₁ ψ₂ bad allowed k‖*
        ((Ideal.absNorm (fullIdeal₁ bad allowed k) : ℝ)*
          (Ideal.absNorm (fullIdeal₂ bad allowed k) : ℝ))^(-(2/5 : ℝ)) =
      ‖fullSeriesTerm ψ₁ ψ₂ bad allowed (2/5 : ℂ) (2/5 : ℂ) k‖ := by
    rw [fullSeriesTerm_coefficient,norm_mul,norm_mul,
      normWeight_critical _ (fullIdeal₁_ne_zero bad allowed k),
      normWeight_critical _ (fullIdeal₂_ne_zero bad allowed k),
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  unfold coefficientMass
  simp_rw [he]
  rw [(fullSeries_summable_norm ψ₁ ψ₂ bad allowed (2/5 : ℂ) (2/5 : ℂ)
    (by norm_num) (by norm_num)).tsum_prod]
  simp only [fullSeriesTerm,norm_mul,tsum_mul_left]
  rw [tsum_mul_right,tsum_fintype]

theorem coefficientMass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
      (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P ∈ bad,allowed P ⊆ residualPairs true true) →
      coefficientMass ψ₁ ψ₂ bad allowed ≤ C*(Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := six_pow_card_subpower ε hε
  refine ⟨C*universalGoodMass,mul_pos hC universalGoodMass_pos,?_⟩
  intro ψ₁ ψ₂ bad allowed hallowed
  rw [coefficientMass_eq_product]
  have hb := badSeries_mass_le ψ₁ ψ₂ bad allowed hallowed (2/5 : ℂ) (2/5 : ℂ) (by norm_num) (by norm_num)
  have hg := goodSeries_mass_le ψ₁ ψ₂ bad (2/5 : ℂ) (2/5 : ℂ) (by norm_num) (by norm_num)
  exact (mul_le_mul hb hg (tsum_nonneg (fun _ => norm_nonneg _)) (by positivity)).trans
    ((mul_le_mul_of_nonneg_right (hbound bad) universalGoodMass_pos.le).trans_eq (by ring))

end
end QRH.Cycle092.SignedCenter
