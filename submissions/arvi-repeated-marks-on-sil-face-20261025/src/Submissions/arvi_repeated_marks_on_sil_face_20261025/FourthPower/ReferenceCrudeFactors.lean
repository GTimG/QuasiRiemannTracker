/- Copyright (c) 2026 Sil. Apache-2.0.
Polynomial bounds for the remaining actual factors. They are used only to
pay the arbitrarily small reflection tail, never as the main energy estimate.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceFactors

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceCrudeFactors
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentSourceMass ReferenceFactors
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

theorem factor_norm (F : Factor) (χ : Character) :
    ‖F.value χ‖ ≤ 128*F.length*F.amplitude := by
  let S := F.pool.filter (fun I => I ≠ 0)
  have he : (∑ I ∈ S, F.coefficient I*idealCoeff χ I) = F.value χ := by
    apply Finset.sum_filter_of_ne
    intro I _ hn hI
    subst I
    exact hn (by simp only [map_zero,mul_zero])
  have hb (I : Id) (hI : I ∈ S) : ‖F.coefficient I*idealCoeff χ I‖ ≤ F.amplitude := by
    have hi := Finset.mem_filter.mp hI
    have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi.2)
    have hs : 1 ≤ Real.sqrt (Ideal.absNorm I : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN
    rw [norm_mul]
    exact ((mul_le_of_le_one_right (norm_nonneg _) (idealCoeff_norm_le_one χ I)).trans
      (F.coefficient_bound I hi.1)).trans (div_le_self F.amplitude_nonneg hs)
  have hsub : S ⊆ idealBall F.length := by
    intro I hI
    have hi := Finset.mem_filter.mp hI
    exact (mem_idealBall _ _).mpr ⟨hi.2,F.support_bound I hi.1⟩
  have hcard : (S.card : ℝ) ≤ 128*F.length :=
    (show (S.card : ℝ) ≤ (idealBall F.length).card by exact_mod_cast Finset.card_le_card hsub).trans
      (idealBall_card F.length F.length_nonneg)
  rw [← he]
  calc
    _ ≤ ∑ I ∈ S, ‖F.coefficient I*idealCoeff χ I‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ S, F.amplitude := Finset.sum_le_sum (fun I hI => hb I hI)
    _ = (S.card : ℝ)*F.amplitude := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard F.amplitude_nonneg

theorem product_norm (F : α → Factor) (χ : Character) :
    ‖∏ i, (F i).value χ‖ ≤ 128^(Fintype.card α)*(∏ i, (F i).length)*(∏ i, (F i).amplitude) := by
  rw [norm_prod]
  apply (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => factor_norm (F i) χ)).trans_eq
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

theorem smooth_product_norm (χ : Character) (W : ℝ → ℂ) (d B X omega : ℝ)
    (hd : 0 ≤ d) (hB : 0 ≤ B) (hX : 0 < X) (hW : ∀ x, ‖W x‖ ≤ B)
    (hs : Function.support W ⊆ Set.Iic d) (F : α → Factor) :
    ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*omega)*∏ i, (F i).value χ‖ ≤
      128^(Fintype.card α+1)*(d*X*∏ i, (F i).length)*(Real.sqrt d*B*∏ i, (F i).amplitude) := by
  have hh := factor_norm (Factor.smooth W d B X omega hd hB hX hW) χ
  rw [Factor.smooth_value W d B X omega hd hB hX hW hs] at hh
  change ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*omega)‖ ≤
    128*(d*X)*(Real.sqrt d*B) at hh
  rw [norm_mul]
  apply (mul_le_mul hh (product_norm F χ) (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hd hX.le))
      (mul_nonneg (Real.sqrt_nonneg _) hB))).trans_eq
  rw [pow_succ]
  ring

theorem row_count (rows : Finset O) (M : ℝ) (hM : 1 ≤ M)
    (hr : ∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ M) :
    (rows.card : ℝ) ≤ 128*M := by
  apply DescentFiberCost.finite_element_count_real rows M hM
  intro x hx
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact hr x hx

theorem error_energy (rows : Finset O) (e P : rows → ℂ) (M B Q : ℝ)
    (hM : 1 ≤ M) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hr : ∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ M)
    (he : ∀ i, ‖e i‖ ≤ B) (hp : ∀ i, ‖P i‖ ≤ Q) :
    (∑ i : rows, ‖e i*P i‖^2) ≤ 128*M*B^2*Q^2 := by
  calc
    _ ≤ ∑ i : rows, (B*Q)^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (he i) (hp i) (norm_nonneg _) hB) 2
    _ = (rows.card : ℝ)*(B*Q)^2 := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    _ ≤ (128*M)*(B*Q)^2 := mul_le_mul_of_nonneg_right (row_count rows M hM hr) (sq_nonneg _)
    _ = _ := by ring

end
end Candidate.FourthPower.ReferenceCrudeFactors
