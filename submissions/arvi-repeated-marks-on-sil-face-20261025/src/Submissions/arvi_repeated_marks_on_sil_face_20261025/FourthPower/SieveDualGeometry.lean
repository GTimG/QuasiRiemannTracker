/- Copyright (c) 2026 Sil. Apache-2.0.
Identify the literal dual Poisson term with the cross kernel controlled by
SievePoissonBound. All repeated-prime factors, twists and normalizations remain.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SievePoissonBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyDyads

set_option autoImplicit false
namespace Candidate.FourthPower.SieveDualGeometry
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CanonicalRowCompletion CanonicalQuadraticSieve
open SexticSieve SievePrimitive SieveCoupling SieveGaussPairs SievePairPoisson SieveUncoupling
open EisensteinSchwartzPoisson
local notation "Id" => Ideal ActualEisensteinCubic.O
local notation "O" => ActualEisensteinCubic.O

theorem modulus_norm_sq (I : Id) (hI : Supported I) :
    ‖eisEmbedding (modulus I)‖^2 = (Ideal.absNorm I.radical : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,span_modulus I hI.1]

theorem modulus_norm_pos (I : Id) : 0 < ‖eisEmbedding (modulus I)‖ :=
  norm_pos_iff.mpr (eisEmbedding_ne_zero (modulus_ne_zero I))

def dualCoefficient (I : Id) (hI : Supported I) (a : ℂ) (c : O) : ℂ :=
  star (a*phase I hI*star (idealRowHom c I)) / (‖eisEmbedding (modulus I)‖ : ℂ)

theorem dualCoefficient_mass (I : Id) (hI : Supported I) (hf : PowerFree 6 I)
    (a : ℂ) (c : O) :
    ‖dualCoefficient I hI a c‖^2 ≤ ‖a‖^2 / (Ideal.absNorm I.radical : ℝ) := by
  simp only [dualCoefficient,norm_div,norm_star,norm_mul,phase_norm I hI hf,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_pow,mul_pow,
    modulus_norm_sq I hI]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (idealRowHom_norm c I))

theorem dualCoefficient_family_mass {n : Type*} [Fintype n] (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i)) (a : n → ℂ)
    (c : O) (N : ℝ) (hN : 0 < N) (hn : ∀ i, N ≤ (Ideal.absNorm (cols i).radical : ℝ)) :
    (∑ i, ‖dualCoefficient (cols i) (hc i) (a i) c‖^2) ≤ (1/N)*∑ i, ‖a i‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply (dualCoefficient_mass _ (hc i) (hf i) (a i) c).trans
  simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using
    div_le_div_of_nonneg_left (sq_nonneg ‖a i‖) hN (hn i)

/-- Exact cross-kernel formula for an arbitrary fixed bad factor c and a
supported frequency ideal K. No bound for the entire family is assumed. -/
theorem dualTerm_cross (I J K : Id) (hI : Supported I) (hJ : Supported J)
    (hK : Supported K) (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J)
    (hcop : IsCoprime I J) (a b : ℂ) (c : O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    dualTerm I J hI hJ a b W M (c*primaryGenerator K) =
      SieveRayCoupling.eta (SieveRayCoupling.label I hI) (SieveRayCoupling.label J hJ) *
      star (dualCoefficient I hI a c)*dualCoefficient J hJ b c*
      crossKernel (sharp I) (sharp J) I.radical J.radical K *
      paperRadialFourier W (M*‖eisEmbedding c‖^2*(Ideal.absNorm K : ℝ)/
        ((Ideal.absNorm I.radical : ℝ)*(Ideal.absNorm J.radical : ℝ))) := by
  have harg : M*‖eisEmbedding (c*primaryGenerator K)‖^2 /
      ‖eisEmbedding (modulus I*modulus J)‖^2 =
      M*‖eisEmbedding c‖^2*(Ideal.absNorm K : ℝ)/
        ((Ideal.absNorm I.radical : ℝ)*(Ideal.absNorm J.radical : ℝ)) := by
    simp only [map_mul,norm_mul,mul_pow,modulus_norm_sq I hI,modulus_norm_sq J hJ,
      primaryGenerator_norm_sq K (supported_primaryGenerator_ne_zero K hK),mul_assoc]
  have hi : idealRowHom (c*primaryGenerator K) I = idealRowHom c I*rowValue K I :=
    idealRowHom_argument_mul c (primaryGenerator K) I
  have hj : idealRowHom (c*primaryGenerator K) J = idealRowHom c J*rowValue K J :=
    idealRowHom_argument_mul c (primaryGenerator K) J
  unfold dualTerm
  rw [harg,SieveRayCoupling.gauss_coupling I J hI hJ hfI hfJ hcop,hi,hj]
  simp only [dualCoefficient,crossKernel,normal_form I hI.1,normal_form J hJ.1,star_mul,star_star,star_div₀,
    Complex.star_def,Complex.conj_ofReal,Complex.conj_conj,map_mul,norm_mul,Complex.ofReal_mul]
  ring

theorem row_zero_of_ne_one (I : Id) (hI : Supported I) (hI1 : I ≠ 1) :
    idealRowHom (0 : O) I = 0 := by
  have ht : I ≠ ⊤ := by simpa only [Ideal.one_eq_top] using hI1
  have hc : ¬IsCoprime I (Ideal.span {(0 : O)}) := by
    simpa only [Ideal.isCoprime_iff_sup_eq,Ideal.span_singleton_zero,sup_bot_eq] using ht
  have he := idealRowHom_sixth_mask (0 : O) I hI
  simpa only [ite_eq_right hc,zero_pow (by decide : (6 : ℕ) ≠ 0)] using he

theorem dualTerm_zero (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hne : I ≠ 1 ∨ J ≠ 1) (a b : ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    dualTerm I J hI hJ a b W M 0 = 0 := by
  rcases hne with h | h <;> simp [dualTerm,row_zero_of_ne_one _ (by assumption) h]

theorem pairGauss_norm_le (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hc : IsCoprime I J) :
    ‖pairGauss I J hI hJ‖ ≤ 1 := by
  rw [SieveRayCoupling.gauss_coupling I J hI hJ hfI hfJ hc]
  simp only [norm_mul,norm_star,phase_norm I hI hfI,phase_norm J hJ hfJ,mul_one]
  have he := SieveRayCoupling.eta_norm_le (SieveRayCoupling.label I hI) (SieveRayCoupling.label J hJ)
  have hr : ‖rowValue J.radical (sharp I)‖ ≤ 1 := idealRowHom_norm _ _
  have hs : ‖rowValue I.radical (sharp J)‖ ≤ 1 := idealRowHom_norm _ _
  have hfirst := ((mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)).trans hr
  exact ((mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)).trans_eq (one_mul _)).trans hs

def dualFamily {n : Type*} [Fintype n] (cols : n → Id) (hc : ∀ i, Supported (cols i))
    (a b : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (k : O) : ℂ :=
  ∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
    dualTerm (cols j) (cols i) (hc j) (hc i) (b j) (a i) W M k else 0

theorem dualFamily_summable {n : Type*} [Fintype n] (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (a b : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (dualFamily cols hc a b W M) := by
  apply summable_sum
  intro i _
  apply summable_sum
  intro j _
  by_cases h : IsCoprime (cols i) (cols j)
  · simpa only [ite_eq_left h] using dualTerm_summable (cols j) (cols i) (hc j) (hc i) (b j) (a i) W M hM
  · simpa only [ite_eq_right h] using (summable_zero : Summable (fun _ : O => (0 : ℂ)))

theorem dualTerm_unit_bound (h : Supported (1 : Id)) (hf : PowerFree 6 (1 : Id))
    (a b : ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    ‖dualTerm 1 1 h h a b W M 0‖ ≤ ‖a‖*‖b‖*‖paperRadialFourier W 0‖ := by
  have hn : ‖eisEmbedding (modulus (1 : Id))‖ = 1 := by
    have he := modulus_norm_sq 1 h
    have hr : (1 : Id).radical = 1 := by
      simpa only [Ideal.one_eq_top] using Ideal.radical_top O
    rw [hr,map_one,Nat.cast_one] at he
    nlinarith [norm_nonneg (eisEmbedding (modulus (1 : Id)))]
  have hp := pairGauss_norm_le 1 1 h h hf hf isCoprime_one_left
  simp only [dualTerm,map_one,map_zero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero,zero_div,star_one,one_mul,map_mul,norm_mul,hn,mul_one,Complex.ofReal_one,
    div_one,norm_star]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hp) (norm_nonneg _)

theorem dualFamily_zero_bound {n : Type*} [Fintype n] (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
    (hinj : Function.Injective cols) (a b : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    ‖dualFamily cols hc a b W M 0‖^2 ≤
      ‖paperRadialFourier W 0‖^2*(∑ i, ‖a i‖^2)*(∑ j, ‖b j‖^2) := by
  by_cases hu : ∃ i, cols i = 1
  · obtain ⟨i₀,hi₀⟩ := hu
    have hnot (i : n) (hi : i ≠ i₀) : cols i ≠ 1 := fun he => hi (hinj (he.trans hi₀.symm))
    have he : dualFamily cols hc a b W M 0 =
        dualTerm (cols i₀) (cols i₀) (hc i₀) (hc i₀) (b i₀) (a i₀) W M 0 := by
      unfold dualFamily
      rw [Finset.sum_eq_single i₀]
      · rw [Finset.sum_eq_single i₀]
        · simp only [hi₀,isCoprime_one_left,ite_true]
        · intro j _ hj
          by_cases h : IsCoprime (cols i₀) (cols j)
          · rw [ite_eq_left h,dualTerm_zero _ _ _ _ (Or.inl (hnot j hj))]
          · exact ite_eq_right h
        · simp
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro j _
        by_cases h : IsCoprime (cols i) (cols j)
        · rw [ite_eq_left h,dualTerm_zero _ _ _ _ (Or.inr (hnot i hi))]
        · exact ite_eq_right h
      · simp
    rw [he]
    have hb : ‖dualTerm (cols i₀) (cols i₀) (hc i₀) (hc i₀) (b i₀) (a i₀) W M 0‖ ≤
        ‖b i₀‖*‖a i₀‖*‖paperRadialFourier W 0‖ := by
      have h1 : Supported (1 : Id) := hi₀ ▸ hc i₀
      have h6 : PowerFree 6 (1 : Id) := hi₀ ▸ hf i₀
      simpa only [hi₀] using dualTerm_unit_bound h1 h6 (b i₀) (a i₀) W M
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [mul_pow,mul_pow] at hsq
    have ha : ‖a i₀‖^2 ≤ ∑ i, ‖a i‖^2 := Finset.single_le_sum (fun i _ => sq_nonneg ‖a i‖) (Finset.mem_univ i₀)
    have hb' : ‖b i₀‖^2 ≤ ∑ i, ‖b i‖^2 := Finset.single_le_sum (fun i _ => sq_nonneg ‖b i‖) (Finset.mem_univ i₀)
    calc
      _ ≤ ‖b i₀‖^2*‖a i₀‖^2*‖paperRadialFourier W 0‖^2 := hsq
      _ ≤ (∑ i, ‖b i‖^2)*(∑ i, ‖a i‖^2)*‖paperRadialFourier W 0‖^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hb' ha (sq_nonneg _) (by positivity)) (sq_nonneg _)
      _ = _ := by ring
  · have hz : dualFamily cols hc a b W M 0 = 0 := by
      unfold dualFamily
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      by_cases h : IsCoprime (cols i) (cols j)
      · rw [ite_eq_left h,dualTerm_zero _ _ _ _ (Or.inr (fun he => hu ⟨i,he⟩))]
      · exact ite_eq_right h
    rw [hz,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

theorem poisson_frequency_shells {n : Type*} [Fintype n] (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
    (a b : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    SievePoissonBound.pairing (SieveSmoothed.gramMatrix cols W M) a b =
      (M : ℂ)*(dualFamily cols hc a b W M 0 +
        ∑' j : ℕ, ∑ k : CubicSieve.frequencyDyad j, dualFamily cols hc a b W M k.val) := by
  rw [SievePoissonBound.gram_pairing_poisson cols hc hf a b W M hM]
  congr 1
  exact CubicSieve.tsum_frequencyDyads_with_zero _ (dualFamily_summable cols hc a b W M hM)

end
end Candidate.FourthPower.SieveDualGeometry
