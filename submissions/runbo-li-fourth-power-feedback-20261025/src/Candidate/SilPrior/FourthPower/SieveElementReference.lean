/- Copyright (c) 2026 Sil. Apache-2.0.
The reference bound on literal Eisenstein elements. Every nonzero element,
including its factors over 2 and 3, and the zero frequency are retained.
-/
import Candidate.SilPrior.FourthPower.SieveReference

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SieveElementReference
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open SexticSieve SieveReference SieveFrequencyGeometry
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def elementEnergy (rows : Finset O) (columns : Finset Id) (a : Id → ℂ) : ℝ :=
  ∑ x ∈ rows, ‖∑ I ∈ columns, a I*idealRowHom x I‖^2

def twisted (c : O) (a : Id → ℂ) (I : Id) : ℂ := a I*idealRowHom c I

theorem twisted_mass_le (c : O) (columns : Finset Id) (a : Id → ℂ) :
    coefficientMass columns (twisted c a) ≤ coefficientMass columns a := by
  apply Finset.sum_le_sum
  intro I _
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  rw [twisted,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (idealRowHom_norm c I)

theorem twisted_row (c : O) (K : Id) (columns : Finset Id) (a : Id → ℂ) :
    (∑ I ∈ columns, a I*idealRowHom (c*primaryGenerator K) I) =
      ∑ I ∈ columns, twisted c a I*rowValue K I := by
  apply Finset.sum_congr rfl
  intro I _
  rw [idealRowHom_argument_mul]
  exact (mul_assoc _ _ _).symm

theorem nonzero_energy_partition (M : ℝ) (rows : Finset O)
    (hr : ∀ x ∈ rows, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ M)
    (columns : Finset Id) (a : Id → ℂ) :
    elementEnergy rows columns a = ∑ l : BadLabel M,
      energy (frequencies M rows hr l) columns (twisted (factor M l) a) := by
  have he := congrArg Complex.re (frequency_sum M rows hr
    (fun x => (↑(‖∑ I ∈ columns, a I*idealRowHom x I‖^2) : ℂ)))
  simp only [Complex.re_sum,Complex.ofReal_re] at he
  simpa only [elementEnergy,energy,twisted_row] using he

theorem nonzero_reference (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      ∀ (rows : Finset O) (columns : Finset Id),
      (∀ x ∈ rows, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ M) →
      (∀ I ∈ columns, Supported I ∧ PowerFree 6 I ∧ (Ideal.absNorm I : ℝ) ≤ N) →
      ∀ a : Id → ℂ, elementEnergy rows columns a ≤
        C*(M*N)^ε*referenceMajorant M N*coefficientMass columns a := by
  obtain ⟨C,hC,hb⟩ := ideal_reference (ε/2) (by positivity)
  obtain ⟨D,hD,hd⟩ := labels_small_power (ε/2) (by positivity)
  refine ⟨D*C,by positivity,?_⟩
  intro M N hM hN rows columns hr hc a
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hm := referenceMajorant_nonneg M N hM0.le hN0.le
  have ha := coefficientMass_nonneg columns a
  have hf (l : BadLabel M) :
      energy (frequencies M rows hr l) columns (twisted (factor M l) a) ≤
        C*(M*N)^(ε/2)*referenceMajorant M N*coefficientMass columns a := by
    have hrows : ∀ K ∈ frequencies M rows hr l,
        Supported K ∧ (Ideal.absNorm K : ℝ) ≤ M := by
      intro K hK
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hK
      exact SieveRanges.mem_fullRange.mp (representation M rows hr x).2.property
    exact (hb M N hM hN _ columns hrows hc _).trans
      (mul_le_mul_of_nonneg_left (twisted_mass_le (factor M l) columns a) (by positivity))
  have hp : M^(ε/2)*(M*N)^(ε/2) ≤ (M*N)^ε := by
    apply (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hM0.le (le_mul_of_one_le_right hM0.le hN) (by positivity : 0 ≤ ε/2))
      (by positivity : 0 ≤ (M*N)^(ε/2))).trans_eq
    rw [← Real.rpow_add (mul_pos hM0 hN0)]
    congr 1
    ring
  rw [nonzero_energy_partition M rows hr]
  calc
    _ ≤ ∑ _l : BadLabel M, C*(M*N)^(ε/2)*referenceMajorant M N*coefficientMass columns a :=
      Finset.sum_le_sum (fun l _ => hf l)
    _ = (Fintype.card (BadLabel M) : ℝ)*
        (C*(M*N)^(ε/2)*referenceMajorant M N*coefficientMass columns a) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ (D*M^(ε/2))*(C*(M*N)^(ε/2)*referenceMajorant M N*coefficientMass columns a) :=
      mul_le_mul_of_nonneg_right (hd M hM) (by positivity)
    _ = (D*C)*(M^(ε/2)*(M*N)^(ε/2))*referenceMajorant M N*coefficientMass columns a := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) hm) ha

theorem zero_character (I : Id) (hI : Supported I) :
    idealRowHom (0 : O) I = if I = 1 then 1 else 0 := by
  have he := idealRowHom_sixth_mask (0 : O) I hI
  simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0),Ideal.span_singleton_zero,
    Ideal.isCoprime_iff_sup_eq,sup_bot_eq,Ideal.one_eq_top] using he

theorem zero_energy_le (columns : Finset Id)
    (hc : ∀ I ∈ columns, Supported I) (a : Id → ℂ) :
    ‖∑ I ∈ columns, a I*idealRowHom (0 : O) I‖^2 ≤ coefficientMass columns a := by
  have he : (∑ I ∈ columns, a I*idealRowHom (0 : O) I) =
      if (1 : Id) ∈ columns then a 1 else 0 := by
    calc
      _ = ∑ I ∈ columns, if I = 1 then a I else 0 := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [zero_character I (hc I hI)]
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_ite_eq']
  rw [he]
  split_ifs with h
  · exact Finset.single_le_sum (fun I _ => sq_nonneg ‖a I‖) h
  · simpa only [norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using coefficientMass_nonneg columns a

/-- The actual element row family, including zero, with no restriction at 2 or 3. -/
theorem element_reference (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      ∀ (rows : Finset O) (columns : Finset Id),
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ M) →
      (∀ I ∈ columns, Supported I ∧ PowerFree 6 I ∧ (Ideal.absNorm I : ℝ) ≤ N) →
      ∀ a : Id → ℂ, elementEnergy rows columns a ≤
        C*(M*N)^ε*referenceMajorant M N*coefficientMass columns a := by
  obtain ⟨C,hC,hb⟩ := nonzero_reference ε hε
  refine ⟨C+1,by positivity,?_⟩
  intro M N hM hN rows columns hr hc a
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hp : 1 ≤ (M*N)^ε := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hN) hε.le
  have hm : 1 ≤ referenceMajorant M N := referenceMajorant_ge_one M N hM hN0.le
  have ha := coefficientMass_nonneg columns a
  have hrest := hb M N hM hN (rows.erase 0) columns
    (fun x hx => ⟨(Finset.mem_erase.mp hx).1,hr x (Finset.mem_erase.mp hx).2⟩) hc a
  have hz := zero_energy_le columns (fun I hI => (hc I hI).1) a
  have hsplit : elementEnergy rows columns a ≤
      elementEnergy (rows.erase 0) columns a + coefficientMass columns a := by
    by_cases hzero : (0 : O) ∈ rows
    · rw [elementEnergy,← Finset.sum_erase_add _ _ hzero]
      exact add_le_add le_rfl hz
    · have he : rows.erase 0 = rows := by
        ext x
        simp only [Finset.mem_erase]
        exact ⟨And.right,fun hx => ⟨fun hx0 => hzero (hx0 ▸ hx),hx⟩⟩
      rw [he]
      exact le_add_of_nonneg_right ha
  have hunit := mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hp hm) ha
  calc
    _ ≤ elementEnergy (rows.erase 0) columns a + coefficientMass columns a := hsplit
    _ ≤ C*(M*N)^ε*referenceMajorant M N*coefficientMass columns a +
        ((M*N)^ε*referenceMajorant M N)*coefficientMass columns a :=
      add_le_add hrest (by simpa only [one_mul] using hunit)
    _ = _ := by ring

end
end Candidate.SilPrior.FourthPower.SieveElementReference
