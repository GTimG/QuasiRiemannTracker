import WeightedQRH.Parameters
import OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation

/-! A radical-sized presentation of the actual physical row, with its exact
smoothed sums and the same reflected character coefficients. The radical
periodicity theorem is upstream; this module connects it to the natural
primitive/deletion reflection API without making a primitive-choice assumption.
-/
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace WeightedQRH.RowConductor
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor ProbeHighRowFamily CenteredMomentNaturalPrimitive
open CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O

theorem idealCoeff_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) (I : Ideal O) :
    idealCoeff χ I = idealCoeff τ I := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
  rw [← hs, idealCoeff_span _ hn, idealCoeff_span _ hn, he]

theorem inverse_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) (n : O) :
    elementCoeff χ.inverse n = elementCoeff τ.inverse n := by
  rw [elementCoeff_inverse, elementCoeff_inverse, he]

theorem polynomial_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n)
    (inv : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) :
    HeckeDyadic.polynomial χ inv W D σ ω = HeckeDyadic.polynomial τ inv W D σ ω := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  simp only [HeckeDyadic.summand, HeckeDyadic.coefficient,
    idealCoeff_eq_of_elementCoeff_eq χ τ he I.val]

theorem principal_iff_of_equal_elements (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) :
    χ.residue = 1 ↔ τ.residue = 1 := by
  apply HeckeFiniteDeletion.principal_iff_of_mask χ τ
  intro I
  by_cases hc : IsCoprime I χ.modulus
  · rw [ite_eq_left hc, idealCoeff_eq_of_elementCoeff_eq χ τ he]
  · rw [ite_eq_right hc]
    simpa only [hc, ite_false] using idealCoeff_source_mask χ I

theorem LFunction_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    LFunction χ s = LFunction τ s := by
  unfold LFunction
  rw [continuedLattice_eq_of_elementCoeff_eq χ τ he hs hs1]

/-- This preserves all coefficients, including their zeros at deleted primes. -/
theorem exists_row_small_presentation (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ∃ τ : Character,
      τ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ n : O, elementCoeff (rowCharacter S hS u) n = elementCoeff τ n := by
  obtain ⟨τ, hn, he⟩ := rawRow_small_presentation u
  refine ⟨τ.excludePrimes S hS, ?_, equal_elements_excludePrimes _ τ he S hS⟩
  change (τ.modulus * ∏ P ∈ S, P).absNorm ≤ _
  rw [map_mul]
  simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right ((∏ P ∈ S, P).absNorm) hn

/-- A combined primitive-plus-redundant scale already pays for all finite
Euler deletions. Its selected-prime deficit therefore does not require
claiming that the redundant primes belong to a fixed set. -/
theorem reflected_scale_selected_deficit
    (S : Finset (Ideal O)) (u : FreeRow) (τ ψ : Character)
    (hτ : τ.modulus.absNorm ≤ fixedConductorConstant S *
      (Ideal.span {u.val} : Ideal O).radical.absNorm)
    (hcap : ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
      τ.modulus.absNorm)
    {k : ℕ} (P : Fin k → Ideal O) (hP : ∀ i, Prime (P i))
    (hdis : Function.Injective P) (e : Fin k → ℕ) (he : ∀ i, 2 ≤ e i)
    (hdiv : ∀ i, P i ^ e i ∣ Ideal.span {u.val}) :
    (ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
      ∏ i, (P i).absNorm ^ (e i - 1) ≤
        fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm := by
  have hr := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1) P hP hdis e
    (fun i => by have := he i; omega) hdiv
  calc
    _ ≤ (fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).radical.absNorm) *
        ∏ i, (P i).absNorm ^ (e i - 1) := Nat.mul_le_mul_right _ (hcap.trans hτ)
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (fixedConductorConstant S) hr

theorem reflected_scale_selected_deficit_real
    (S : Finset (Ideal O)) (u : FreeRow) (τ ψ : Character)
    (hτ : τ.modulus.absNorm ≤ fixedConductorConstant S *
      (Ideal.span {u.val} : Ideal O).radical.absNorm)
    (hcap : ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
      τ.modulus.absNorm)
    {k : ℕ} (P : Fin k → Ideal O) (hP : ∀ i, Prime (P i))
    (hdis : Function.Injective P) (e : Fin k → ℕ) (he : ∀ i, 2 ≤ e i)
    (hdiv : ∀ i, P i ^ e i ∣ Ideal.span {u.val}) :
    ((ψ.modulus.absNorm : ℝ) * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
      ∏ i, ((P i).absNorm : ℝ) ^ (e i - 1) ≤
        (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm := by
  exact_mod_cast reflected_scale_selected_deficit S u τ ψ hτ hcap P hP hdis e he hdiv

theorem reflected_scale_pos (τ ψ : Character) :
    0 < (ψ.modulus.absNorm : ℝ) * (redundantIdeal τ.modulus ψ.modulus).absNorm := by
  apply mul_pos
  · exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  · exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (redundantIdeal_ne_zero τ.modulus ψ.modulus))

/-- Exact original physical numerator reflection using a radical-sized
presentation. The output preserves the physical row and its inverse on all
ideals; the RHS is the actual upstream retained/discarded reflection. -/
theorem row_original_split (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow)
    (hn : (rowCharacter S hS u).residue ≠ 1) :
    ∃ (τ ψ : Character) (g : ℂ),
      (∀ n : O, elementCoeff (rowCharacter S hS u) n = elementCoeff τ n) ∧
      (∀ I : Ideal O, idealCoeff (rowCharacter S hS u).inverse I = idealCoeff τ.inverse I) ∧
      τ.residue ≠ 1 ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.residue ≠ 1 ∧ ‖g‖ = 1 ∧
      τ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
        τ.modulus.absNorm ∧
      (∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) →
        Function.Injective P → ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
        (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
        (ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
          ∏ i, (P i).absNorm ^ (e i - 1) ≤
            fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm) ∧
      ∀ (G : 𝓢(ℝ, ℂ)) (X R : ℝ), 0 < X →
        HeckeDyadic.polynomial (rowCharacter S hS u) false G X 0 0 =
          g * (retainedSchwartz τ ψ G X R + discardedSchwartz τ ψ G X R) := by
  obtain ⟨τ, hτ, he⟩ := exists_row_small_presentation S hS u
  have hnτ : τ.residue ≠ 1 := fun h => hn ((principal_iff_of_equal_elements _ τ he).mpr h)
  obtain ⟨ψ, g, hp, hnp, hg, hcap, hsplit⟩ := original_split τ hnτ
  refine ⟨τ, ψ, g, he, ?_, hnτ, hp, hnp, hg, hτ, hcap, ?_, ?_⟩
  · exact idealCoeff_eq_of_elementCoeff_eq _ _ (inverse_elementCoeff_eq _ _ he)
  · intro k P hP hdis e he hdiv
    exact reflected_scale_selected_deficit S u τ ψ hτ hcap P hP hdis e he hdiv
  · intro G X R hX
    rw [polynomial_eq_of_elementCoeff_eq _ τ he]
    exact hsplit G X R hX

end WeightedQRH.RowConductor
end
