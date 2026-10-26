/- Copyright (c) 2026 Sil. Apache-2.0.
The actual cubic twist has a modulus linear in the twist norm. Squaring
the existing sextic row character preserves its modulus and its natural zeros.
This is not the cruder construction using the squared row parameter D^2.
-/
import Candidate.FourthPower.ReferenceNaturalData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.UnitRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceCubicCharacter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRow CenteredMomentHeckeExpansion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem ideal_positive_power (χ : Character) (n : ℕ) (hn : n ≠ 0) (I : Id) :
    idealCoeff (χ.power n) I = (idealCoeff χ I)^n := by
  by_cases hI : I = 0
  · simp only [hI,map_zero,zero_pow hn]
  · rw [← span_idealGenerator I,idealCoeff_span _ (idealGenerator_ne_zero I hI),
      idealCoeff_span _ (idealGenerator_ne_zero I hI)]
    exact MulChar.pow_apply' χ.residue hn _

/-- Baseline ReflectedSource.unit_ideal with an arbitrary unit. -/
theorem unit_character_ideal (u : Oˣ) (I : Id) (hI : Supported I) :
    idealCoeff (HeckeUnitRows.character u) I = idealRowHom (u : O) I := by
  rw [← span_idealGenerator I,idealCoeff_span _ (idealGenerator_ne_zero I hI.1),
    HeckeUnitRows.elementCoeff_character]
  change (if Supported (Ideal.span {idealGenerator I}) then _ else 0) = _
  rw [span_idealGenerator,ite_eq_left hI]

theorem fixed_mask_one (I : Id) (hI : Supported I) : idealRowHom (fixedBadMask^6) I = 1 := by
  have hc : IsCoprime I (Ideal.span {fixedBadMask}) := by
    rw [← span_idealGenerator I,Ideal.isCoprime_span_singleton_iff]
    exact (fixedBadMask_coprime _ (by simpa only [span_idealGenerator] using hI)).symm
  rw [idealRowHom_sixth_mask fixedBadMask I hI,ite_eq_left hc]

def conductorConstant : ℕ := (HeckeUnitRows.character (1 : Oˣ)).modulus.absNorm *
  (Ideal.span {fixedBadMask}).absNorm * (Ideal.span {(72 : O)}).absNorm

structure Data (D : O) where
  character : Character
  modulus_bound : character.modulus.absNorm ≤ conductorConstant*(Ideal.span {D}).absNorm
  on_supported : ∀ I : Id, Supported I → idealCoeff character I = (idealRowHom D I)^2
  off_supported : ∀ I : Id, ¬Supported I → idealCoeff character I = 0

theorem data_exists (D : O) (hD : D ≠ 0) : Nonempty (Data D) := by
  let η₀ := HeckeUnitRows.character (1 : Oˣ)
  obtain ⟨ψ,hψ,hrow⟩ := exists_row_character_with_conductor η₀ fixedBadMask 1 D
    fixedBadMask_ne_zero one_ne_zero hD (dvd_mul_right _ _) (dvd_mul_left _ _)
  have hideal := idealCoeff_eq_row η₀ ψ fixedBadMask 1 D hrow
  have hon (I : Id) (hI : Supported I) : idealCoeff ψ I = idealRowHom D I := by
    rw [hideal I,unit_character_ideal _ I hI]
    simp only [Units.val_one,one_pow,mul_one,idealRowHom_one_supported I hI,one_mul,
      idealRowHom_argument_mul,fixed_mask_one I hI]
  have hoff (I : Id) (hI : ¬Supported I) : idealCoeff ψ I = 0 := by
    have hz := rowWeight_zero_of_not_supported η₀ fixedBadMask 1 D 0
      (dvd_mul_right _ _) (dvd_mul_left _ _) I hI
    change (idealCoeff η₀ I*idealRowHom (fixedBadMask^6*(1*D)) I)*
      (Ideal.absNorm I : ℂ)^(Complex.I*0) = 0 at hz
    rw [hideal I]
    simpa only [one_pow,mul_one,one_mul,mul_zero,Complex.cpow_zero] using hz
  refine ⟨⟨ψ.power 2,?_,?_,?_⟩⟩
  · simpa only [Character.power,rowConductorBound,Ideal.span_singleton_one,Ideal.absNorm_top,
      one_pow,one_mul,conductorConstant,η₀] using hψ
  · intro I hI
    rw [ideal_positive_power ψ 2 (by decide),hon I hI]
  · intro I hI
    rw [ideal_positive_power ψ 2 (by decide),hoff I hI,zero_pow (by decide : 2 ≠ 0)]

theorem product_modulus_bound (χ ψ : Character) :
    (χ.product ψ).modulus.absNorm ≤ χ.modulus.absNorm*ψ.modulus.absNorm := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul _ _

/-- Literal physical character, retaining both the cubic twist and natural
zeros. The displayed modulus is linear in N(D) and N(z). -/
theorem physical_character_exists (η : Character) (m D z : O)
    (hm : m ≠ 0) (hD : D ≠ 0) (hz : z ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character,
      χ.modulus.absNorm ≤ conductorConstant*η.modulus.absNorm*(Ideal.span {m}).absNorm*
        (Ideal.span {(72 : O)}).absNorm*(Ideal.span {D}).absNorm*(Ideal.span {z}).absNorm ∧
      (∀ I : Id, Supported I → idealCoeff χ I =
        idealCoeff η I*(idealRowHom D I)^2*idealRowHom (m^6) I*idealRowHom z I) ∧
      (∀ I : Id, ¬Supported I → idealCoeff χ I = 0) := by
  obtain ⟨r⟩ := data_exists D hD
  obtain ⟨χ,hχ,hrow⟩ := exists_row_character_with_conductor (η.product r.character) m 1 z
    hm one_ne_zero hz hmLam hm2
  have hid := idealCoeff_eq_row (η.product r.character) χ m 1 z hrow
  refine ⟨χ,?_,?_,?_⟩
  · have hp := product_modulus_bound η r.character
    have hb : (η.product r.character).modulus.absNorm ≤
        η.modulus.absNorm*(conductorConstant*(Ideal.span {D}).absNorm) :=
      hp.trans (Nat.mul_le_mul_left _ r.modulus_bound)
    apply hχ.trans
    simp only [rowConductorBound,Ideal.span_singleton_one,Ideal.absNorm_top,one_pow,one_mul]
    calc
      _ ≤ (η.modulus.absNorm*(conductorConstant*(Ideal.span {D}).absNorm))*
          (Ideal.span {m}).absNorm*(Ideal.span {(72 : O)}).absNorm*(Ideal.span {z}).absNorm :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb))
      _ = _ := by ring
  · intro I hI
    rw [hid I,idealCoeff_product,r.on_supported I hI]
    simp only [one_pow,mul_one,idealRowHom_argument_mul]
    ring
  · intro I hI
    rw [hid I,idealCoeff_product,r.off_supported I hI,mul_zero,zero_mul]

end
end Candidate.FourthPower.ReferenceCubicCharacter
