/- Copyright (c) 2026 Sil. Apache-2.0.
The common-column reference for actual physical Hecke characters. The
characters are constructed with the linear cubic conductor bound, and their
unsupported coefficients vanish. No hypothetical character family is assumed.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferenceProductEnergy
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferenceCubicCharacter

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceHeckeProducts
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge
open ReferenceProductEnergy ReferenceCubicCharacter
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

def fixedCoefficient (η : Character) (m D : O) (I : Id) : ℂ :=
  idealCoeff η I*(idealRowHom D I)^2*idealRowHom (m^6) I

theorem fixed_coefficient_norm (η : Character) (m D : O) (I : Id) :
    ‖fixedCoefficient η m D I‖ ≤ 1 := by
  rw [fixedCoefficient,norm_mul,norm_mul,norm_pow]
  have hh := mul_le_mul
    (mul_le_mul (idealCoeff_norm_le_one η I)
      (pow_le_one₀ (norm_nonneg _) (idealRowHom_norm D I))
      (pow_nonneg (norm_nonneg _) 2) zero_le_one)
    (idealRowHom_norm (m^6) I) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1*1)
  simpa only [one_mul] using hh

theorem finite_factor_identity (η χ : Character) (m D x : O)
    (hon : ∀ I : Id, Supported I → idealCoeff χ I =
      idealCoeff η I*(idealRowHom D I)^2*idealRowHom (m^6) I*idealRowHom x I)
    (hoff : ∀ I : Id, ¬Supported I → idealCoeff χ I = 0)
    (pool : Finset Id) (a : Id → ℂ) :
    (∑ I ∈ pool, a I*idealCoeff χ I) =
      ∑ I ∈ pool.filter Supported, (a I*fixedCoefficient η m D I)*idealRowHom x I := by
  have he : (∑ I ∈ pool.filter Supported, a I*idealCoeff χ I) =
      ∑ I ∈ pool, a I*idealCoeff χ I := by
    apply Finset.sum_filter_of_ne
    intro I _ hn
    by_contra hI
    exact hn (by rw [hoff I hI,mul_zero])
  rw [← he]
  apply Finset.sum_congr rfl
  intro I hI
  rw [hon I (Finset.mem_filter.mp hI).2]
  unfold fixedCoefficient
  ring

theorem identified_product_reference (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y N T : ℝ),
      1 ≤ Z → 0 ≤ R → 1 ≤ N → 0 ≤ T →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 → N ≤ Z^v → N ≤ Z^y*T →
      ∀ (η : Character) (m D : O) (rows : Finset O) (χ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
        ∀ (pool : α → Finset Id) (a : α → Id → ℂ) (H B : α → ℝ),
        (∀ i, 0 ≤ B i) → (∏ i, H i) ≤ N →
        (∀ i I, I ∈ pool i → (Ideal.absNorm I : ℝ) ≤ H i) →
        (∀ i I, I ∈ pool i → ‖a i I‖ ≤ B i/Real.sqrt (Ideal.absNorm I : ℝ)) →
        (∑ x : rows, ‖∏ i, ∑ I ∈ pool i, a i I*idealCoeff (χ x) I‖^2) ≤
          C*Z^(R+ε)*(3+T^(1/3 : ℝ))*(∏ i, B i)^2 := by
  obtain ⟨C,hC,hb⟩ := two_scale_product (α:=α) ε L hε hL
  refine ⟨C,hC,?_⟩
  intro Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D rows χ hon hoff hr
  intro pool a H B hB hHN hp ha
  have hcoeff (i : α) (I : Id) (hI : I ∈ (pool i).filter Supported) :
      ‖a i I*fixedCoefficient η m D I‖ ≤ B i/Real.sqrt (Ideal.absNorm I : ℝ) := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (fixed_coefficient_norm η m D I)).trans
      (ha i I (Finset.mem_filter.mp hI).1)
  have he := hb Z R v y N T hZ hR hN hT hcap hv hy hmax href rows
    (fun i => (pool i).filter Supported) (fun i I => a i I*fixedCoefficient η m D I) H B hB hHN hr
    (fun i I hI => ⟨(Finset.mem_filter.mp hI).2,hp i I (Finset.mem_filter.mp hI).1⟩) hcoeff
  have hsame (x : rows) :
      (∏ i, ∑ I ∈ pool i, a i I*idealCoeff (χ x) I) =
      ∏ i, ∑ I ∈ (pool i).filter Supported, (a i I*fixedCoefficient η m D I)*idealRowHom x.val I := by
    apply Finset.prod_congr rfl
    intro i _
    exact finite_factor_identity η (χ x) m D x.val (hon x) (hoff x) (pool i) (a i)
  simp_rw [hsame]
  simpa only [Finset.sum_coe_sort rows
    (fun x : O => ‖∏ i, ∑ I ∈ (pool i).filter Supported,
      (a i I*fixedCoefficient η m D I)*idealRowHom x I‖^2)] using he

/-- The coefficient identities in the preceding theorem have actual physical
character witnesses, with a conductor linear in the cubic parameter. -/
theorem physical_product_reference (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y N T : ℝ),
      1 ≤ Z → 0 ≤ R → 1 ≤ N → 0 ≤ T →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 → N ≤ Z^v → N ≤ Z^y*T →
      ∀ (η : Character) (m D : O), m ≠ 0 → D ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
      ∀ (rows : Finset O), (∀ x ∈ rows, x ≠ 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      ∃ χ : rows → Character,
        (∀ x, (χ x).modulus.absNorm ≤ conductorConstant*η.modulus.absNorm*(Ideal.span {m}).absNorm*
          (Ideal.span {(72 : O)}).absNorm*(Ideal.span {D}).absNorm*(Ideal.span {x.val}).absNorm) ∧
        (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D I*idealRowHom x.val I) ∧
        (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) ∧
        ∀ (pool : α → Finset Id) (a : α → Id → ℂ) (H B : α → ℝ),
        (∀ i, 0 ≤ B i) → (∏ i, H i) ≤ N →
        (∀ i I, I ∈ pool i → (Ideal.absNorm I : ℝ) ≤ H i) →
        (∀ i I, I ∈ pool i → ‖a i I‖ ≤ B i/Real.sqrt (Ideal.absNorm I : ℝ)) →
        (∑ x : rows, ‖∏ i, ∑ I ∈ pool i, a i I*idealCoeff (χ x) I‖^2) ≤
          C*Z^(R+ε)*(3+T^(1/3 : ℝ))*(∏ i, B i)^2 := by
  obtain ⟨C,hC,hb⟩ := identified_product_reference (α:=α) ε L hε hL
  refine ⟨C,hC,?_⟩
  intro Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D hm hD hmLam hm2 rows hn hr
  choose χ hχ hon hoff using fun x : rows =>
    physical_character_exists η m D x.val hm hD (hn x.val x.property) hmLam hm2
  exact ⟨χ,hχ,hon,hoff,hb Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D rows χ hon hoff hr⟩

end
end Candidate.FourthPower.ReferenceHeckeProducts
