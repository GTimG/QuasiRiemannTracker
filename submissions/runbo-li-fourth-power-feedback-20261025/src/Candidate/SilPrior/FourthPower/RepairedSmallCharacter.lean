/- Copyright (c) 2026 Sil. Apache-2.0.
Exact empty-selection cubic character and exceptional partition. Natural
zeros and the common-height factors are retained pointwise.

-/
import Candidate.SilPrior.FourthPower.OuterFreshRows
import Candidate.SilPrior.FourthPower.MixedFirstReferenceDispatch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RepairedSmallCharacter
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss ConcretePrimeRowBridge RayFourExpansion CenteredExceptionalProfile HeckeRowClosure
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentSecondChildProfile CenteredMomentSecondEnergySplit
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOriginalFrequency
open OuterFreshRows OuterFreshStructure MixedFirstReferenceDispatch
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem empty_selected_product (q : Data ι) (hJ : q.J=∅) (y : Selected q) :
    selectedProduct q y=1 := by
  unfold selectedProduct
  apply Finset.prod_eq_one
  intro j hj
  exact False.elim (by simpa only [hJ,Finset.notMem_empty] using j.property)

/-- The ideal-level identity carries all original natural zeros. -/
theorem child_ideal_cubic (τ σ : Character) (ξ χ : RayCharacter) (f : O)
    (hσ : ∀I : Id,Supported I →
      idealCoeff σ I=idealCoeff τ I*(idealRowHom f I)^2*rayCharacter ξ (primaryGenerator I))
    (I : Id) (hI : Supported I) :
    idealCoeff (childCharacter σ χ) I=
      idealCoeff (childCharacter τ (ξ*χ)) I*(idealRowHom f I)^2 := by
  rw [child_ideal_primary σ χ I hI,hσ I hI,child_ideal_primary τ (ξ*χ) I hI,rays_product]
  ring

theorem all_element_cubic_row (τ σ : Character) (ξ χ : RayCharacter) (f : O)
    (hσ : ∀I : Id,Supported I →
      idealCoeff σ I=idealCoeff τ I*(idealRowHom f I)^2*rayCharacter ξ (primaryGenerator I))
    (m A z n : O) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    rowTwist (elementHom (childCharacter σ χ)) m 1 (A*z) n=
      rowTwist (elementHom (childCharacter τ (ξ*χ))) m 1 (A*f^2*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hn0 : n≠0 := by
      intro he
      exact hn.1 (by simp only [he,Ideal.span_singleton_zero,Ideal.zero_eq_bot])
    have hc : elementCoeff (childCharacter σ χ) n=
        elementCoeff (childCharacter τ (ξ*χ)) n*(idealRowHom f (Ideal.span {n}))^2 := by
      rw [←idealCoeff_span (childCharacter σ χ) hn0,
        ←idealCoeff_span (childCharacter τ (ξ*χ)) hn0]
      exact child_ideal_cubic τ σ ξ χ f hσ (Ideal.span {n}) hn
    rw [rowTwist_extract_sixth_mask _ m 1 (A*z) n hn,
      rowTwist_extract_sixth_mask _ m 1 (A*f^2*z) n hn]
    change elementCoeff (childCharacter σ χ) n*coprimalityMask m n*
      idealRowHom (1^4*(A*z)) (Ideal.span {n})=
        elementCoeff (childCharacter τ (ξ*χ)) n*coprimalityMask m n*
          idealRowHom (1^4*(A*f^2*z)) (Ideal.span {n})
    rw [hc]
    simp only [one_pow,one_mul,idealRowHom_argument_mul,
      idealRowHom_argument_pow f 2 (Ideal.span {n}) hn]
    ring
  · exact (rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn).trans
      (rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn).symm

theorem inducing_iff (τ σ : Character) (ξ χ : RayCharacter) (f : O)
    (hσ : ∀I : Id,Supported I →
      idealCoeff σ I=idealCoeff τ I*(idealRowHom f I)^2*rayCharacter ξ (primaryGenerator I))
    (Q : Id) (m A z : O) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    FixedInducingRow (childCharacter σ χ) Q m A z ↔
      FixedInducingRow (childCharacter τ (ξ*χ)) Q m (A*f^2) z := by
  constructor
  · rintro ⟨χ₁,ψ,hprim,hind,hQ,hrow⟩
    exact ⟨χ₁,ψ,hprim,hind,hQ,fun n =>
      (hrow n).trans (all_element_cubic_row τ σ ξ χ f hσ m A z n hmLam hm2)⟩
  · rintro ⟨χ₁,ψ,hprim,hind,hQ,hrow⟩
    exact ⟨χ₁,ψ,hprim,hind,hQ,fun n =>
      (hrow n).trans (all_element_cubic_row τ σ ξ χ f hσ m A z n hmLam hm2).symm⟩

/-- The new sigma has a LINEAR frozen-product conductor; it is chosen
before both physical heights and the later second reciprocity ray.
The final Iff is explicitly INSIDE both divisibility implications. This
corrects the formerly unparenthesized header's parsing; it adds no new
hypothesis beyond the two already displayed divisibility gates. -/
theorem exists_supplier_character (τ : Character) (f : Id) (hf : Supported f)
    (ξ : RayCharacter) :
    ∃σ : Character,
      σ.modulus.absNorm≤τ.modulus.absNorm*(ReferenceCubicCharacter.conductorConstant*f.absNorm)*
        (Ideal.span {(12:O)}).absNorm ∧
      (∀I : Id,Supported I → ∀t : ℝ,
        heightCoeff σ t I=heightCoeff τ t I*(idealRowHom (primaryGenerator f) I)^2*
          rayCharacter ξ (primaryGenerator I)) ∧
      (∀χ : RayCharacter,∀Q : Id,∀m A z : O,goodLambda∣m → (2:O)∣m →
        (FixedInducingRow (childCharacter σ χ) Q m A z ↔
          FixedInducingRow (childCharacter τ (ξ*χ)) Q m (A*(primaryGenerator f)^2) z)) := by
  obtain ⟨σ,hmod,hheight⟩ := common_height_character τ f hf ξ
  have hon (I : Id) (hI : Supported I) :
      idealCoeff σ I=idealCoeff τ I*(idealRowHom (primaryGenerator f) I)^2*
        rayCharacter ξ (primaryGenerator I) := by
    simpa only [heightCoeff,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hheight I hI 0
  exact ⟨σ,hmod,hheight,fun χ Q m A z hmLam hm2 =>
    inducing_iff τ σ ξ χ (primaryGenerator f) hon Q m A z hmLam hm2⟩

/-- The sourceRows geometry is unchanged; only its exact predicate is
transported. The finite common-height coefficients are not erased. -/
theorem empty_outer_rows (q : Data ι) (x : Frozen q) (y : Selected q)
    (hy : selectedProduct q y=1) (τ σ : Character) (ξ χ : RayCharacter)
    (hσ : ∀I : Id,Supported I →
      idealCoeff σ I=idealCoeff τ I*(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
        rayCharacter ξ (primaryGenerator I))
    (exceptional : Bool) (Q C D : Id) (U : Finset (CommonIndex C D)) (R : ℝ) :
    partRows exceptional σ χ Q fixedBadMask C D U R=
      outerRows exceptional q x y τ ξ χ Q C D U R := by
  have hi (z : O) := inducing_iff τ σ ξ χ (primaryGenerator (frozenProduct q x)) hσ
    Q fixedBadMask (oldMoving C D U) z (dvd_mul_right _ _) (dvd_mul_left _ _)
  cases exceptional
  · rw [partRows_false]
    unfold outerRows
    simp only [Bool.false_eq_true,ite_false,hy,primaryGenerator_one,one_pow,mul_one]
    apply Finset.filter_congr
    intro z hz
    exact not_congr (hi z)
  · change (sourceRows C D U R).filter (fun z =>
        FixedInducingRow (childCharacter σ χ) Q fixedBadMask (oldMoving C D U) z)=
      (sourceRows C D U R).filter (fun z =>
        FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask
          (oldMoving C D U*(primaryGenerator (frozenProduct q x))^2*
            (primaryGenerator (selectedProduct q y))^2) z)
    simp only [hy,primaryGenerator_one,one_pow,mul_one]
    apply Finset.filter_congr
    intro z hz
    exact hi z

end
end Candidate.SilPrior.FourthPower.RepairedSmallCharacter
