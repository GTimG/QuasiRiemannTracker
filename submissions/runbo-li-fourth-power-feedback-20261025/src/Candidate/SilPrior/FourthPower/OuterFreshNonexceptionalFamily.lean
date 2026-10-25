/- Copyright (c) 2026 Sil. Apache-2.0.
Sharp fixed-f physical character family for the NEW outer partition.
D stays in the live row parameter, not the fixed conductor.

-/
import Candidate.SilPrior.FourthPower.OuterFreshRows
import Candidate.SilPrior.FourthPower.ReferenceCubicCharacter
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshNonexceptionalFamily
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge RayFourExpansion
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondFamilyTransport
open CenteredMomentExceptionalReflection CenteredMomentSecondChildProfile
open CenteredMomentChildAssembly CenteredMomentSecondScaled
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondRadicalBudget CenteredMomentSectorLocalization
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOuterActive
open OuterFreshStructure OuterFreshRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

/-- Only equality of the full row parameter is used. This does not
remove natural-zero masks or change the fixed inducing modulus. -/
theorem inducing_parameter_congr (η : Character) (Q : Id) (m A z B w : O)
    (h : A*z=B*w) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q m B w := by
  unfold FixedInducingRow
  rw [h]

/-- Multiplying by the actual cubic character is exactly inserting f²
in the sextic row parameter. Equality also holds on unsupported elements. -/
theorem cubic_product_row (η : Character) (f : O) (r : ReferenceCubicCharacter.Data f)
    (A z n : O) :
    rowTwist (elementHom (η.product r.character)) fixedBadMask 1 (A*z) n=
      rowTwist (elementHom η) fixedBadMask 1 ((A*f^2)*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hn0 : n≠0 := by
      intro he
      apply hn.1
      simp only [he,Ideal.span_singleton_zero,Ideal.zero_eq_bot]
    have hr : elementCoeff r.character n=(idealRowHom f (Ideal.span {n}))^2 := by
      rw [←idealCoeff_span r.character hn0]
      exact r.on_supported _ hn
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn,
      rowTwist_extract_sixth_mask _ _ _ _ n hn]
    change elementCoeff (η.product r.character) n*coprimalityMask fixedBadMask n*
      idealRowHom (1^4*(A*z)) (Ideal.span {n})=_
    rw [elementCoeff_product,hr]
    simp only [one_pow,one_mul,idealRowHom_argument_mul,
      idealRowHom_argument_pow f 2 (Ideal.span {n}) hn]
    rw [show elementHom η n=elementCoeff η n from rfl]
    ring
  · exact (rowTwist_zero_of_not_supported (elementHom (η.product r.character))
        fixedBadMask 1 (A*z) n (dvd_mul_right _ _) (dvd_mul_left _ _) hn).trans
      (rowTwist_zero_of_not_supported (elementHom η) fixedBadMask 1 ((A*f^2)*z) n
        (dvd_mul_right _ _) (dvd_mul_left _ _) hn).symm

theorem cubic_product_inducing (η : Character) (f : O) (r : ReferenceCubicCharacter.Data f)
    (Q : Id) (A z : O) :
    FixedInducingRow (η.product r.character) Q fixedBadMask A z ↔
      FixedInducingRow η Q fixedBadMask (A*f^2) z := by
  unfold FixedInducingRow
  simp only [cubic_product_row η f r A z]

/-- A sharp character family, chosen before D, height, frequency pool,
or source coefficient. The sole moving cubic cost in its conductor is f.
All physical identities are proved, not assumptions on the target energy. -/
structure SharpFamily (τ : Character) (f : Id) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character) : Prop where
  height_eq : ∀χ I,Supported I→(IsCoprime C I ∨ IsCoprime E I)→∀t,
    heightCoeff (ψ χ) t I=heightCoeff τ t I*idealRowHom (oldMoving C E U) I*
      (idealRowHom (primaryGenerator f) I)^2*rayCharacter (ξ*χ) (primaryGenerator I)
  inducing_iff : ∀χ Q D z,D≠0 → z≠0 →
    (FixedInducingRow (ψ χ) Q fixedBadMask (D^2) z ↔
      FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask
        (oldMoving C E U*(primaryGenerator f)^2*D^2) z)
  physical_budget : ∀(t : ℝ)(S : Finset Id)(β : Id→ℂ)(R : ℝ)(rows : Finset O)
      (W : 𝓢(ℝ,ℂ))(K : ℝ),0<K→∀n : Fin 4→ℤ,
    physicalBlock τ t S β C E hC hE U R rows W K n≠0→∀χ,
      (ψ χ).modulus.absNorm≤
        (τ.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
          (Ideal.span {nonunitFrequencyGenerator C E U}).absNorm)*
          (ReferenceCubicCharacter.conductorConstant*f.absNorm) ∧
      ∀Z : ℝ,1<Z→∀z∈liveRows C E U R rows,
        Real.logb Z (normValue z)+Real.logb Z ((ψ χ).modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (τ.modulus.absNorm:ℝ)-
            Real.logb Z (normValue (commonFrequencyGenerator C E))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))+
            Real.logb Z (ReferenceCubicCharacter.conductorConstant*f.absNorm:ℝ)

theorem exists_sharp_family (τ : Character) (f : Id) (hf : Supported f) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E) (hCE : primeSupport C=primeSupport E)
    (U : Finset (CommonIndex C E)) :
    ∃ψ : RayCharacter→Character,SharpFamily τ f ξ C E hC hE U ψ := by
  obtain ⟨σ,hσ⟩ := exists_exceptional_family τ C E hC hE hCE U
  obtain ⟨r⟩ := ReferenceCubicCharacter.data_exists (primaryGenerator f)
    (supported_primaryGenerator_ne_zero f hf)
  let ψ := fun χ=> (σ (ξ*χ)).product r.character
  have hr : r.character.modulus.absNorm≤ReferenceCubicCharacter.conductorConstant*f.absNorm := by
    simpa only [primary_span_supported f hf] using r.modulus_bound
  refine ⟨ψ,⟨?_,?_,?_⟩⟩
  · intro χ I hI hcop t
    have he := hσ.height_eq (ξ*χ) I hI hcop t
    change idealCoeff ((σ (ξ*χ)).product r.character) I*
      (I.absNorm:ℂ)^(Complex.I*t)=_
    rw [idealCoeff_product,r.on_supported I hI]
    change (idealCoeff (σ (ξ*χ)) I*(idealRowHom (primaryGenerator f) I)^2)*
      (I.absNorm:ℂ)^(Complex.I*t)=_
    calc
      _=heightCoeff (σ (ξ*χ)) t I*(idealRowHom (primaryGenerator f) I)^2 := by
        unfold heightCoeff
        ring
      _=_ := by rw [he]; unfold oldMoving; ring
  · intro χ Q D z hD hz
    have hfreq : (primaryGenerator f)^2*D^2*z≠0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (supported_primaryGenerator_ne_zero f hf))
        (pow_ne_zero _ hD)) hz
    change FixedInducingRow ((σ (ξ*χ)).product r.character) Q fixedBadMask (D^2) z↔_
    calc
      _↔FixedInducingRow (σ (ξ*χ)) Q fixedBadMask (D^2*(primaryGenerator f)^2) z :=
        cubic_product_inducing (σ (ξ*χ)) (primaryGenerator f) r Q (D^2) z
      _↔FixedInducingRow (σ (ξ*χ)) Q fixedBadMask 1 ((primaryGenerator f)^2*D^2*z) :=
        inducing_parameter_congr _ _ _ _ _ _ _ (by ring)
      _↔FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask (oldMoving C E U)
          ((primaryGenerator f)^2*D^2*z) :=
        (hσ.inducing_iff (ξ*χ) Q fixedBadMask _ fixedBadMask_ne_zero hfreq
          (dvd_mul_right _ _) (dvd_mul_left _ _)).symm
      _↔_ := inducing_parameter_congr _ _ _ _ _ _ _ (by ring)
  · intro t S β R rows W K hK n hne χ
    have hp := hσ.physical_budget t S β R rows W K hK n hne (ξ*χ)
    have hproduct := ReferenceCubicCharacter.product_modulus_bound (σ (ξ*χ)) r.character
    have hmod : (ψ χ).modulus.absNorm≤
        (σ (ξ*χ)).modulus.absNorm*(ReferenceCubicCharacter.conductorConstant*f.absNorm) :=
      hproduct.trans (Nat.mul_le_mul_left _ hr)
    refine ⟨hmod.trans (Nat.mul_le_mul_right _ hp.1),?_⟩
    intro Z hZ z hz
    have hσpos : 0<((σ (ξ*χ)).modulus.absNorm:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (Ideal.absNorm_eq_zero_iff.not.mpr (σ (ξ*χ)).modulus_ne_bot)
    have hψpos : 0<((ψ χ).modulus.absNorm:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (ψ χ).modulus_ne_bot)
    have hfpos : 0<(ReferenceCubicCharacter.conductorConstant*f.absNorm:ℝ) := by
      have hh : 0<r.character.modulus.absNorm := Nat.pos_of_ne_zero
        (Ideal.absNorm_eq_zero_iff.not.mpr r.character.modulus_ne_bot)
      exact_mod_cast hh.trans_le hr
    have hmodR : ((ψ χ).modulus.absNorm:ℝ)≤
        ((σ (ξ*χ)).modulus.absNorm:ℝ)*(ReferenceCubicCharacter.conductorConstant*f.absNorm:ℝ) := by
      exact_mod_cast hmod
    have hlog := (Real.logb_le_logb hZ hψpos (mul_pos hσpos hfpos)).mpr hmodR
    rw [Real.logb_mul hσpos.ne' hfpos.ne'] at hlog
    have hwidth := hp.2 Z hZ z hz
    linarith

/-- For actual retained selected rows, the new complement is exactly
noninduction of the sharp fixed-f family at live parameter D². -/
theorem actual_outer_noninducing (q : Data ι) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ : RayCharacter) (Q C E : Id)
    (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (hD : Supported (selectedProduct q y)) (R : ℝ) (z : O)
    (hz : z∈outerRows false q x y τ ξ χ Q C E U R) :
    z≠0 ∧ ¬FixedInducingRow (ψ χ) Q fixedBadMask
      ((primaryGenerator (selectedProduct q y))^2) z := by
  have hz0 := outer_rows_nonzero false q x y τ ξ χ Q C E U R z hz
  have hn : ¬FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask
      (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
        (primaryGenerator (selectedProduct q y))^2) z := by
    simpa only [Bool.false_eq_true,ite_false] using
      (Finset.mem_filter.mp hz).2
  exact ⟨hz0,fun h=>hn ((hψ.inducing_iff χ Q (primaryGenerator (selectedProduct q y)) z
    (supported_primaryGenerator_ne_zero _ hD) hz0).mp h)⟩

/-- Every reciprocity ray on both sides uses the SAME new complement.
The right child retains its genuine reflected frequency -z. -/
theorem actual_outer_noninducing_rays (q : Data ι) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ χ₁ χ₂ : RayCharacter) (Q C E : Id) (hQ : Q≤Ideal.span {(72:O)})
    (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (hD : Supported (selectedProduct q y)) (R : ℝ) (z : O)
    (hz : z∈outerRows false q x y τ ξ χ Q C E U R) :
    z≠0 ∧
      ¬FixedInducingRow (ψ χ₁) Q fixedBadMask ((primaryGenerator (selectedProduct q y))^2) z ∧
      ¬FixedInducingRow (ψ χ₂) Q fixedBadMask ((primaryGenerator (selectedProduct q y))^2) (-z) := by
  have hz0 := outer_rows_nonzero false q x y τ ξ χ Q C E U R z hz
  have hD0 := supported_primaryGenerator_ne_zero _ hD
  let A := oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
    (primaryGenerator (selectedProduct q y))^2
  have hn : ¬FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask A z := by
    simpa only [A,Bool.false_eq_true,ite_false] using (Finset.mem_filter.mp hz).2
  refine ⟨hz0,?_,?_⟩
  · intro h
    have h₁ := (hψ.inducing_iff χ₁ Q (primaryGenerator (selectedProduct q y)) z hD0 hz0).mp h
    have h₂ := fixedInducingRow_reflected τ (ξ*χ₁) (ξ*χ) Q hQ fixedBadMask A z
      (dvd_mul_right _ _) (dvd_mul_left _ _) h₁
    have h₃ := fixedInducingRow_reflected τ (ξ*χ) (ξ*χ) Q hQ fixedBadMask A (-z)
      (dvd_mul_right _ _) (dvd_mul_left _ _) h₂
    exact hn (by simpa only [neg_neg] using h₃)
  · intro h
    have h₁ := (hψ.inducing_iff χ₂ Q (primaryGenerator (selectedProduct q y)) (-z)
      hD0 (neg_ne_zero.mpr hz0)).mp h
    have h₂ := fixedInducingRow_reflected τ (ξ*χ₂) (ξ*χ) Q hQ fixedBadMask A (-z)
      (dvd_mul_right _ _) (dvd_mul_left _ _) h₁
    exact hn (by simpa only [neg_neg] using h₂)

/-- Actual post-Poisson coefficient in the sharp family. Its moving D
factor stays explicit, and all common, divisor and original source masks
remain in the unchanged commonColumn. -/
theorem actual_child_coefficient (q : Data ι) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ : RayCharacter) (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (seed G L I : Id) (hI : Supported I) (hcop : IsCoprime C I ∨ IsCoprime E I)
    (t : ℝ) (z : O) :
    divisorCoefficient L (fun J : Id=>primaryGenerator J)
      (movingCoefficient (oldMoving C E U) (fun J : Id=>primaryGenerator J)
        (fun J=>MixedSupplierOriginalFrequency.outerColumn q x y seed ξ (G*J)*heightCoeff τ t J)) χ I*
      idealRowHom z I=
      (twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ G*
        (if L∣I then commonColumn q x seed (G*I) else 0))*
        (heightCoeff (ψ χ) t I*(idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
          idealRowHom z I) := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,
    outer_column_extract q x y seed G I ξ,hψ.height_eq χ I hI hcop t]
  simp only [twist,rays_product]
  split_ifs <;> ring

end
end Candidate.SilPrior.FourthPower.OuterFreshNonexceptionalFamily
