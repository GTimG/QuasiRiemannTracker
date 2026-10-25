/- Copyright (c) 2026 Sil. Apache-2.0.
Literal outer second-Poisson rows and THEIR exceptional partition.
The upstream partRows classifies A2 alone and is deliberately not reused.
The physical kernel remains at original K; its Fourier geometry uses A2*z.

-/
import Candidate.SilPrior.FourthPower.OuterFreshStructure
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ExceptionalReflection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshRows
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss ConcretePrimeRowBridge RayFourExpansion CenteredExceptionalProfile
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentChildRows CenteredMomentChildAssembly CenteredMomentSecondScaled
open CenteredMomentSecondChildProfile CenteredMomentSecondHeightFamily
open CenteredMomentSecondFamilyTransport CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalReflection
open CenteredMomentSecondLiveBlock CenteredMomentSecondPhysicalBlock
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentFirstSectors
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOuterActive
open MixedSupplierOriginalFrequency OuterFreshStructure
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

/-- The complete original multiplier, including its natural zeros. -/
def twist (f d : O) (ξ : RayCharacter) (I : Id) : ℂ :=
  (idealRowHom f I)^2 * (idealRowHom d I)^2 * rayCharacter ξ (primaryGenerator I)

theorem twist_mul (f d : O) (ξ : RayCharacter) (C I : Id) :
    twist f d ξ (C*I) = twist f d ξ C * twist f d ξ I := by
  simp only [twist,map_mul,primaryGenerator_mul,rayCharacter_mul,mul_pow]
  ring

theorem rays_product (ξ χ : RayCharacter) (a : O) :
    rayCharacter (ξ*χ) a = rayCharacter ξ a * rayCharacter χ a := rfl

theorem outer_column_extract (q : Data α) (x : Frozen q) (y : Selected q)
    (seed C I : Id) (ξ : RayCharacter) :
    outerColumn q x y seed ξ (C*I) =
      twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ C *
      commonColumn q x seed (C*I) *
      twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ I := by
  have he : outerColumn q x y seed ξ (C*I) =
      commonColumn q x seed (C*I) *
      twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ (C*I) := by
    unfold outerColumn twist
    ring
  rw [he,twist_mul]
  ring

/-- Exact child coefficient in actual_scaled_row_children. The full m^6
factor is retained pointwise; neither its natural zeros nor those of f,d
are removed. This identity holds also for zero Fourier frequency z. -/
theorem post_poisson_column (q : Data α) (x : Frozen q) (y : Selected q)
    (seed C L I : Id) (hI : Supported I) (τ : Character) (t : ℝ)
    (ξ χ : RayCharacter) (m A₂ z : O) :
    divisorCoefficient L (fun J : Id => primaryGenerator J)
      (movingCoefficient A₂ (fun J : Id => primaryGenerator J)
        (fun J => outerColumn q x y seed ξ (C*J) * rowWeight τ m 1 1 t J)) χ I *
        idealRowHom z I =
      (twist (primaryGenerator (frozenProduct q x))
          (primaryGenerator (selectedProduct q y)) ξ C *
        (if L ∣ I then commonColumn q x seed (C*I) else 0)) *
      (PrincipalPhysical.coefficient (childCharacter τ (ξ*χ)) m
        (A₂*(primaryGenerator (frozenProduct q x))^2*
          (primaryGenerator (selectedProduct q y))^2) z I *
        (Ideal.absNorm I : ℂ)^(Complex.I*t)) := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,
    outer_column_extract q x y seed C I ξ]
  rw [PrincipalCubic.coefficient_cubic _ m
      (A₂*(primaryGenerator (frozenProduct q x))^2)
      (primaryGenerator (selectedProduct q y)) z I hI,
    PrincipalCubic.coefficient_cubic _ m A₂
      (primaryGenerator (frozenProduct q x)) z I hI]
  simp only [PrincipalPhysical.coefficient,child_ideal_primary τ (ξ*χ) I hI,
    rays_product,twist,rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
    idealRowHom_argument_mul,one_mul,mul_one]
  split_ifs <;> ring

/-- Specialization to the actual height coefficient in physicalBlock.
The fixed bad mask is inserted only using its proved value one on support;
every other original puncture remains in commonColumn and the original τ. -/
theorem post_poisson_height_column (q : Data α) (x : Frozen q) (y : Selected q)
    (seed C L I : Id) (hI : Supported I) (τ : Character) (t : ℝ)
    (ξ χ : RayCharacter) (A₂ z : O) :
    divisorCoefficient L (fun J : Id => primaryGenerator J)
      (movingCoefficient A₂ (fun J : Id => primaryGenerator J)
        (fun J => outerColumn q x y seed ξ (C*J) * heightCoeff τ t J)) χ I *
        idealRowHom z I =
      (twist (primaryGenerator (frozenProduct q x))
          (primaryGenerator (selectedProduct q y)) ξ C *
        (if L ∣ I then commonColumn q x seed (C*I) else 0)) *
      (PrincipalPhysical.coefficient (childCharacter τ (ξ*χ)) fixedBadMask
        (A₂*(primaryGenerator (frozenProduct q x))^2*
          (primaryGenerator (selectedProduct q y))^2) z I *
        (Ideal.absNorm I : ℂ)^(Complex.I*t)) := by
  have hh := post_poisson_column q x y seed C L I hI τ t ξ χ fixedBadMask A₂ z
  simpa only [divisorCoefficient,movingCoefficient,
    ←heightCoeff_eq_fixed_rowWeight τ t I hI] using hh

/-- The genuine child character exists by the baseline constructor.
Its Fourier rows have exactly the combined fixed-inducing predicate.
No old radical/conductor bound for A2 alone is claimed for this character. -/
theorem exists_actual_character (τ : Character) (ξ χ : RayCharacter)
    (A₂ f d : O) (hA : A₂ ≠ 0) (hf : f ≠ 0) (hd : d ≠ 0) :
    ∃ σ : Character,
      σ.modulus.absNorm ≤ HeckeRowClosure.rowConductorBound
        (childCharacter τ (ξ*χ)) fixedBadMask 1 (A₂*f^2*d^2) ∧
      (∀ n, elementCoeff σ n = rowTwist
        (HeckeRowClosure.elementHom (childCharacter τ (ξ*χ)))
        fixedBadMask 1 (A₂*f^2*d^2) n) ∧
      (∀ I : Id, Supported I → ∀ t : ℝ,
        heightCoeff σ t I = heightCoeff τ t I * idealRowHom (A₂*f^2*d^2) I *
          rayCharacter (ξ*χ) (primaryGenerator I)) ∧
      (∀ Q : Id, ∀ z : O, FixedInducingRow σ Q fixedBadMask 1 z ↔
        FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask (A₂*f^2*d^2) z) := by
  obtain ⟨σ,hN,he,ht⟩ := exists_second_family_presentation τ (ξ*χ) (A₂*f^2*d^2)
    (mul_ne_zero (mul_ne_zero hA (pow_ne_zero _ hf)) (pow_ne_zero _ hd))
  exact ⟨σ,hN,he,ht,fun Q z =>
    fixedInducingRow_transport τ σ (ξ*χ) (A₂*f^2*d^2) he Q z⟩

/-- NEW outer exceptional rows. Upstream partRows would classify only
A2 and would not justify the fresh-D count. Geometry remains sourceRows,
because the original physical kernel still has frequency A2*z. -/
def outerRows (exceptional : Bool) (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ : RayCharacter) (Q : Id)
    (C E : Id) (U : Finset (CommonIndex C E)) (R : ℝ) : Finset O :=
  (sourceRows C E U R).filter (fun z => if exceptional then
    FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask
      (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
        (primaryGenerator (selectedProduct q y))^2) z else
    ¬FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask
      (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
        (primaryGenerator (selectedProduct q y))^2) z)

theorem outer_rows_nonzero (exceptional : Bool) (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ : RayCharacter) (Q C E : Id)
    (U : Finset (CommonIndex C E)) (R : ℝ) (z : O)
    (hz : z ∈ outerRows exceptional q x y τ ξ χ Q C E U R) : z ≠ 0 :=
  sourceRows_nonzero C E U R z (Finset.mem_filter.mp hz).1

/-- Classification is extracted from the actual new exceptional filter,
not asserted for an unrelated hypothetical row family. -/
theorem outer_rows_inducing (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ : RayCharacter) (Q C E : Id)
    (U : Finset (CommonIndex C E)) (R : ℝ) (z : O)
    (hz : z ∈ outerRows true q x y τ ξ χ Q C E U R) :
    FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask
      (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
        (primaryGenerator (selectedProduct q y))^2) z := by
  simpa using (Finset.mem_filter.mp hz).2

/-- One exceptional split works for every pair of finite reciprocity
rays on the left/right children, with their genuine z and -z frequencies. -/
theorem outer_rows_inducing_rays (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ χ₁ χ₂ : RayCharacter) (Q C E : Id)
    (hQ : Q ≤ Ideal.span {(72 : O)}) (U : Finset (CommonIndex C E))
    (R : ℝ) (z : O) (hz : z ∈ outerRows true q x y τ ξ χ Q C E U R) :
    FixedInducingRow (childCharacter τ (ξ*χ₁)) Q fixedBadMask
      (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
        (primaryGenerator (selectedProduct q y))^2) z ∧
    FixedInducingRow (childCharacter τ (ξ*χ₂)) Q fixedBadMask
      (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
        (primaryGenerator (selectedProduct q y))^2) (-z) := by
  have he := outer_rows_inducing q x y τ ξ χ Q C E U R z hz
  have hr := fixedInducingRow_reflected τ (ξ*χ) (ξ*χ₂) Q hQ fixedBadMask
    (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
      (primaryGenerator (selectedProduct q y))^2) z
    (dvd_mul_right _ _) (dvd_mul_left _ _) he
  refine ⟨?_,hr⟩
  simpa only [neg_neg] using fixedInducingRow_reflected τ (ξ*χ₂) (ξ*χ₁) Q hQ fixedBadMask
    (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
      (primaryGenerator (selectedProduct q y))^2) (-z)
    (dvd_mul_right _ _) (dvd_mul_left _ _) hr

theorem outer_rows_radius (exceptional : Bool) (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ : RayCharacter) (Q C E : Id)
    (U : Finset (CommonIndex C E)) (R : ℝ) (z : O)
    (hz : z ∈ outerRows exceptional q x y τ ξ χ Q C E U R) :
    (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤
      4*R/(normValue (commonFrequencyGenerator C E)*normValue (nonunitFrequencyGenerator C E U)) :=
  (liveRows_geometry C E U R _ z (Finset.mem_filter.mp hz).1).2.2.2

/-- Exact partition of the actual physical block, at the same original K.
Nothing about the old partRows predicate is used. -/
theorem physical_block_outer_split (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ χ : RayCharacter) (Q : Id)
    (S : Finset Id) (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (R : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    physicalBlock τ t S (outerColumn q x y seed ξ) C E hC hE U R
      (sourceRows C E U R) W K n =
      physicalBlock τ t S (outerColumn q x y seed ξ) C E hC hE U R
        (outerRows true q x y τ ξ χ Q C E U R) W K n +
      physicalBlock τ t S (outerColumn q x y seed ξ) C E hC hE U R
        (outerRows false q x y τ ξ χ Q C E U R) W K n := by
  simpa [outerRows] using
    physicalBlock_filter_split τ t S (outerColumn q x y seed ξ) C E hC hE U R
      (sourceRows C E U R) W K n
      (fun z => FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask
        (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
          (primaryGenerator (selectedProduct q y))^2) z)

/-- The concrete new exceptional rows satisfy supplier_count with no
extra row, forcing, valuation or radius-by-row assumption. The remaining
radius input is just the explicit scalar bound from the physical mesh. -/
theorem actual_exceptional_count (q : Data α) (x : Frozen q) (y : Selected q)
    (hy : Function.Injective y) (seed : Id) (τ : Character) (t : ℝ)
    (ξ χ : RayCharacter) (hw : selectedPositiveWeight q x y τ ≠ 0)
    (C E I J : Id) (U : Finset (CommonIndex C E))
    (hsector : (I,J) ∈ pairSector C E (supportedColumns (commonColumns q))
      (supportedColumns (commonColumns q)))
    (hpair : (outerColumn q x y seed ξ I * heightCoeff τ t I) *
      star (outerColumn q x y seed ξ J * heightCoeff τ t J) ≠ 0)
    (Q : Id) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (R Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hR : 4*R/(normValue (commonFrequencyGenerator C E)*
      normValue (nonunitFrequencyGenerator C E U)) ≤ Cr*Z^M) :
    ((outerRows true q x y τ ξ χ Q C E U R).card : ℝ) ≤
      (Ideal.absNorm (commonRadical Q Q) : ℝ)^(2/3 : ℝ)*
      (768*(6 : ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card*Cr^(1/6 : ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (oldIdeal C E U) : ℝ)-
          4*Real.logb Z (Ideal.absNorm (selectedProduct q y) : ℝ))/6)) := by
  exact supplier_count q x y hy seed τ t ξ (ξ*χ) hw C E I J U hsector hpair
    Q hQ0 hQ hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    (outerRows true q x y τ ξ χ Q C E U R)
    (outer_rows_nonzero true q x y τ ξ χ Q C E U R)
    (outer_rows_inducing q x y τ ξ χ Q C E U R) Z Cr M hZ hCr
    (fun z hz => (outer_rows_radius true q x y τ ξ χ Q C E U R z hz).trans hR)

end
end Candidate.SilPrior.FourthPower.OuterFreshRows
