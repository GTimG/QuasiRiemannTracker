/- Copyright (c) 2026 Sil. Apache-2.0.
Actual old+fresh arithmetic at the ORIGINAL outer frequency. The old
ideal and moving parameter are the literal second canonical ones. Their
coprimality and valuation gates are derived from actual nonzero source
coefficients; no count, energy, or source estimate is assumed.

-/
import Candidate.Feedback.FourthPower.OuterFreshCount
import Candidate.Feedback.FourthPower.MixedSupplierOriginalFrequency

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.OuterFreshStructure
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge UniqueFactorizationMonoid RayFourExpansion CompletedGauss
open CenteredExceptionalCount CenteredExceptionalProfile CenteredMomentForcing
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondExceptionalCount
open CenteredMomentPartitionNorm CenteredMomentChildRows CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical
open CenteredMomentFirstSectors CenteredMomentCompleteCommon MixedSupplierCanonical
open MixedSupplierFourthRow MixedSupplierReconstruction MixedSupplierOuterActive MixedSupplierSource
open MixedSupplierOriginalFrequency
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- The inherited forcing ideal, with the second partition U unchanged. -/
def oldIdeal (C E : Id) (U : Finset (CommonIndex C E)) : Id :=
  forcingIdeal (fun P : CommonIndex C E => P.val)
    (leftExponent C E) (rightExponent C E) (nonunitPartitionSet C E U)

/-- The actual second Poisson common/nonunit multiplier, before f²D². -/
def oldMoving (C E : Id) (U : Finset (CommonIndex C E)) : O :=
  commonFrequencyGenerator C E * nonunitFrequencyGenerator C E U

theorem common_ideal_prime (C E : Id) (P : CommonIndex C E) : Prime P.val :=
  prime_of_normalized_factor _
    (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

theorem old_moving_span (C E : Id) (hC : Supported C)
    (U : Finset (CommonIndex C E)) :
    Ideal.span {oldMoving C E U} = movingIdeal (fun P : CommonIndex C E => P.val)
      (leftExponent C E) (rightExponent C E) (nonunitPartitionSet C E U) := by
  rw [oldMoving,←Ideal.span_singleton_mul_span_singleton,
    commonFrequencyGenerator_span C E hC,nonunitFrequencyGenerator_span]
  simp only [commonIdeal,unitIdeal,commonPrime_span C E hC,movingIdeal]

theorem old_moving_ne_zero (C E : Id) (hC : Supported C)
    (U : Finset (CommonIndex C E)) : oldMoving C E U ≠ 0 :=
  mul_ne_zero (commonFrequencyGenerator_ne_zero C E hC)
    (nonunitFrequencyGenerator_ne_zero C E hC U)

theorem old_squarefree (C E : Id) (U : Finset (CommonIndex C E)) :
    Squarefree (oldIdeal C E U) :=
  forcingIdeal_squarefree (fun P : CommonIndex C E => P.val)
    (common_ideal_prime C E) Subtype.val_injective _ _ _

/-- No inherited residue is an input: it follows from the two exponents
equal to one on the literal second canonical forcing set. -/
theorem old_valuation (C E : Id) (hC : Supported C)
    (U : Finset (CommonIndex C E)) (P : Id)
    (hP : P ∈ normalizedFactors (oldIdeal C E U)) :
    valuation (Ideal.span {oldMoving C E U}) P % 6 = 2 := by
  obtain ⟨i,hi,rfl⟩ := forcing_prime_mem (fun i : CommonIndex C E => i.val)
    (common_ideal_prime C E) (leftExponent C E) (rightExponent C E)
    (nonunitPartitionSet C E U) P hP
  rw [old_moving_span C E hC U,
    forcing_valuation_two _ (common_ideal_prime C E) Subtype.val_injective
      (leftExponent C E) (rightExponent C E) (nonunitPartitionSet C E U) i hi]

theorem old_coprime_of_left (C E : Id) (U : Finset (CommonIndex C E))
    (I : Id) (hc : IsCoprime C I) : IsCoprime (oldIdeal C E U) I := by
  unfold oldIdeal forcingIdeal
  apply IsCoprime.prod_left
  intro P _
  exact hc.of_isCoprime_of_dvd_left (common_prime_dvd_left C E P)

theorem old_moving_coprime_of_left (C E : Id) (hC : Supported C)
    (U : Finset (CommonIndex C E)) (I : Id) (hc : IsCoprime C I) :
    IsCoprime (Ideal.span {oldMoving C E U}) I := by
  rw [old_moving_span C E hC U,movingIdeal]
  apply IsCoprime.mul_left
  · apply IsCoprime.prod_left
    intro P _
    exact (hc.of_isCoprime_of_dvd_left (common_prime_dvd_left C E P)).pow_left
  · apply IsCoprime.prod_left
    intro P _
    exact hc.of_isCoprime_of_dvd_left (common_prime_dvd_left C E P)

/-- This uses only support at 2 and 3. It says nothing about coprimality
with the actual inducing Q; those primes are still filtered by the count. -/
theorem supported_child_coprime (τ : Character) (ρ : RayCharacter)
    (I : Id) (hI : Supported I) (hc : IsCoprime τ.modulus I) :
    IsCoprime (childCharacter τ ρ).modulus I :=
  childCharacter_coprime τ ρ (Ideal.span {(72 : O)}) I le_rfl
    (supported_coprime_72 I hI) hc

theorem supported_prime_gates (τ : Character) (ρ : RayCharacter)
    (I : Id) (hI : Supported I) (hc : IsCoprime τ.modulus I)
    (P : Id) (hP : P ∈ normalizedFactors I) :
    goodLambda ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime (childCharacter τ ρ).modulus P := by
  have hp := supported_factors_good I hI P hP
  let : P.IsMaximal := hp.1
  obtain ⟨hl,h2⟩ := hp.2
  exact ⟨hl,good_odd_prime_two_not_mem P h2,
    (supported_child_coprime τ ρ I hI hc).of_isCoprime_of_dvd_right
      (dvd_of_mem_normalizedFactors hP)⟩

theorem old_prime_gates (τ : Character) (ρ : RayCharacter)
    (C E : Id) (hC : Supported C) (hc : IsCoprime τ.modulus C)
    (U : Finset (CommonIndex C E)) (P : Id)
    (hP : P ∈ normalizedFactors (oldIdeal C E U)) :
    goodLambda ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime (childCharacter τ ρ).modulus P := by
  obtain ⟨i,_,rfl⟩ := forcing_prime_mem (fun i : CommonIndex C E => i.val)
    (common_ideal_prime C E) (leftExponent C E) (rightExponent C E)
    (nonunitPartitionSet C E U) P hP
  exact supported_prime_gates τ ρ C hC hc i.val
    (Multiset.mem_toFinset.mp (Finset.mem_inter.mp i.property).1)

variable {α : Type*} [Fintype α]

/-- Genuine injective selected prime assignments give squarefree D. -/
theorem selected_squarefree (q : Data α) (y : Selected q)
    (hy : Function.Injective y) : Squarefree (selectedProduct q y) := by
  have hh := forcingIdeal_squarefree (fun j : q.J => (y j).val)
    (fun j => alphabet_prime q.pool q.prime (y j))
    (fun i j he => hy (Subtype.ext he)) (fun _ => 1) (fun _ => 1) Finset.univ
  simpa [forcingIdeal,forcingSet,selectedProduct] using hh

/-- Actual canonical source coefficients are unpacked into actual
nonzero tuples. Thus no C,E coprimality or old-character gate is assumed.
The fresh scalar's natural zeros are retained by selectedPositiveWeight. -/
theorem actual_common_pair (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (hw : selectedPositiveWeight q x y τ ≠ 0)
    (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hβI : outerColumn q x y seed ξ I * heightCoeff τ t I ≠ 0)
    (hβJ : outerColumn q x y seed ξ J * heightCoeff τ t J ≠ 0)
    (C E : Id) (hCI : C ∣ I) (hEJ : E ∣ J) :
    SelectedActive q x y τ ∧ Supported C ∧ Supported E ∧
      IsCoprime (frozenProduct q x * selectedProduct q y) C ∧
      IsCoprime (frozenProduct q x * selectedProduct q y) E ∧
      IsCoprime τ.modulus C ∧ IsCoprime τ.modulus E := by
  have ha := selected_positive_active q x y τ hw
  have hD := ((supported_mul_iff _ _).mp ha.support).2
  obtain ⟨v,hv,hvn⟩ := outer_column_active_tuple q x y seed τ t ξ I hI hβI
  obtain ⟨w,hw',hwn⟩ := outer_column_active_tuple q x y seed τ t ξ J hJ hβJ
  obtain ⟨hcopC,hτC⟩ := original_common_divisor_active q x y seed τ t ξ hD v hvn C
    (by simpa only [hv] using hCI)
  obtain ⟨hcopE,hτE⟩ := original_common_divisor_active q x y seed τ t ξ hD w hwn E
    (by simpa only [hw'] using hEJ)
  exact ⟨ha,supported_of_dvd C I hI hCI,supported_of_dvd E J hJ hEJ,
    hcopC,hcopE,hτC,hτE⟩

/-- All combined forcing gates for the actual second canonical pair.
The quantifier is over ALL primes of H_old*D, including Q-primes.
The following count filters Q-primes once and keeps its fixed radical loss. -/
theorem supplier_combined_structure (q : Data α) (x : Frozen q) (y : Selected q)
    (hy : Function.Injective y) (seed : Id) (τ : Character) (t : ℝ)
    (ξ ρ : RayCharacter) (hw : selectedPositiveWeight q x y τ ≠ 0)
    (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hβI : outerColumn q x y seed ξ I * heightCoeff τ t I ≠ 0)
    (hβJ : outerColumn q x y seed ξ J * heightCoeff τ t J ≠ 0)
    (C E : Id) (hCI : C ∣ I) (hEJ : E ∣ J) (U : Finset (CommonIndex C E)) :
    oldMoving C E U * (primaryGenerator (frozenProduct q x))^2 *
        (primaryGenerator (selectedProduct q y))^2 ≠ 0 ∧
      Squarefree (oldIdeal C E U * selectedProduct q y) ∧
      ∀ P ∈ normalizedFactors (oldIdeal C E U * selectedProduct q y),
        goodLambda ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime (childCharacter τ ρ).modulus P ∧
          valuation (Ideal.span {oldMoving C E U * (primaryGenerator (frozenProduct q x))^2 *
            (primaryGenerator (selectedProduct q y))^2}) P % 6 = 2 := by
  obtain ⟨ha,hC,_,hcopC,_,hτC,_⟩ := actual_common_pair q x y seed τ t ξ hw
    I J hI hJ hβI hβJ C E hCI hEJ
  obtain ⟨hf,hD⟩ := (supported_mul_iff _ _).mp ha.support
  have hfn := supported_primaryGenerator_ne_zero _ hf
  have hdn := supported_primaryGenerator_ne_zero _ hD
  have hAn := old_moving_ne_zero C E hC U
  have hHs := old_squarefree C E U
  have hDs := selected_squarefree q y hy
  have hHD : IsCoprime (oldIdeal C E U) (selectedProduct q y) :=
    old_coprime_of_left C E U _ hcopC.of_mul_left_right.symm
  have hHf : IsCoprime (oldIdeal C E U) (frozenProduct q x) :=
    old_coprime_of_left C E U _ hcopC.of_mul_left_left.symm
  have hAD : IsCoprime (Ideal.span {oldMoving C E U}) (selectedProduct q y) :=
    old_moving_coprime_of_left C E hC U _ hcopC.of_mul_left_right.symm
  have hspanf := primary_span_supported (frozenProduct q x) hf
  have hspanD := primary_span_supported (selectedProduct q y) hD
  obtain ⟨hJs,hJv⟩ := OuterFreshCount.combined_structure (oldIdeal C E U) hHs
    (oldMoving C E U) (primaryGenerator (frozenProduct q x))
    (primaryGenerator (selectedProduct q y)) hAn hfn hdn
    (by simpa only [hspanD] using hDs) (by simpa only [hspanf] using hHf)
    (by simpa only [hspanD] using hHD) (by simpa only [hspanD] using hAD)
    (by simpa only [hspanf,hspanD] using ha.gate.1) (old_valuation C E hC U)
  rw [hspanD] at hJs hJv
  refine ⟨mul_ne_zero (mul_ne_zero hAn (pow_ne_zero _ hfn)) (pow_ne_zero _ hdn),hJs,?_⟩
  intro P hP
  have hv := hJv P hP
  rw [normalizedFactors_mul hHs.ne_zero hDs.ne_zero] at hP
  rcases Multiset.mem_add.mp hP with hp | hp
  · obtain ⟨hl,h2,hτ⟩ := old_prime_gates τ ρ C E hC hτC U P hp
    exact ⟨hl,h2,hτ,hv⟩
  · have hτD : IsCoprime τ.modulus (selectedProduct q y) :=
      ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff τ _).mp
        (active_coefficients q x y τ ha).2).2.symm
    obtain ⟨hl,h2,hτ⟩ := supported_prime_gates τ ρ _ hD hτD P hp
    exact ⟨hl,h2,hτ,hv⟩

/-- Literal nonzero common-sector summands from original_energy_common_sectors
provide the support, divisors and both active source coefficients. -/
theorem actual_sector_data (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (C E I J : Id)
    (hsector : (I,J) ∈ pairSector C E (supportedColumns (commonColumns q))
      (supportedColumns (commonColumns q)))
    (hn : (outerColumn q x y seed ξ I * heightCoeff τ t I) *
      star (outerColumn q x y seed ξ J * heightCoeff τ t J) ≠ 0) :
    Supported I ∧ Supported J ∧
      outerColumn q x y seed ξ I * heightCoeff τ t I ≠ 0 ∧
      outerColumn q x y seed ξ J * heightCoeff τ t J ≠ 0 ∧ C ∣ I ∧ E ∣ J := by
  obtain ⟨hIJ,hC,hE⟩ := Finset.mem_filter.mp hsector
  obtain ⟨hIS,hJS⟩ := Finset.mem_product.mp hIJ
  have hI : Supported I := (Finset.mem_filter.mp hIS).2
  have hJ : Supported J := (Finset.mem_filter.mp hJS).2
  have hleft := left_ne_zero_of_mul hn
  have hright : outerColumn q x y seed ξ J * heightCoeff τ t J ≠ 0 := by
    intro h
    exact hn (by rw [h,star_zero,mul_zero])
  refine ⟨hI,hJ,hleft,hright,?_,?_⟩
  · rw [←hC]
    exact commonPart_dvd I J hI.1
  · rw [←hE]
    exact commonPart_dvd J I hJ.1

/-- Actual fixed-inducing rows now receive ONE root count. The row set's
fixed-inducing property and physical radius are the usual count inputs;
none of its forcing, coprimality, squarefree or valuation gates is assumed.
C,E and the two active columns come from the actual original-k sector. -/
theorem supplier_count (q : Data α) (x : Frozen q) (y : Selected q)
    (hy : Function.Injective y) (seed : Id) (τ : Character) (t : ℝ)
    (ξ ρ : RayCharacter) (hw : selectedPositiveWeight q x y τ ≠ 0)
    (C E I J : Id) (U : Finset (CommonIndex C E))
    (hsector : (I,J) ∈ pairSector C E (supportedColumns (commonColumns q))
      (supportedColumns (commonColumns q)))
    (hpair : (outerColumn q x y seed ξ I * heightCoeff τ t I) *
      star (outerColumn q x y seed ξ J * heightCoeff τ t J) ≠ 0)
    (Q : Id) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, FixedInducingRow (childCharacter τ ρ) Q m
      (oldMoving C E U * (primaryGenerator (frozenProduct q x))^2 *
        (primaryGenerator (selectedProduct q y))^2) z)
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr*Z^M) :
    (rows.card : ℝ) ≤ (Ideal.absNorm (commonRadical Q Q) : ℝ)^(2/3 : ℝ)*
      (768*(6 : ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6 : ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (oldIdeal C E U) : ℝ)-
          4*Real.logb Z (Ideal.absNorm (selectedProduct q y) : ℝ))/6)) := by
  obtain ⟨hI,hJ,hβI,hβJ,hCI,hEJ⟩ :=
    actual_sector_data q x y seed τ t ξ C E I J hsector hpair
  obtain ⟨hA,hHD,hgood⟩ := supplier_combined_structure q x y hy seed τ t ξ ρ hw
    I J hI hJ hβI hβJ C E hCI hEJ U
  have hb := OuterFreshCount.fixed_support_count_fixedQ (childCharacter τ ρ) Q hQ0 hQ hQ72 m
    (oldMoving C E U * (primaryGenerator (frozenProduct q x))^2 *
      (primaryGenerator (selectedProduct q y))^2) hm hA hmLam hm2 rows hrows hex
    (oldIdeal C E U * selectedProduct q y) hHD hgood Z Cr M hZ hCr hN
  rw [map_mul,Nat.cast_mul,Real.logb_mul (norm_pos (old_squarefree C E U).ne_zero).ne'
    (norm_pos (selected_squarefree q y hy).ne_zero).ne'] at hb
  have he : (M-4*(Real.logb Z (Ideal.absNorm (oldIdeal C E U) : ℝ)+
      Real.logb Z (Ideal.absNorm (selectedProduct q y) : ℝ)))/6 =
      (M-4*Real.logb Z (Ideal.absNorm (oldIdeal C E U) : ℝ)-
        4*Real.logb Z (Ideal.absNorm (selectedProduct q y) : ℝ))/6 := by ring
  simpa only [he] using hb

end
end Candidate.Feedback.FourthPower.OuterFreshStructure
