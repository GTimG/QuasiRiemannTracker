import Candidate.Cycle25.Assembly.SourceData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource

set_option autoImplicit false
set_option maxHeartbeats 40000

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open ProbePhysical CenteredMomentDetectorDictionary Cycle25ProbeFinalAssembly
local notation "O" => HeckeFamily.O

theorem excluded_one_ofResidue (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) :
    excluded (Character.ofResidue M hM χ hu) 1 = Character.ofResidue M hM χ hu := by
  have hsupport : CompletedGauss.primeSupport (1 : Ideal O) = ∅ := by
    change UniqueFactorizationMonoid.primeFactors (1 : Ideal O) = ∅
    exact UniqueFactorizationMonoid.primeFactors_one
  unfold excluded Character.excludePrimes
  simp only [hsupport, Finset.prod_empty, mul_one]
  unfold Character.refineModulus
  have hinflate : ResidueCharacter.inflate (show M ≤ M from le_refl M) χ = χ := by
    apply DFunLike.ext
    intro x
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [ResidueCharacter.inflate_mk]
    split_ifs with hn
    · rfl
    · exact (MulChar.map_nonunit χ hn).symm
  change Character.ofResidue M _ (ResidueCharacter.inflate _ χ) _ = _
  congr 1

private theorem fixed_source_supported (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (hbad : fixedBadPrimes ⊆ S) (n : O)
    (hn : elementCoeff (fixedSourcePrincipal S hS) n ≠ 0) :
    Supported (Ideal.span {n}) := by
  have hunit := MulChar.apply_ne_zero_iff.mp hn
  have hcop : IsCoprime (Ideal.span {n}) (fixedSourcePrincipal S hS).modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp hunit
  have hmod : (fixedSourcePrincipal S hS).modulus ≤ Ideal.span {fixedBadMask} := by
    have h := source_product_le_rowMask S hbad
    simpa only [fixedSourcePrincipal, HeckeRayFamily.character, Character.ofResidue,
      ProbeHighRowFamily.rowMaskElement, fixedBadMask, mul_comm] using h
  have hc : IsCoprime n fixedBadMask :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hmod))
  have hlam : IsCoprime goodLambda n := (hc.symm.of_isCoprime_of_dvd_left (dvd_mul_right _ _))
  have htwo : IsCoprime (2 : O) n := (hc.symm.of_isCoprime_of_dvd_left (dvd_mul_left _ _))
  apply (supported_span_iff n).mpr
  refine ⟨PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp hlam, ?_⟩
  have hneg : IsCoprime (-2 : O) n := htwo.of_isCoprime_of_dvd_left ⟨-1, by ring⟩
  simpa only [neg_dvd] using negative_two_prime.irreducible.coprime_iff_not_dvd.mp hneg

/-- The original fixed exclusions absorb the natural row's fixed sixth mask. -/
theorem actual_fixed_source_unit_row (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (hbad : fixedBadPrimes ⊆ S) (n : O) :
    elementCoeff (fixedSourcePrincipal S hS) n =
      rowTwist (elementHom (fixedSourcePrincipal S hS)) fixedBadMask 1 1 n := by
  by_cases hs : Supported (Ideal.span {n})
  · have hcop : IsCoprime (Ideal.span {n}) (Ideal.span {fixedBadMask}) :=
      (Ideal.isCoprime_span_singleton_iff _ _).mpr (fixedBadMask_coprime n hs).symm
    have hrow := idealRowHom_sixth_mask fixedBadMask (Ideal.span {n}) hs
    rw [ite_eq_left hcop] at hrow
    change elementCoeff _ n = elementCoeff _ n * idealRowHom (fixedBadMask ^ 6 * 1 ^ 4 * 1) _
    simp only [one_pow, mul_one]
    change elementCoeff _ n = elementCoeff _ n * idealRowHom (fixedBadMask ^ 6) (Ideal.span {n})
    rw [hrow, mul_one]
  · have hz : elementCoeff (fixedSourcePrincipal S hS) n = 0 := by
      by_contra h
      exact hs (fixed_source_supported S hS hbad n h)
    change elementCoeff _ n = elementCoeff _ n * idealRowHom _ _
    rw [hz, zero_mul]

def fixedSourceNaturalRow (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (hbad : fixedBadPrimes ⊆ S) : NaturalRow (fixedSourcePrincipal S hS) (1 : O) where
  character := fixedSourcePrincipal S hS
  modulus_bound := by
    have hm : 1 ≤ (Ideal.span {fixedBadMask} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    have h72 : 1 ≤ (Ideal.span {(72 : O)} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    simp only [rowConductorBound, Ideal.span_singleton_one, Ideal.absNorm_top, one_pow, mul_one]
    exact (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt hm)).trans
      (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt h72))
  element := actual_fixed_source_unit_row S hS hbad

theorem actual_fixed_source_natural_excluded (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hbad : fixedBadPrimes ⊆ S) :
    fixedSourcePrincipal S hS = excluded (fixedSourceNaturalRow S hS hbad).character 1 := by
  change fixedSourcePrincipal S hS = excluded (fixedSourcePrincipal S hS) 1
  unfold fixedSourcePrincipal HeckeRayFamily.character
  exact (excluded_one_ofResidue _ _ _ _).symm

theorem actual_weighted_source_natural_excluded {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) :
    fixedSourcePrincipal F.S F.exclusions.prime =
      excluded (fixedSourceNaturalRow F.S F.exclusions.prime F.exclusions.bad).character 1 :=
  actual_fixed_source_natural_excluded F.S F.exclusions.prime F.exclusions.bad

end
end OAI.SevenEighths.Cycle63InitialMass
