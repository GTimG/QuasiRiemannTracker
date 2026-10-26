/- Actual weighted-root parent presentation.
Supported-coefficient argument adapted unchanged from Hailey Collet's
Cycle63/CountAffine/Supply (Apache-2.0); binding (c)2026 Zhongpai Gao. -/
import Candidate.Research.RecursiveAffine.LocalGeometryWitness
import Candidate.Research.RecursiveAffine.PrefixHighPresentation

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical HeckeNotation
open HeckeRowClosure CanonicalRowCompletion ActualEisensteinCubic Cycle153HighProvider
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open CenteredMomentCommonRadialData CenteredMomentChildRows
open Cycle63InitialMass Cycle153LocalHighWitness

/-- The actual final weighted source hypothesis on the fixed character
already forces every nonzero source coefficient onto supported elements. -/
theorem root_supported_of_modulus (eta : Character)
    (heta : eta.modulus ≤ Ideal.span {fixedBadMask})(n : O)
    (hn : elementCoeff eta n≠0) : Supported (Ideal.span {n}) :=by
  have hunit:=MulChar.apply_ne_zero_iff.mp hn
  have hcop : IsCoprime (Ideal.span {n}) eta.modulus:=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp hunit
  have hc : IsCoprime n fixedBadMask:=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr heta))
  have hlam : IsCoprime goodLambda n:=(hc.symm.of_isCoprime_of_dvd_left (dvd_mul_right _ _))
  have htwo : IsCoprime (2:O) n:=(hc.symm.of_isCoprime_of_dvd_left (dvd_mul_left _ _))
  apply (supported_span_iff n).mpr
  refine ⟨PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp hlam,?_⟩
  have hneg : IsCoprime (-2:O) n:=htwo.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  simpa only[neg_dvd] using negative_two_prime.irreducible.coprime_iff_not_dvd.mp hneg

/-- The root row is constructed from the literal final seed eta at row1.
The actual affine root has character eta by its fixedParentState
constructor; no chosen natural row or presentation is an input. -/
def actualRootParentRow (eta : Character)(heta : eta.modulus ≤ Ideal.span {fixedBadMask}) :
    NaturalRow eta 1:=selfNaturalRow eta (root_supported_of_modulus eta heta)

theorem actual_root_parent_presentation {alpha : Type}[Fintype alpha]
    (eta : Character)(heta : eta.modulus ≤ Ideal.span {fixedBadMask})
    (s : Input alpha)(hs : s.η=eta) :
    ParentPresentation s.η (actualRootParentRow eta heta) 1:=by
  rw [hs]
  exact self_parent_presentation eta (actualRootParentRow eta heta) rfl
    (root_supported_of_modulus eta heta)
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_parent_presentation
