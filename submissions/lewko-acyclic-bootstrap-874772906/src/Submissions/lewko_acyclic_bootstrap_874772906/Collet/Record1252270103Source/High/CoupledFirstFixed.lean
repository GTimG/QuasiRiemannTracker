/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified columns keep the canonical character and fixed-mask coprimality.
Adapted from pinned OpenAI/Hailey Collet source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstAllocation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy


set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators

namespace QRH.Record1252270103Source.High.CoupledFirst
open OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport
open CenteredMomentFirstPhysicalSource
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

variable {ι:Type*}[Fintype ι]
local instance coupledFirstFixedDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem beta_coprime (s:OriginalData ι)(modifier:Tuple ι→ℂ)(I:Ideal O)(h:modifiedBeta s modifier I≠0):IsCoprime I s.R:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.S) (fun v=>modifier v*s.profile v) I h
  have hv0 := (mul_ne_zero_iff.mp hv0).2
  rw [←he]
  by_contra hn
  apply hv0
  simp only [OriginalData.profile,profileCoefficient,hn,ite_false,mul_zero,zero_mul]

lemma extracted_mask_redundant (s:OriginalData ι)(modifier:Tuple ι→ℂ)(C:Ideal O):
    maskedSource (idealGenerator s.R) (fun I=>modifiedBeta s modifier (C*I))=(fun I=>modifiedBeta s modifier (C*I)):=by
  apply maskedSource_eq_of_live
  intro I hI
  rw [span_idealGenerator]
  exact (beta_coprime s modifier (C*I) hI).of_mul_left_right

theorem fixed_divisor_column (s:OriginalData ι)(modifier:Tuple ι→ℂ)(η τ:Character)(C:Ideal O)
    (F:O→ℂ)(ξ:RayCharacter)
    (hτ:∀I:Ideal O,Supported I→∀t:ℝ,heightCoeff τ t I=
      rowWeight η fixedBadMask 1 1 t I*(F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (L I:Ideal O)(hI:Supported I)(t:ℝ):
    divisorCoefficient L (fun J:Ideal O=>primaryGenerator J)
      (fun J=>modifiedBeta s modifier (C*J)*rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t J*
        F (primaryGenerator J)) ξ I=
      (if L∣I then modifiedBeta s modifier (C*I) else 0)*heightCoeff τ t I:=by
  have hh:=divisor_column_masked η τ F ξ hτ (idealGenerator s.R) L I hI (fun J=>modifiedBeta s modifier (C*J)) t
  rw [extracted_mask_redundant s modifier] at hh
  exact hh

variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem fixed_left_column (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)(modifier:Tuple ι→ℂ)(t:ℝ)(L:Ideal O)
    (I:columns C C hC.1 s.columns):
    divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t (modifiedBeta s modifier) C a*
        leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C C hC.1 s.columns a)) ξ₁ I=
      (if L∣(I:Ideal O) then (modifiedBeta s modifier) (C*I) else 0)*heightCoeff F.left t I:=
  fixed_divisor_column s modifier η F.left C _ ξ₁ F.left_height L I
    (column_supported C C hC.1 s.columns I) t

theorem fixed_right_column (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (s:OriginalData ι)(modifier:Tuple ι→ℂ)(t:ℝ)(L:Ideal O)(I:columns C D hD.1 s.columns):
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t (modifiedBeta s modifier) D a*
        rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C D hD.1 s.columns a)) ξ₂ I=
      (if L∣(I:Ideal O) then (modifiedBeta s modifier) (D*I) else 0)*heightCoeff F.right t I:=
  fixed_divisor_column s modifier η F.right D _ ξ₂ F.right_height L I
    (column_supported C D hD.1 s.columns I) t

end QRH.Record1252270103Source.High.CoupledFirst
end
#print axioms QRH.Record1252270103Source.High.CoupledFirst.beta_coprime
#print axioms QRH.Record1252270103Source.High.CoupledFirst.fixed_left_column
#print axioms QRH.Record1252270103Source.High.CoupledFirst.fixed_right_column
