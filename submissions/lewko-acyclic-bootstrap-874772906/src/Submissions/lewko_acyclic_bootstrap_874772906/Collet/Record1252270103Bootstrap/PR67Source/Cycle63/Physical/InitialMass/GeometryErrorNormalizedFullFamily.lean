import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalErrorCapacity.Capacity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorNormalizedAssembly
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondRetainedRows
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentEligibleEnergy CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAmplificationErrorEnergy CenteredMomentRestrictedEnergy
open CenteredMomentAllocatedRayDictionary CenteredMomentSlotRatios
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Cycle63FinalNatural Cycle63Moment Cycle63FinalError Cycle63FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget CenteredMomentLogDyadic
local instance errorNormalizedFullFamilySumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Arbitrary finite original block families retain both ray sums, the
complete ordinary zero-mode sets and the exact extracted-prime coefficient. -/
theorem actual_error_indexed_normalized_to_admitted_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K)
    (index : Label→ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0≤weight) (prime : O) (i : Fin 3)
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (hcard : Fintype.card α≤N) (hlower : a≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ap≤x) (hW₂ : ∀x,s.W₂ x≠0→ap≤x)
    (W : 𝓢(ℝ,ℂ)) (χ₀ : Label→RayCharacter) (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (second : Bool) (t u : ℝ) :
    let d := fun n=>actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK (index n)
    let datum := fun n=>ordinarySecondDatum (d n) (χ₀ n) Q fixedBadMask
    let c := errorNormalizedCoefficient P weight (volume s) prime i
    let w := fun n=>(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ (index n)
    secondNormalizedSum second datum
      (secondEffectiveWeight (fun n=>(datum n).block) w W) t u≤
      ∑χ : RayCharacter,∑ψ : RayCharacter,∑n,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if second then
            ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D z‖^2
           else
            ∑z∈partRows false s.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
  intro d datum c w
  have hc : 0≤ c := error_normalized_coefficient_nonneg P weight (volume s) hw (volume_pos s) prime i
  have hbase := actual_error_ordinary_normalized_columns N a ap ha hap d w W hcard
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂) χ₀ Q second t u
  apply hbase.trans
  calc
    _≤∑n,∑χ : RayCharacter,∑ψ : RayCharacter,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          ∑z∈partRows false s.η (χ₀ n) Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
            (if second then
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D (-z)‖^2
             else
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
      refine Finset.sum_le_sum fun n _ => ?_
      apply Finset.sum_le_sum
      intro χ _
      apply Finset.sum_le_sum
      intro ψ _
      have hn := actual_block_weight_norm s R seed K Tsec Z ξ (index n) c hc
      have hf : 0≤K/lowerFactor N a ap := div_nonneg hK.le (lowerFactor_pos N a ap ha hap).le
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hf)
          (normalizer_pos (d n).C (d n).D (d n).hC (d n).inactive).le
      · exact Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>by split_ifs <;> positivity))
    _=∑n,∑χ : RayCharacter,∑ψ : RayCharacter,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if second then
            ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D z‖^2
           else
            ∑z∈partRows false s.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ψ _ => ?_
      apply congrArg (fun r : ℝ=>(c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*r)
      refine Finset.sum_congr rfl fun D _ => ?_
      exact actual_error_complete_column_rows s (d n).τ (d n).C (d n).D (d n).hC (d n).hD
        (d n).inactive R seed D Q (d n).radius hQ (χ₀ n) χ ψ second t u
    _=_ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro χ _; rw [Finset.sum_comm]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
