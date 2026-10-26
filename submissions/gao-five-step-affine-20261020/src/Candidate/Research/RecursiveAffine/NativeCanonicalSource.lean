/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowQuantitativePayment
import Candidate.Cycle63.Physical.InitialMass.SecondLowSourceCaps
import Candidate.Research.RecursiveAffine.PhysicalDaughterSource
import Candidate.Research.RecursiveAffine.LowPhysical.NativeResidualShells

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153CanonicalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open LocalMoment
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentDivisorRetained
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearNormalization CenteredMomentEnergyBands
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open Cycle63Moment Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural
open Cycle63InitialMass Cycle153RegionalLow Cycle153LowPhysical
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The genuine original plain-scale cap survives both actual common
allocations and every actual residual plain divisor. It bounds the raw
source scales used by the recursive daughter operator, before clipping. -/
theorem actual_chain_raw_plain_cap (s : Input α) (ch : Chain s)
    (χ : Character) (t bound : ℝ) (hbound : 1 ≤ bound)
    (hplain : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j ≤ bound)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2))) (j : Fin 2) :
    rawDaughterScale (ch.final χ t) second L alloc j ≤ bound := by
  have hcap := actual_two_common_final_plain_cap s bound hbound hplain
    ch.C₁ ch.R₁ ch.B₁ ch.η₁ ch.t₁ ch.E₂ ch.R₂ ch.B₂ χ t L alloc second j
  apply le_trans _ hcap
  change rawDaughterScale (ch.final χ t) second L alloc j ≤
    max 1 (rawDaughterScale (ch.final χ t) second L alloc j)
  exact le_max_right _ _

/-- The occupied canonical buffer supplies the actual source-frequency
envelope for every original slot, retaining the signed shifted height. -/
theorem canonical_buffer_frequency {ι : Type*} {e : ℝ} (p : BufferIndex e)
    (hp : 1 ≤ p.1.val) (heightV height T : ℝ) (hT : 0 ≤ T)
    (hheight : |heightV|+height+T/2 ≤ 5*T)
    (frequency : ι→ℝ) (hfrequency : ∀i,|frequency i| ≤ height) :
    |heightV|+height+T/2 ≤ (3*p.1.val+2:ℕ)*T ∧
    ∀i,|heightV+frequency i|+T/2 ≤ (3*p.1.val+2:ℕ)*T := by
  have hb := main_low_payment_height_bin p hp heightV height T hT hheight
  refine ⟨hb,?_⟩
  intro i
  have ha := abs_add_le heightV (frequency i)
  linarith only [hb,ha,hfrequency i]

/-- Ordinary restriction changes only the physical row set. The native
residual cost keeps the original input, ray, height, projector seed,
reciprocal coefficient and normalized column literally. In particular,
no first-seed reciprocal is moved onto a returned forest. -/
theorem ordinary_native_residual_cost_eq {Label : Type} [Fintype Label]
    (second : Bool) (datum : Label→SecondInputDatum α)
    (χ₀ : Label→RayFourExpansion.RayCharacter) (Q : Ideal O) (m : O)
    (coefficient : Label→ℝ) (ray : Label→RayFourExpansion.RayCharacter)
    (height : Label→ℝ) (zs : Label→Finset O) (r : Label) (D : Ideal O) :
    nativeResidualCost second (fun r=>ordinarySecondDatum (datum r) (χ₀ r) Q m)
      coefficient ray height zs (fun _ _=>1) r D =
    coefficient r * ∑z∈zs r,
      ‖normalizedColumn (withHeight (datum r).input ((datum r).τ (ray r)) (height r))
        (if second then (datum r).D else (datum r).C) (mainLowPhysicalSupported second (datum r))
        (datum r).R (datum r).seed D z‖^2 := by
  unfold nativeResidualCost
  simp only [one_mul]
  rfl

/-- The shared residual projector dictionary is unchanged by ordinary
restriction; the shell selected before the canonical rows remains SAME. -/
theorem ordinary_shared_projectors_eq {Label : Type} [Fintype Label]
    (datum : Label→SecondInputDatum α) (χ₀ : Label→RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m : O) :
    sharedProjectors (fun r=>(ordinarySecondDatum (datum r) (χ₀ r) Q m).block.divisors.filter Squarefree)=
      sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree) := rfl
end
end OAI.SevenEighths.Cycle153CanonicalLow
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.actual_chain_raw_plain_cap
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.canonical_buffer_frequency
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.ordinary_native_residual_cost_eq
