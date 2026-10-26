/- Packaging rehearsal. Original notices retained; separate replay required. -/
/- B176Part2A (1 of 3): consecutive declarations of one original source section, unchanged, split for the 600-second per-module replay limit. -/
import Candidate.Bundles.B176Part1

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCoarseFamily; sha256 9ab5aeb70109181eb2521fb5fab7c857dfc19e094fb893fa86c97e4dcf1ab307 -/
section
                                                                
                                                                 
                                                         
                                                      
                                                        

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentSecondEnergySplit CenteredMomentWholeDivisorShell
open CenteredMomentSourceRow CenteredMomentCommonPairedSource CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstSourceReduction
local notation "O" => HeckeFamily.O
local instance geometryMainCoarseFamilySumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem geometry_ordinary_high_image_sum
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α)
    (χ : Label→ RayCharacter) (Q : Label→ Ideal O) (m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (rows : Finset (secondLiveRows
      (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)))
    (second : Bool)
    (weight height : secondLiveRows (fun l=>(d l).block)→ℝ)
    (Ds : secondLiveRows (fun l=>(d l).block)→ Finset (Ideal O)) :
    (∑r∈rows,weight (ordinaryHighOriginalRow d χ Q m hrows r)*
      highNormalizedRowCost second (fun l=>ordinarySecondDatum (d l) (χ l) (Q l) (m l))
        r (height (ordinaryHighOriginalRow d χ Q m hrows r))
        (Ds (ordinaryHighOriginalRow d χ Q m hrows r))) =
      ∑r∈rows.image (ordinaryHighOriginalRow d χ Q m hrows),
        weight r*highNormalizedRowCost second d r (height r) (Ds r) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r _
    rw [ordinary_high_original_row_cost]
  · intro r _ s _ h
    exact ordinary_high_original_row_injective d χ Q m hrows h

end
end OAI.SevenEighths.Cycle61InitialMass

end
