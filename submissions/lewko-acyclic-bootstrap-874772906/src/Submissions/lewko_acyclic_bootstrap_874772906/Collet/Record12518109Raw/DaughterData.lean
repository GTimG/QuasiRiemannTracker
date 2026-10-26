/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.GeometryChainProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
local notation "O" => HeckeFamily.O

/-- A positive physical daughter of one actual second datum. This package
contains only literal row/allocation choices; it has no analytic fields. -/
structure PhysicalDaughter {α : Type*}[Fintype α][DecidableEq α]
    (datum : SecondInputDatum α)(second : Bool) where
  row : secondLiveRows (fun _ : Unit=>datum.block)
  common : actualAllocations datum.input.pools (if second then datum.D else datum.C)
  projector : Ideal O
  residual : Allocation projector
    (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices common.val⊕Fin 2))
  rectangle : Bool

namespace PhysicalDaughter
variable {α : Type*}[Fintype α][DecidableEq α]
variable {datum : SecondInputDatum α}{second : Bool}(d : PhysicalDaughter datum second)

def source (ψ : RayCharacter)(v : ℝ) :=
  commonData (withHeight datum.input (datum.τ ψ) v)
    (if second then datum.D else datum.C) datum.R d.common

def scale (j : Fin 2) : ℝ :=
  Cycle61.Physical.sourcePlainScales
    (commonData datum.input (if second then datum.D else datum.C) datum.R d.common).toSource
    d.rectangle j/(selectedPlain d.projector d.residual j).absNorm

def value (ψ : RayCharacter)(v : ℝ) : ℂ :=
  Cycle61.Physical.sourcePositiveRow (d.source ψ v).toSource d.rectangle d.projector d.residual
    (if second then -d.row.val.2.2.2.val else d.row.val.2.2.2.val)

theorem scale_pos (j : Fin 2) : 0<d.scale j := by
  have hn : (0:ℝ)<(selectedPlain d.projector d.residual j).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero d.projector Finset.univ d.residual (Sum.inr j)))
  dsimp only [scale]
  apply div_pos _ hn
  cases h:d.rectangle <;> fin_cases j
  · exact (commonData datum.input _ datum.R d.common).X₁_pos
  · exact (commonData datum.input _ datum.R d.common).X₂_pos
  · exact (commonData datum.input _ datum.R d.common).Y₁_pos
  · exact (commonData datum.input _ datum.R d.common).Y₂_pos

end PhysicalDaughter
end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.PhysicalDaughter.scale_pos
