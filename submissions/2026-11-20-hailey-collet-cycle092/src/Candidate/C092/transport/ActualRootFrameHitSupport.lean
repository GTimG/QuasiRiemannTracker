/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   True selected/reindexed coefficient support and normalization projectors. -/
import Candidate.C092.transport.ActualRootFrameHitSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualRootFrameHit
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentActiveSource
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock MixedOriginalNormCap
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.ColoredGaussFrameProvider QRH.Cycle092.TwistedRawSource
local notation "Id"=>Ideal HeckeFamily.O
local instance (priority := 2000) supportHitSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type} [Fintype ι] {a b:ℝ}

/-- No nonzero value of an uncolored aggregate is inferred. The actual
    two colored columns and their active finite carriers agree exactly. -/
theorem selected_active_eq (s:Source ι a b)(ha:0<a)(hb:0≤b)(cover:OriginalEnclosure s)
    (G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val))
    (ω₁ ω₂:Id→*₀ℂ) :
    RootColoredSeed.active (originalSelectedSource s hb cover G B J) ha ω₁ ω₂=
      RootColoredSeed.active (restOf s hb cover G B J) ha ω₁ ω₂ := by
  unfold originalSelectedSource RootColoredSeed.active
  rw [sourceColumns_reindex,sourceColumn_reindex,sourceColumns_renorm,sourceColumn_renorm]

theorem selected_volume_eq (s:Source ι a b)(hb:0≤b)(cover:OriginalEnclosure s)
    (G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)) :
    sourceVolume (originalSelectedSource s hb cover G B J)=sourceVolume (renorm (restOf s hb cover G B J)) := by
  unfold originalSelectedSource
  exact sourceVolume_reindex _ _

theorem selected_floor_eq (s:Source ι a b)(hb:0≤b)(cover:OriginalEnclosure s)
    (G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val)) :
    (originalSelectedSource s hb cover G B J).L=(renorm (restOf s hb cover G B J)).L := rfl

/-- The original residual scalar norm cap bounds the same literal colored
    active columns after both native prefix normalization and reindexing. -/
theorem selected_column_cap (s:Source ι a b)(ha:0<a)(hb:0≤b)(cover:OriginalEnclosure s)
    (G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val))
    (ω₁ ω₂:Id→*₀ℂ)(X:ℝ)
    (hcap:sourceNormCap (restOf s hb cover G B J).P b (restOf s hb cover G B J).T
      (restOf s hb cover G B J).d≤X) :
    ∀I∈RootColoredSeed.active (originalSelectedSource s hb cover G B J) ha ω₁ ω₂,(I.absNorm:ℝ)≤X := by
  intro I hI
  rw [selected_active_eq] at hI
  unfold RootColoredSeed.active at hI
  rw [mem_activeSource] at hI
  exact (sourceColumn_cap (restOf s hb cover G B J) ha ω₁ ω₂ 1 I hI.2).2.trans hcap

#print axioms selected_active_eq
#print axioms selected_volume_eq
#print axioms selected_column_cap
end
end QRH.Cycle092.ActualRootFrameHit
