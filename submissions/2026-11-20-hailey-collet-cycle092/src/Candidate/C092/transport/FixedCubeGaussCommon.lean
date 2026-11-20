/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact source transport through Sil's native common allocation. -/
import Candidate.C092.transport.FixedCubeGaussCompleted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSecondSectorColumns
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentLattice
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedHeightEnergy MixedCommonRestriction MixedCommonCoefficient
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def sourcePools (r : Source ι a b) := MixedPrincipalAllocations.tuplePools r

def commonAlloc (r : Source ι a b) (G : Id) := actualAllocations (sourcePools r) G

theorem commonAlloc_ne (r : Source ι a b) (G : Id) (B : commonAlloc r G) : ∀ j,B.val j≠0 :=
  (allocation_data _ _ _ (Finset.mem_filter.mp B.property).1).1

def commonScalar (r : Source ι a b) (G : Id) (B : commonAlloc r G) : ℂ :=
  frozenWeight (punctureProduct r.S r.H) B.val*frozenCoefficient B.val G r.R r.ν r.Wslot r.P

def commonLiveCoefficient (r : Source ι a b) (ha : 0<a) (G : Id) (B : commonAlloc r G) (I : Id) : ℂ :=
  finiteColumnCoefficient (liveBox (sourcePools r) B.val (commonAlloc_ne r G B))
    (fun v=>tupleWeight (punctureProduct r.S r.H) v*
      liveProfile B.val G r.R r.ν r.Wslot r.P
        (normPowerProfile r.W₁ a b ha r.hs₁ (r.W₁.smooth ⊤) r.t₁)
        (normPowerProfile r.W₂ a b ha r.hs₂ (r.W₂.smooth ⊤) r.t₂)
        r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2 v) I

/-- This is the original source coefficient at the actual sector ideal,
allocated by the full common ideal. No coefficient or restriction is replaced. -/
theorem sourceCoefficient_common_allocated (r : Source ι a b) (ha : 0<a)
    (G : Id) (hG : Supported G) (I : sectorPool G hG.1 (Second.Concrete.S0 r ha)) :
    sourceCoefficient r ha 1 (G*I)=
      ∑ B : commonAlloc r G,commonScalar r G B*commonLiveCoefficient r ha G B I := by
  have hI := sectorPool_supported G hG.1 _ I
  have hcop : IsCoprime G (I:Id) := (Finset.mem_filter.mp I.property).2
  have hsrc : ∀ j,∀ K∈sourcePools r j,K≠0 := by
    exact MixedLiteralAllocation.source_pools_nonzero r.pool r.hp r.d r.hd b r.X₁ r.X₂ r.Y₁ r.Y₂
  have hp : ∀ i,∀ K∈sourcePools r (Sum.inl i),Prime K := r.hp
  exact original_restricted_column (punctureProduct r.S r.H) (sourcePools r) hsrc hp
    G r.R 1 I hG.1 hI.1 hcop (one_dvd _) r.ν r.Wslot r.P _ _
    r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2

#print axioms sourceCoefficient_common_allocated
end
end QRH.Cycle092.FixedCubeGauss
