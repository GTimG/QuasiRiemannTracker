/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Prefix renormalization preserves the literal colored source and physical rows. -/
import Candidate.C092.transport.ColoredGaussFrameProviderReindex
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderResidual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentRectangle
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) renormSumDecEq {κ κ₂ : Type*} : DecidableEq (κ⊕κ₂) := Classical.decEq _

/-- This is tuplewise renormalization, so neither independent ordinary color
    nor any cancellation in its finite column is changed. -/
theorem sourceColumn_renorm (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (seed : Id) :
    sourceColumn (renorm s) ha ω₁ ω₂ seed = sourceColumn s ha ω₁ ω₂ seed := by
  unfold sourceColumn
  rw [tuplePools_renorm]
  congr 1
  funext u
  congr 1
  unfold MixedOriginalSecondZero.originalTuple
  congr 1
  unfold profileCoefficient
  dsimp only [renorm]
  rw [idealRectangle_renorm _ _ s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2
    (u (Sum.inr 0)) (u (Sum.inr 1)) s.hd.1 s.hd.2]

theorem groupedPartTerms_renorm (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ)
    (part : Bool) (ψ : Character) (χ₀ : RayFourExpansion.RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) :
    RootColoredSeed.groupedPartTerms part (renorm s) ha ω₁ ω₂ ψ χ₀ Q m t K Tsec Z ξ H =
      RootColoredSeed.groupedPartTerms part s ha ω₁ ω₂ ψ χ₀ Q m t K Tsec Z ξ H := by
  have hc := sourceColumn_renorm s ha ω₁ ω₂ 1
  have hA : RootColoredSeed.active (renorm s) ha ω₁ ω₂ = RootColoredSeed.active s ha ω₁ ω₂ := by
    unfold RootColoredSeed.active
    rw [sourceColumns_renorm,hc]
  exact congrArg₂ (fun S c=>physicalTerms part S c ψ χ₀ Q m t K Tsec Z ξ H) hA hc

variable {L : ℝ} {θ : GData L} {Z : ℝ}
local instance (priority := 2000) renormSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-- Exactly the upstream residFin construction: renorm, then native reindex. -/
def normalizedSelectedSource (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (J : Finset (liveIndices B.val)) : Source (Fin (Fintype.card (Rest J))) θ.a θ.b :=
  reindexSource (renorm (restOf s hb cover G B J)) (Fintype.equivFin (Rest J))

theorem normalizedSelectedSource_canonical (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b)
    (cover : OriginalEnclosure s) (χ : Fin θ.N→RayQuotient.Characters θ.rayM θ.Hray)
    (w σ freq : Fin θ.N→ℝ) (t : ℝ) (R₀ : Fin θ.N→Finset Id)
    (hcan : Canonical s Z χ w σ freq t R₀ s.H s.R s.d)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    Canonical (θ:=withSlots θ (Fintype.card (Rest J))) (normalizedSelectedSource s hb cover G B J) Z
      (fun i=>χ (originalIndex s hb cover G B J i))
      (fun i=>w (originalIndex s hb cover G B J i))
      (fun i=>σ (originalIndex s hb cover G B J i))
      (fun i=>freq (originalIndex s hb cover G B J i)) t
      (fun i=>R₀ (originalIndex s hb cover G B J i)) s.H
      (restOf s hb cover G B J).R (1,1) := by
  refine ⟨hcan.S,rfl,?_,?_,?_,?_,rfl,rfl⟩
  · intro i;exact hcan.pool (originalIndex s hb cover G B J i)
  · intro i;exact hcan.ν (originalIndex s hb cover G B J i)
  · intro i;exact hcan.Wslot (originalIndex s hb cover G B J i)
  · intro i;exact hcan.P (originalIndex s hb cover G B J i)

#print axioms sourceColumn_renorm
#print axioms groupedPartTerms_renorm
#print axioms normalizedSelectedSource_canonical
end
end QRH.Cycle092.ColoredGaussFrameProvider
