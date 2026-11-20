/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   The genuine generic Original canonical producer reaches native selected-frame data. -/
import Candidate.C092.transport.ColoredGaussFrameProviderActual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) originalSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def originalSlot (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (i : Fin (Fintype.card (Rest J))) : ι := ((Fintype.equivFin (Rest J)).symm i).val.val

def originalSelectedSource (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    Source (Fin (Fintype.card (Rest J))) a b :=
  reindexSource (renorm (restOf s hb cover G B J)) (Fintype.equivFin (Rest J))

variable {L : ℝ} {θ : GData L} {Z : ℝ}

/-- The five original canonical mark identities of RestoredRootSource.Data,
    after actual allocation/deletion, give every native frame canonical field. -/
theorem originalSelectedSource_canonical (s : Source ι θ.a θ.b) (hb : 0≤θ.b)
    (cover : OriginalEnclosure s) (χ : ι→RayQuotient.Characters θ.rayM θ.Hray)
    (w σ freq : ι→ℝ) (t : ℝ) (R₀ : ι→Finset Id)
    (hcan : MixedFirstActualNonexceptional.Canonical θ.rayM θ.Hray θ.hH θ.W θ.Cap θ.Lcap Z
      θ.η₀ χ w σ freq t R₀ s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    Canonical (θ:=withSlots θ (Fintype.card (Rest J))) (originalSelectedSource s hb cover G B J) Z
      (fun i=>χ (originalSlot s hb cover G B J i))
      (fun i=>w (originalSlot s hb cover G B J i))
      (fun i=>σ (originalSlot s hb cover G B J i))
      (fun i=>freq (originalSlot s hb cover G B J i)) t
      (fun i=>R₀ (originalSlot s hb cover G B J i)) s.H (restOf s hb cover G B J).R (1,1) := by
  obtain ⟨hS,hpool,hν,hWs,hP⟩ := hcan
  refine ⟨hS,rfl,?_,?_,?_,?_,rfl,rfl⟩
  · intro i;exact congrFun hpool (originalSlot s hb cover G B J i)
  · intro i;exact congrFun hν (originalSlot s hb cover G B J i)
  · intro i;exact congrFun hWs (originalSlot s hb cover G B J i)
  · intro i;exact congrFun hP (originalSlot s hb cover G B J i)

/-- Reindexing and actual prefix absorption preserve each physical flag,
    all original rows, and its exact Fourier kernel. -/
theorem originalSelectedSource_grouped (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (J : Finset (liveIndices B.val)) (ω₁ ω₂ : Character) (part : Bool) (ψ : Character)
    (χ₀ : RayFourExpansion.RayCharacter) (Q : Id) (m : HeckeFamily.O) (t K Tsec Z ξ H : ℝ) :
    RootColoredSeed.groupedPartTerms part (originalSelectedSource s hb cover G B J) ha
      (idealCoeff ω₁) (idealCoeff ω₂) ψ χ₀ Q m t K Tsec Z ξ H =
    RootColoredSeed.groupedPartTerms part (restOf s hb cover G B J) ha
      (idealCoeff ω₁) (idealCoeff ω₂) ψ χ₀ Q m t K Tsec Z ξ H := by
  unfold originalSelectedSource
  rw [groupedPartTerms_reindex,groupedPartTerms_renorm]

/-- The selected puncture is the genuine first common factor because the
    Original producer has R=1. Its Z^8 cap follows from actual colored first labels. -/
theorem originalSelectedSource_R_cap (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (ω₁ ω₂ : Character) (hR : s.R=1) (Z : ℝ)
    (hX : ∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Z^(8:ℝ))
    (p : CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))
      (CenteredMomentSourceRow.supportedColumns (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))))
    (G : Id) (hG : G=p.val.1 ∨ G=p.val.2) (B : actualAllocations (tuplePools s) G)
    (J : Finset (liveIndices B.val)) :
    ((originalSelectedSource s hb cover G B J).R.absNorm:ℝ)≤Z^(8:ℝ) := by
  have hh := QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry.lab_cols_le
    (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) (Z^(8:ℝ)) hX ⟨p,∅⟩
  change ((s.R*G).absNorm:ℝ)≤Z^(8:ℝ)
  rw [hR,one_mul]
  rcases hG with h|h <;> rw [h]
  · exact hh.1
  · exact hh.2

#print axioms originalSelectedSource_canonical
#print axioms originalSelectedSource_grouped
#print axioms originalSelectedSource_R_cap
end
end QRH.Cycle092.ColoredGaussFrameProvider
