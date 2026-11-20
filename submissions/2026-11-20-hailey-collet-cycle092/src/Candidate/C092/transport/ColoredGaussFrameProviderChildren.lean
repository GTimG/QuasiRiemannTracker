/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Canonical original slots survive the actual allocation and whole-slot deletion. -/
import Candidate.C092.transport.ColoredGaussFrameProvider
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) subtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {L : ℝ} (θ : GData L)

/-- Only the number of surviving original marks changes. All moduli, masks,
    windows and original price parameters remain the same. -/
def withSlots (n : ℕ) : GData L := {θ with N:=n}

variable {θ} {mesh Z : ℝ}

/-- The literal surviving original index, after common allocation, selection
    and the native finite reindexing. -/
def originalIndex (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (i : Fin (Fintype.card (Rest J))) : Fin θ.N :=
  ((Fintype.equivFin (Rest J)).symm i).val.val

def selectedSource (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    Source (Fin (Fintype.card (Rest J))) θ.a θ.b :=
  reindexSource (restOf s hb cover G B J) (Fintype.equivFin (Rest J))

/-- The actual divided/selected source is canonical on exactly the surviving
    original marks. The inherited puncture and both ordinary prefixes are kept. -/
theorem selectedSource_canonical (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b)
    (cover : OriginalEnclosure s) (χ : Fin θ.N→RayQuotient.Characters θ.rayM θ.Hray)
    (w σ freq : Fin θ.N→ℝ) (t : ℝ) (R₀ : Fin θ.N→Finset Id)
    (hcan : Canonical s Z χ w σ freq t R₀ s.H s.R s.d)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    Canonical (θ:=withSlots θ (Fintype.card (Rest J))) (selectedSource s hb cover G B J) Z
      (fun i=>χ (originalIndex s hb cover G B J i))
      (fun i=>w (originalIndex s hb cover G B J i))
      (fun i=>σ (originalIndex s hb cover G B J i))
      (fun i=>freq (originalIndex s hb cover G B J i)) t
      (fun i=>R₀ (originalIndex s hb cover G B J i)) s.H
      (restOf s hb cover G B J).R (restOf s hb cover G B J).d := by
  refine ⟨hcan.S,rfl,?_,?_,?_,?_,rfl,rfl⟩
  · intro i
    exact hcan.pool (originalIndex s hb cover G B J i)
  · intro i
    exact hcan.ν (originalIndex s hb cover G B J i)
  · intro i
    exact hcan.Wslot (originalIndex s hb cover G B J i)
  · intro i
    exact hcan.P (originalIndex s hb cover G B J i)

#print axioms selectedSource_canonical
end
end QRH.Cycle092.ColoredGaussFrameProvider
