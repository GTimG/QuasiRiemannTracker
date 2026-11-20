/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Genuine native frame source on the surviving original marks. -/
import Candidate.C092.transport.ColoredGaussFrameProviderRenorm
import Candidate.C092.transport.ColoredGaussFrameProviderFrame
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
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) normalizedFrameSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- Native srcOf with the original mark vectors restricted to the actual
    surviving slots. No fitness or energy premise is used in this construction. -/
def normalizedFrame (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b) (cover : OriginalEnclosure s)
    (r : GSrc θ mesh Z) (hX₁ : r.X₁=s.X₁) (hX₂ : r.X₂=s.X₂)
    (hY₁ : r.Y₁=s.Y₁) (hY₂ : r.Y₂=s.Y₂)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (kLog : ℝ) : GSrc (withSlots θ (Fintype.card (Rest J))) mesh Z :=
  srcOf (normalizedSelectedSource s hb cover G B J) r.hZ
    (fun i=>r.χ (originalIndex s hb cover G B J i))
    (fun i=>r.w (originalIndex s hb cover G B J i))
    (fun i=>r.σ (originalIndex s hb cover G B J i))
    (fun i=>r.freq (originalIndex s hb cover G B J i)) r.t r.Vf
    (fun i=>r.R₀ (originalIndex s hb cover G B J i))
    (fun i=>r.hw _) (fun i=>r.hwm _) (fun i=>r.hσ _) r.hVf (fun i=>r.hfreq _)
    (fun i=>r.hR₀ _)
    (by
      change s.X₁/((restOf s hb cover G B J).d.1.absNorm:ℝ) ≤ Z^L
      apply (div_le_self (s.hL.trans_le s.hX₁).le
        (QRH.SilDensitySplit.CubeFree.Second.Provider.nrm_one_le (restOf s hb cover G B J).hd.1)).trans
      rw [←hX₁];exact r.hX₁L)
    (by
      change s.X₂/((restOf s hb cover G B J).d.2.absNorm:ℝ) ≤ Z^L
      apply (div_le_self (s.hL.trans_le s.hX₂).le
        (QRH.SilDensitySplit.CubeFree.Second.Provider.nrm_one_le (restOf s hb cover G B J).hd.2)).trans
      rw [←hX₂];exact r.hX₂L)
    (by
      change s.Y₁/((restOf s hb cover G B J).d.1.absNorm:ℝ) ≤ Z^L
      apply (div_le_self (s.hL.trans_le s.hY₁).le
        (QRH.SilDensitySplit.CubeFree.Second.Provider.nrm_one_le (restOf s hb cover G B J).hd.1)).trans
      rw [←hY₁];exact r.hY₁L)
    (by
      change s.Y₂/((restOf s hb cover G B J).d.2.absNorm:ℝ) ≤ Z^L
      apply (div_le_self (s.hL.trans_le s.hY₂).le
        (QRH.SilDensitySplit.CubeFree.Second.Provider.nrm_one_le (restOf s hb cover G B J).hd.2)).trans
      rw [←hY₂];exact r.hY₂L)
    r.V₀ r.hV₀ kLog

theorem normalizedFrame_canonical (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b)
    (cover : OriginalEnclosure s) (r : GSrc θ mesh Z)
    (hX₁ : r.X₁=s.X₁) (hX₂ : r.X₂=s.X₂) (hY₁ : r.Y₁=s.Y₁) (hY₂ : r.Y₂=s.Y₂)
    (hcan : Canonical s Z r.χ r.w r.σ r.freq r.t r.R₀ s.H s.R s.d)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) (kLog : ℝ) :
    let r' := normalizedFrame s hb cover r hX₁ hX₂ hY₁ hY₂ G B J kLog
    Canonical (normalizedSelectedSource s hb cover G B J) Z r'.χ r'.w r'.σ r'.freq r'.t r'.R₀ s.H
      (restOf s hb cover G B J).R (1,1) :=
  normalizedSelectedSource_canonical s hb cover r.χ r.w r.σ r.freq r.t r.R₀ hcan G B J

/-- The frame volume is the actual selected source volume. This does not
    replace the original full denominator of the outer allocation ledger. -/
theorem normalizedFrame_volume (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b)
    (cover : OriginalEnclosure s) (r : GSrc θ mesh Z)
    (hX₁ : r.X₁=s.X₁) (hX₂ : r.X₂=s.X₂) (hY₁ : r.Y₁=s.Y₁) (hY₂ : r.Y₂=s.Y₂)
    (hcan : Canonical s Z r.χ r.w r.σ r.freq r.t r.R₀ s.H s.R s.d)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) (kLog : ℝ) :
    (normalizedFrame s hb cover r hX₁ hX₂ hY₁ hY₂ G B J kLog).vol =
      sourceVolume (normalizedSelectedSource s hb cover G B J) := by
  let r' := normalizedFrame s hb cover r hX₁ hX₂ hY₁ hY₂ G B J kLog
  have hp := (normalizedFrame_canonical s hb cover r hX₁ hX₂ hY₁ hY₂ hcan G B J kLog).P
  unfold GSrc.vol sourceVolume
  simp only [hp]
  rfl

theorem sourceVolume_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {a b : ℝ}
    (s : Source ι a b) (e : ι≃κ) : sourceVolume (reindexSource s e)=sourceVolume s := by
  change s.X₁*s.X₂*(∏i,s.P (e.symm i))=s.X₁*s.X₂*(∏i,s.P i)
  rw [Fintype.prod_equiv e.symm (fun i=>s.P (e.symm i)) s.P (fun _=>rfl)]

theorem normalizedFrame_volume_div_prefix (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b)
    (cover : OriginalEnclosure s) (r : GSrc θ mesh Z)
    (hX₁ : r.X₁=s.X₁) (hX₂ : r.X₂=s.X₂) (hY₁ : r.Y₁=s.Y₁) (hY₂ : r.Y₂=s.Y₂)
    (hcan : Canonical s Z r.χ r.w r.σ r.freq r.t r.R₀ s.H s.R s.d)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) (kLog : ℝ) :
    (normalizedFrame s hb cover r hX₁ hX₂ hY₁ hY₂ G B J kLog).vol =
      sourceVolume (restOf s hb cover G B J) /
        (((restOf s hb cover G B J).d.1.absNorm:ℝ)*(restOf s hb cover G B J).d.2.absNorm) := by
  rw [normalizedFrame_volume s hb cover r hX₁ hX₂ hY₁ hY₂ hcan G B J kLog]
  unfold normalizedSelectedSource
  rw [sourceVolume_reindex,QRH.SilDensitySplit.CubeFree.Second.Provider.sourceVolume_renorm]
  rfl

theorem normalizedSource_floor (s : Source (Fin θ.N) θ.a θ.b) (hb : 0≤θ.b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (J : Finset (liveIndices B.val)) :
    (normalizedSelectedSource s hb cover G B J).L = (restOf s hb cover G B J).L /
      (((restOf s hb cover G B J).d.1.absNorm:ℝ)*(restOf s hb cover G B J).d.2.absNorm) := rfl

#print axioms normalizedFrame_canonical
#print axioms normalizedFrame_volume
#print axioms normalizedFrame_volume_div_prefix
#print axioms normalizedSource_floor
end
end QRH.Cycle092.ColoredGaussFrameProvider
