/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Native GSrc on actual Original canonical marks and the true divided lengths. -/
import Candidate.C092.transport.ColoredGaussFrameProviderOriginal
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
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance (priority := 2000) originalFrameSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {ι : Type*} [Fintype ι] {L : ℝ} {θ : GData L} {mesh Z : ℝ}
variable (s : Source ι θ.a θ.b) (hb : 0≤θ.b) (cover : OriginalEnclosure s)
variable (hZ : 1<Z) (χ : ι→RayQuotient.Characters θ.rayM θ.Hray)
variable (w σ freq : ι→ℝ) (t Vf : ℝ) (R₀ : ι→Finset Id)
variable (hw : ∀i,0≤w i) (hwm : ∀i,w i≤ mesh) (hσ : ∀i,σ i=33/50)
variable (hVf : 0≤Vf) (hfreq : ∀i,|freq i|≤Vf) (hR₀ : ∀i,(R₀ i).card≤θ.Holes)
variable (hX₁ : s.X₁≤Z^L) (hX₂ : s.X₂≤Z^L) (hY₁ : s.Y₁≤Z^L) (hY₂ : s.Y₂≤Z^L)
variable (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
variable (V₀ : O) (hV₀ : V₀≠0) (kLog : ℝ)

/-- All native data are the actual Original producer's fields, restricted to
    surviving marks. srcOf uses the genuinely divided ordinary lengths. -/
def originalFrame : GSrc (withSlots θ (Fintype.card (Rest J))) mesh Z :=
  srcOf (originalSelectedSource s hb cover G B J) hZ
    (fun i=>χ (originalSlot s hb cover G B J i))
    (fun i=>w (originalSlot s hb cover G B J i))
    (fun i=>σ (originalSlot s hb cover G B J i))
    (fun i=>freq (originalSlot s hb cover G B J i)) t Vf
    (fun i=>R₀ (originalSlot s hb cover G B J i))
    (fun i=>hw _) (fun i=>hwm _) (fun i=>hσ _) hVf (fun i=>hfreq _) (fun i=>hR₀ _)
    (by
      change s.X₁/((restOf s hb cover G B J).d.1.absNorm:ℝ)≤Z^L
      exact (div_le_self (s.hL.trans_le s.hX₁).le (nrm_one_le (restOf s hb cover G B J).hd.1)).trans hX₁)
    (by
      change s.X₂/((restOf s hb cover G B J).d.2.absNorm:ℝ)≤Z^L
      exact (div_le_self (s.hL.trans_le s.hX₂).le (nrm_one_le (restOf s hb cover G B J).hd.2)).trans hX₂)
    (by
      change s.Y₁/((restOf s hb cover G B J).d.1.absNorm:ℝ)≤Z^L
      exact (div_le_self (s.hL.trans_le s.hY₁).le (nrm_one_le (restOf s hb cover G B J).hd.1)).trans hY₁)
    (by
      change s.Y₂/((restOf s hb cover G B J).d.2.absNorm:ℝ)≤Z^L
      exact (div_le_self (s.hL.trans_le s.hY₂).le (nrm_one_le (restOf s hb cover G B J).hd.2)).trans hY₂)
    V₀ hV₀ kLog

local notation "gr" => originalFrame s hb cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀
  hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog

variable (hcan : MixedFirstActualNonexceptional.Canonical θ.rayM θ.Hray θ.hH θ.W θ.Cap θ.Lcap Z
  θ.η₀ χ w σ freq t R₀ s)

include hcan

theorem originalFrame_canonical :
    Canonical (originalSelectedSource s hb cover G B J) Z (gr).χ (gr).w (gr).σ (gr).freq (gr).t (gr).R₀
      s.H (restOf s hb cover G B J).R (1,1) :=
  originalSelectedSource_canonical s hb cover χ w σ freq t R₀ hcan G B J

theorem originalFrame_volume : (gr).vol=sourceVolume (originalSelectedSource s hb cover G B J) := by
  have hp := (originalFrame_canonical s hb cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀
    hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan).P
  unfold GSrc.vol sourceVolume
  simp only [hp]
  rfl

theorem originalFrame_volume_div_prefix :
    (gr).vol=sourceVolume (restOf s hb cover G B J)/
      (((restOf s hb cover G B J).d.1.absNorm:ℝ)*(restOf s hb cover G B J).d.2.absNorm) := by
  rw [originalFrame_volume s hb cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀
    hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan]
  unfold originalSelectedSource
  rw [sourceVolume_reindex,QRH.SilDensitySplit.CubeFree.Second.Provider.sourceVolume_renorm]
  rfl

omit hcan in
theorem originalSource_floor :
    (originalSelectedSource s hb cover G B J).L=(restOf s hb cover G B J).L/
      (((restOf s hb cover G B J).d.1.absNorm:ℝ)*(restOf s hb cover G B J).d.2.absNorm) := rfl

#print axioms originalFrame_canonical
#print axioms originalFrame_volume
#print axioms originalFrame_volume_div_prefix
#print axioms originalSource_floor
end
end QRH.Cycle092.ColoredGaussFrameProvider
