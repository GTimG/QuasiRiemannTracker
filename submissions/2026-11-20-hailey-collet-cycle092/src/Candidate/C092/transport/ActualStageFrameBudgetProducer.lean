/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native frames on the actual original marks and residual ordinary lengths,
placed in the early finite slot-count bank without auxiliary geometry. -/
import Candidate.C092.transport.ActualStageFrameBudgetData
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.ColoredGaussFrameProvider
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) producerSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type*} [Fintype ι]
variable (N:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
variable (hHr:RayOrthogonality.globalUnits rayM ≤ Hr)
variable (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
variable (base:Character)(Q:Id)(hQ:Q ≤ rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
variable (hQ72:Q ≤ Ideal.span {(72:O)})(hQbase:Q ≤ base.modulus)
local notation "Θ"=>frameData N 0 rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase
variable {mesh Z:ℝ}(s:Source ι (1/4) (9/4))(cover:OriginalEnclosure s)(hZ:1<Z)
variable (χ:ι→RayQuotient.Characters rayM Hr)(w σ freq:ι→ℝ)(t Vf:ℝ)(R₀:ι→Finset Id)
variable (hw:∀i,0 ≤ w i)(hwm:∀i,w i ≤ mesh)(hσ:∀i,σ i=33/50)
variable (hVf:0 ≤ Vf)(hfreq:∀i,|freq i| ≤ Vf)(hR₀:∀i,(R₀ i).card ≤ 2*N)
variable (hX₁:s.X₁ ≤ Z^(3:ℝ))(hX₂:s.X₂ ≤ Z^(3:ℝ))
variable (hY₁:s.Y₁ ≤ Z^(3:ℝ))(hY₂:s.Y₂ ≤ Z^(3:ℝ))
variable (G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val))
variable (V₀:O)(hV₀:V₀≠0)(kLog:ℝ)

/-- Only the surviving-slot index is chosen at this stage. All other native
parameters were fixed before the scale, allocation and first label. -/
def bankFrame : GSrc
    (frameData N (Fintype.card (Rest J)) rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase) mesh Z :=
  originalFrame (θ:=Θ) s (by norm_num [frameData]) cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀
    hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog

local notation "rs"=>bankFrame N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase
  s cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog

variable (hcan:MixedFirstActualNonexceptional.Canonical rayM Hr hHr W 16 8 Z base χ w σ freq t R₀ s)

include hcan in
theorem bankFrame_canonical : Canonical
    (originalSelectedSource s (by norm_num [frameData]) cover G B J) Z (rs).χ (rs).w (rs).σ (rs).freq (rs).t (rs).R₀
    s.H (restOf s (by norm_num [frameData]) cover G B J).R (1,1) :=
  originalFrame_canonical (θ:=Θ) s (by norm_num [frameData]) cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀
    hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan

include hcan in
theorem bankFrame_volume : (rs).vol=sourceVolume (originalSelectedSource s (by norm_num [frameData]) cover G B J) :=
  originalFrame_volume (θ:=Θ) s (by norm_num [frameData]) cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀
    hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan

/-- Independent original pitches survive unchanged through the physical
source. The native frame convention divides each pitch by 2 pi once. -/
theorem bankFrame_pitches : (rs).t₁=s.t₁/(2*Real.pi) ∧ (rs).t₂=s.t₂/(2*Real.pi) := ⟨rfl,rfl⟩

theorem bankFrame_radius : (rs).kLog=kLog ∧ (rs).V₀=V₀ := ⟨rfl,rfl⟩

#print axioms bankFrame_canonical
#print axioms bankFrame_volume
#print axioms bankFrame_pitches
#print axioms bankFrame_radius
end
end QRH.Cycle092.ActualStageFrameBudget
