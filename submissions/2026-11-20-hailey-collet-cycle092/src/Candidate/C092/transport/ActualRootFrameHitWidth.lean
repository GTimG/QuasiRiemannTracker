/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact surviving-slot weight sum for the existing concrete native bankFrame. -/
import Candidate.C092.transport.ActualStageFrameBudgetProducer
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualRootFrameHit
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.ColoredGaussFrameProvider QRH.Cycle092.ActualStageFrameBudget
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) widthHitSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type} [Fintype ι]
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

local notation "rs"=>bankFrame N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase
  s cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog

/-- The native Fin index is exactly a reindex of the surviving physical
    marks. No width is lost or duplicated in the bank constructor. -/
theorem bank_wsum : (∑ i, (rs).w i) = ∑ j : Rest J, w j.val.val := by
  change (∑ i : Fin (Fintype.card (Rest J)),
    w (((Fintype.equivFin (Rest J)).symm i).val.val)) = _
  exact (Fintype.equivFin (Rest J)).symm.sum_comp (fun j : Rest J => w j.val.val)

theorem bank_mark_time : (rs).t=t := rfl

theorem bank_frequency_bound : (rs).Vf=Vf := rfl

#print axioms bank_wsum
#print axioms bank_mark_time
#print axioms bank_frequency_bound
end
end QRH.Cycle092.ActualRootFrameHit
