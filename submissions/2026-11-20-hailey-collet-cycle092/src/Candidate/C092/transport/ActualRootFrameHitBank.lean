/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Complete projector hits for the EXISTING concrete native bankFrame. -/
import Candidate.C092.transport.ActualRootFrameHitSupport
import Candidate.C092.transport.ActualColoredCutoff
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
local instance (priority := 2000) bankHitSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
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

variable (hcan:MixedFirstActualNonexceptional.Canonical rayM Hr hHr W 16 8 Z base χ w σ freq t R₀ s)


local notation "child"=>originalSelectedSource s (by norm_num) cover G B J

theorem bank_fields :
    (rs).W₁=(child).W₁ ∧ (rs).W₂=(child).W₂ ∧
    (rs).t₁=(child).t₁/(2*Real.pi) ∧ (rs).t₂=(child).t₂/(2*Real.pi) ∧
    (rs).X₁=(child).X₁ ∧ (rs).X₂=(child).X₂ ∧ (rs).Y₁=(child).Y₁ ∧ (rs).Y₂=(child).Y₂ ∧
    (rs).V₀=V₀ ∧ (rs).kLog=kLog ∧ (child).d=(1,1) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

include hcan in
theorem bank_canonical_self : Canonical (child) Z (rs).χ (rs).w (rs).σ (rs).freq (rs).t (rs).R₀
    (child).H (child).R (child).d :=
  ActualStageFrameBudget.bankFrame_canonical N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase s cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan

include hcan in
theorem bank_volume_rest : (rs).vol=sourceVolume (renorm (restOf s (by norm_num) cover G B J)) := by
  rw [ActualStageFrameBudget.bankFrame_volume N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase s cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan]
  exact selected_volume_eq (a:=1/4) (b:=9/4) s (by norm_num : (0:ℝ) ≤ 9/4) cover G B J

include hcan in
theorem bank_volume_prefix : (rs).vol=sourceVolume (restOf s (by norm_num) cover G B J)/
    (((restOf s (by norm_num) cover G B J).d.1.absNorm:ℝ)*(restOf s (by norm_num) cover G B J).d.2.absNorm) := by
  rw [bank_volume_rest N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase s cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan,sourceVolume_renorm]
  rfl

include hcan in
theorem bank_colLog : (rs).colLog=Real.logb Z (sourceVolume (child)) := by
  unfold GSrc.colLog
  rw [ActualStageFrameBudget.bankFrame_volume N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase s cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan]

theorem bank_internalQ : internalQ (frameData N (Fintype.card (Rest J)) rayM Hr hHr W hW hWs base Q
    hQ hQ0 hQt hQ72 hQbase).Q (frameData N (Fintype.card (Rest J)) rayM Hr hHr W hW hWs base Q
    hQ hQ0 hQt hQ72 hQbase).η₀=Q := by
  change Q ⊓ base.modulus=Q
  exact inf_eq_left.mpr hQbase

theorem bank_power_radius (K:ℝ)(hK:0<K)(hlog:kLog=Real.logb Z K) : Z^(rs).kLog=K := by
  change Z^kLog=K
  rw [hlog]
  exact Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hK

include hcan in
theorem bank_frequency_cutoff (ω₁ ω₂:Id→*₀ℂ)
    (active:(RootColoredSeed.active (child) (by norm_num) ω₁ ω₂).Nonempty)
    (K ξ:ℝ)(hK:0<K)(hlog:kLog=Real.logb Z K)
    (hpay:32*((9/4:ℝ)^2*(2:ℝ)^Fintype.card (Rest J))^2*Z^(ξ/2) ≤ Z^mesh) :
    32*frequencyRadius
      ((RawSides.residualCapQ (restOf s (by norm_num) cover G B J))^2/K) Z ξ ≤ Z^(cutoffLog (rs)) := by
  have act:(RootColoredSeed.active (restOf s (by norm_num) cover G B J) (by norm_num) ω₁ ω₂).Nonempty := by
    rw [selected_active_eq] at active
    exact active
  apply FixedFramePacking.frequency_cutoff (rs) (restOf s (by norm_num) cover G B J) (by norm_num)
    ω₁ ω₂ act K ξ hK (by exact hlog) (bank_volume_prefix N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase s cover hZ χ w σ freq t Vf R₀ hw hwm hσ hVf hfreq hR₀ hX₁ hX₂ hY₁ hY₂ G B J V₀ hV₀ kLog hcan) hpay

#print axioms bank_fields
#print axioms bank_canonical_self
#print axioms bank_volume_rest
#print axioms bank_colLog
#print axioms bank_internalQ
#print axioms bank_frequency_cutoff
end
end QRH.Cycle092.ActualRootFrameHit
