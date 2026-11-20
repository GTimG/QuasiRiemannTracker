/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected second scale is 16 K W^4. Account for its complete
two-to-the-number-of-slots factor when deriving the filled radius. -/
import Candidate.C092.transport.FixedFirstGeometry
import Candidate.C092.transport.TwistedRawBallAllocation
import Candidate.C092.transport.RawSidesZeroTailSource
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Provider QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O
variable {ι:Type} [Fintype ι] {a b:ℝ}
local instance (priority := 2000) c092LocalInst_Candidate_C092_transport_FixedFirstFilled_910943fc513928e1_001 {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

theorem lower_volume (s:Source ι a b) (hb:0≤b) (cover:OriginalEnclosure s) (G:Id)
    (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val)) (hd:s.d=(1,1))
    (ω₁ ω₂:Id→ℂ) (hw:TwistedRawBall.allocationWeight s ω₁ ω₂ G B≠0) :
    sourceVolume s ≤ sourceVolume (renorm (restOf s hb cover G B J))*
      (∏ j:J,s.P j.val.val)*(G.absNorm:ℝ) := by
  have hs : TwistedRawBall.allocationScalar s ω₁ ω₂ G B ≠ 0 := by
    intro he;apply hw;simp only [TwistedRawBall.allocationWeight,he,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
  have hn : allocWeight s G B ≠ 0 := by
    change _*_*_ ≠ 0 at hs
    exact mul_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hs)) (right_ne_zero_of_mul hs)
  have h:=live_volume_ge s hb cover G B (frozen_ge_of_weight s G B hn)
  rw [hd] at h
  have hk:=rest_volume_mul (allocatedLiveSource s hb cover G B) (fun _=>rfl) J
  change sourceVolume (renorm (restOf s hb cover G B J))*(∏j:J,s.P j.val.val)=_ at hk
  rw [hk];simpa [nrm] using h

theorem selection_scale (s:Source ι a b) (hb:0≤b) (cover:OriginalEnclosure s) (G:Id)
    (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val)) :
    RawSides.selectionScaleQ s hb cover G B J =
      (2:ℝ)^J.card*(∏ j:J,s.P j.val.val) := by
  unfold RawSides.selectionScaleQ
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  congr 1
  exact (Finset.prod_coe_sort J (fun j:liveIndices B.val=>s.P j.val)).symm

/-- Non-logarithmic form on the original active child. The last premise is
the genuine native first-radius inequality, supplied in both orientations. -/
theorem selected_radius_payment (s:Source ι a b) (hb:0≤b) (cover:OriginalEnclosure s) (G:Id)
    (hG:G≠0) (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val)) (hd:s.d=(1,1))
    (ω₁ ω₂:Id→ℂ) (hw:TwistedRawBall.allocationWeight s ω₁ ω₂ G B≠0)
    (Z V K κ : ℝ) (hZ:1<Z) (hV:0≤V) (hK:0≤K)
    (hfirst: K*(G.absNorm:ℝ)^2*Z≤4*V*(sourceVolume s)^2*Z^((3/2)*κ)) :
    let p:=∏ j:J,s.P j.val.val
    let vol:=sourceVolume (renorm (restOf s hb cover G B J))
    (16*K*(RawSides.selectionScaleQ s hb cover G B J)^4)*Z ≤
      (64*((2:ℝ)^J.card)^4)*V*vol^2*p^6*Z^((3/2)*κ) := by
  dsimp only
  let p:=∏ j:J,s.P j.val.val
  let vol:=sourceVolume (renorm (restOf s hb cover G B J))
  have hlo:=lower_volume s hb cover G B J hd ω₁ ω₂ hw
  change sourceVolume s ≤ vol*p*(G.absNorm:ℝ) at hlo
  have hsq := pow_le_pow_left₀ (sourceVolume_pos s).le hlo 2
  have hfirst' := le_trans hfirst (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by linarith : 0≤4*V))
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  have hn:0<(G.absNorm:ℝ):=nrm_pos hG
  have hred : K*Z ≤ 4*V*vol^2*p^2*Z^((3/2)*κ) := by
    apply le_of_mul_le_mul_right (a:=(G.absNorm:ℝ)^2) _ (sq_pos_of_pos hn)
    convert hfirst' using 1 <;> ring
  rw [selection_scale]
  change 16*K*((2:ℝ)^J.card*p)^4*Z ≤ _
  have hmul := mul_le_mul_of_nonneg_left hred (by positivity : 0≤16*((2:ℝ)^J.card)^4*p^4)
  convert hmul using 1 <;> ring

#print axioms lower_volume
#print axioms selection_scale
#print axioms selected_radius_payment
end QRH.Cycle092.FixedFramePacking
