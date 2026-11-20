/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Lower and upper common group horizons from the *same* true first common
ideal, selected prefix and scaled second radius. -/
import Candidate.C092.transport.FirstLabelRadius
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.SilDensitySplit.CubeFree FP MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedInnerExceptionalBlock MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Packet.Grouped Second.ConcreteGroup
open Second.Provider Second.Concrete CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform
namespace QRH.Cycle092.FixedFramePacking
local notation "Id"=>Ideal HeckeFamily.O
variable {ι:Type} [Fintype ι] {a b L mesh Z:ℝ} {θ:GData L}
local instance (priority := 2000) c092LocalInst_Candidate_C092_transport_FirstGroupWindow_1055a62110a90b4d_001 {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

theorem actual_window (r:GSrc θ mesh Z) (s:Source ι a b) (hb:0≤b) (cover:OriginalEnclosure s)
    (G:Id) (hG:G≠0) (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val))
    (hd:s.d=(1,1)) (ω₁ ω₂:Id→ℂ) (hwt:TwistedRawBall.allocationWeight s ω₁ ω₂ G B≠0)
    (w:ι→ℝ) (hw:∀i,0≤w i) (hP:∀i,s.P i=Z^(w i)) (K κ aRoot:ℝ)
    (hK:1/2≤K) (hcap:sourceVolume s ≤ Z^aRoot)
    (hvol:r.vol=sourceVolume (renorm (restOf s hb cover G B J)))
    (hk:r.kLog=Real.logb Z (16*K*(RawSides.selectionScaleQ s hb cover G B J)^4))
    (htwist:((Ideal.span {r.V₀}).absNorm:ℝ) ≤ (G.absNorm:ℝ)^2)
    (hfirst:K*(G.absNorm:ℝ)^2*Z ≤ 4*((Ideal.span {r.V₀}).absNorm:ℝ)*(sourceVolume s)^2*Z^((3/2)*κ)) :
    let u':=∑j∈J,w j.val
    1-6*u'+mesh-(Real.logb Z (64*((2:ℝ)^J.card)^4)+(3/2)*κ) ≤ commonH r ∧
    commonH r ≤ 2*aRoot+2*Real.logb Z ((2:ℝ)^Fintype.card ι)+mesh := by
  have hZ:=r.hZ
  have hz:=zero_lt_one.trans hZ
  have hg:0<(G.absNorm:ℝ):=nrm_pos hG
  have hV:0<((Ideal.span {r.V₀}).absNorm:ℝ):=absNorm_span_pos _ r.hV₀
  have hK':0<K:=by linarith
  have hlow:=radius_log s hb cover G hG B J hd ω₁ ω₂ hwt Z _ K κ hZ hV hK' hfirst w hP
  dsimp only at hlow
  rw [←hvol,←hk] at hlow
  have hi:=first_volume s hb cover G B J
  rw [←hvol] at hi
  have hpp : 1 ≤ ∏ i:J,s.P i.val.val := by
    calc
      (1:ℝ)=∏ _i:J,(1:ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _=>zero_le_one) (fun i _=>s.hP i.val.val)
  have hvr:=r.vol_pos hz
  have hvc : r.vol*(G.absNorm:ℝ) ≤ (2:ℝ)^(Fintype.card ι)*Z^aRoot := calc
    _ ≤ (r.vol*(∏i:J,s.P i.val.val))*(G.absNorm:ℝ) :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hvr.le hpp) hg.le
    _ ≤ _ := hi.trans (mul_le_mul_of_nonneg_left hcap (by positivity))
  have hlog:=Real.logb_le_logb_of_le hZ (mul_pos hvr hg) hvc
  rw [Real.logb_mul hvr.ne' hg.ne',Real.logb_mul (by positivity : 0<(2:ℝ)^Fintype.card ι).ne'
    (Real.rpow_pos_of_pos hz _).ne',Real.logb_rpow hz hZ.ne'] at hlog
  have htw:=Real.logb_le_logb_of_le hZ hV htwist
  rw [Real.logb_pow] at htw
  have hscale:1≤RawSides.selectionScaleQ s hb cover G B J := by
    rw [selection_scale];exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hpp
  have hK0:0≤r.kLog:=by
    rw [hk];apply Real.logb_nonneg hZ
    have h4:=one_le_pow₀ hscale (n:=4)
    nlinarith only [hK,h4,mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr h4)]
  change (1-6*(∑j∈J,w j.val)+mesh-(_) ≤ 2*Real.logb Z r.vol-r.kLog+mesh+Real.logb Z _) ∧ _
  change 1-6*(∑j∈J,w j.val) ≤ 2*Real.logb Z r.vol-r.kLog+Real.logb Z _+_ at hlow
  constructor
  · linarith
  · unfold commonH cutoffLog GSrc.colLog GSrc.twistLog
    change Real.logb Z ((Ideal.span {r.V₀}).absNorm:ℝ) ≤ 2*Real.logb Z (G.absNorm:ℝ) at htw
    linarith only [hlog,hK0,htw]

#print axioms actual_window
end QRH.Cycle092.FixedFramePacking
