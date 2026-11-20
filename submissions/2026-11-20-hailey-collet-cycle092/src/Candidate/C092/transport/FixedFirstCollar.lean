/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Quantified filled-radius lower edge in the same units as the common native
group. The six selected widths and every dyadic constant are explicit. -/
import Candidate.C092.transport.FixedFirstFilled
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Provider QRH.SilDensitySplit.CubeFree.Second.Concrete
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O
variable {ι:Type} [Fintype ι] {a b:ℝ}
local instance (priority := 2000) c092LocalInst_Candidate_C092_transport_FixedFirstCollar_299beee140f18baa_001 {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

theorem radius_log (s:Source ι a b) (hb:0 ≤ b) (cover:OriginalEnclosure s) (G:Id)
    (hG:G≠0) (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val)) (hd:s.d=(1,1))
    (ω₁ ω₂:Id→ℂ) (hw:TwistedRawBall.allocationWeight s ω₁ ω₂ G B≠0)
    (Z V K κ:ℝ) (hZ:1<Z) (hV:0<V) (hK:0<K)
    (hfirst:K*(G.absNorm:ℝ)^2*Z ≤ 4*V*(sourceVolume s)^2*Z^((3/2)*κ))
    (w:ι→ℝ) (hP:∀i,s.P i=Z^(w i)) :
    let vol:=sourceVolume (renorm (restOf s hb cover G B J))
    let K₂:=16*K*(RawSides.selectionScaleQ s hb cover G B J)^4
    1-6*(∑j∈J,w j.val) ≤
      2*Real.logb Z vol-Real.logb Z K₂+Real.logb Z V+
        (Real.logb Z (64*((2:ℝ)^J.card)^4)+(3/2)*κ) := by
  let vol:=sourceVolume (renorm (restOf s hb cover G B J))
  let p:=∏j:J,s.P j.val.val
  let K₂:=16*K*(RawSides.selectionScaleQ s hb cover G B J)^4
  let C:=64*((2:ℝ)^J.card)^4
  have hp':0<p:=Finset.prod_pos (fun j _=>zero_lt_one.trans_le (s.hP j.val.val))
  have hs:=selected_radius_payment s hb cover G hG B J hd ω₁ ω₂ hw Z V K κ hZ hV.le hK.le hfirst
  change K₂*Z ≤ C*V*vol^2*p^6*Z^((3/2)*κ) at hs
  have hv':0<vol:=sourceVolume_pos _
  have hC:0<C:=by dsimp [C];positivity
  have hK₂:0<K₂:=by dsimp [K₂]; rw [selection_scale]; change 0<16*K*((2:ℝ)^J.card*p)^4;positivity
  have hl:=Real.logb_le_logb_of_le hZ (mul_pos hK₂ (zero_lt_one.trans hZ)) hs
  rw [Real.logb_mul hK₂.ne' (zero_lt_one.trans hZ).ne',Real.logb_self_eq_one hZ] at hl
  rw [Real.logb_mul (by positivity : 0<C*V*vol^2*p^6).ne' (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    Real.logb_mul (by positivity : 0<C*V*vol^2).ne' (pow_pos hp' _).ne',
    Real.logb_mul (mul_pos hC hV).ne' (pow_pos hv' _).ne',Real.logb_mul hC.ne' hV.ne',
    Real.logb_pow,Real.logb_pow] at hl
  have he : p = Z^(∑ j∈J,w j.val) := by
    dsimp only [p];simp_rw [hP];rw [←Finset.sum_coe_sort,Real.rpow_sum_of_pos (zero_lt_one.trans hZ)]
  rw [he,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  change 1-6*(∑j∈J,w j.val) ≤ 2*Real.logb Z vol-Real.logb Z K₂+Real.logb Z V+(Real.logb Z C+(3/2)*κ)
  norm_num at hl
  linarith

#print axioms radius_log
end QRH.Cycle092.FixedFramePacking
