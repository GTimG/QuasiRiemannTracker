/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original admissible grouped window supplies the physical packed radius
and the upper dual frame relation used in the fixed-row price. -/
import Candidate.C092.transport.FixedFramePrice
import Submissions.sil_density_split_20261026.CubeFree.Second.SeamBUse
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths HeckeFamily
open QRH.SilDensitySplit.CubeFree
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
namespace QRH.Cycle092.FixedFramePacking
local notation "O" => HeckeFamily.O
variable {L mesh Z : ℝ} {θ : GData L}

def horizon (Z H mesh : ℝ) := Real.logb Z 2 + (H+mesh)

theorem rpow_horizon (hZ:1<Z) (H mesh : ℝ) :
    Z^(horizon Z H mesh)=2*Z^(H+mesh) := by
  rw [horizon,Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by norm_num)]

theorem native_row_cap {η:Character} (r : GSrc θ mesh Z) (x:GLabel θ mesh Z)
    (fit:Fits η r x) (H:ℝ) (he : |gEnvelope r x-H| ≤ mesh)
    (z:O) (hk:((Ideal.span {z}).absNorm:ℝ) ≤ 2*CenteredMomentSectorLocalization.dyadicScale (x.n 1)) :
    ((Ideal.span {(r.V₀*x.twist)*z}).absNorm:ℝ)≤Z^(horizon Z H mesh) := by
  have hZ:=zero_lt_one.trans r.hZ
  have hp:=absNorm_span_pos _ (mul_ne_zero r.hV₀ fit.twist_ne)
  have heq: ((Ideal.span {r.V₀*x.twist}).absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (x.n 1)=Z^(gEnvelope r x) :=
    (Real.rpow_logb hZ r.hZ.ne' (mul_pos hp (CenteredMomentSectorLocalization.dyadicScale_pos _))).symm
  have he':gEnvelope r x ≤ H+mesh := by linarith [(abs_le.mp he).2]
  rw [absNorm_span_mul,rpow_horizon r.hZ]
  calc
    _ ≤ ((Ideal.span {r.V₀*x.twist}).absNorm:ℝ)*(2*CenteredMomentSectorLocalization.dyadicScale (x.n 1)) :=
      mul_le_mul_of_nonneg_left hk hp.le
    _ = 2*Z^(gEnvelope r x) := by rw [←heq];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le r.hZ.le he') (by norm_num)

/-- The dual window in Fits is one-sided. Only that direction is needed. -/
theorem native_dual_upper {η:Character} (r : GSrc θ mesh Z) (x:GLabel θ mesh Z)
    (fit:Fits η r x) (H:ℝ) (he : |gEnvelope r x-H| ≤ mesh) :
    horizon Z H mesh ≤ 2*r.colLog-r.kLog+r.twistLog+(3*mesh+Real.logb Z 2) := by
  have h:= (abs_le.mp he).1
  rw [gEnvelope_eq r x fit.twist_ne] at h
  unfold horizon
  linarith [fit.dual]

/-- The genuinely available upper relation suffices for P7. The constants
show all frame collars separately, including the dyadic factor two. -/
theorem native_frame_excess {η:Character} (r:GSrc θ mesh Z) (x:GLabel θ mesh Z)
    (fit:Fits η r x) {H A₀ c u' Lf err:ℝ} (he:|gEnvelope r x-H| ≤ mesh)
    (hA : A₀ ≤ 9179599/10000000) (hu:u'≤(QRH.SourceCertificate.u:ℝ))
    (ha:r.colLog≤A₀-c-u'+err)
    (hfill:1-6*u' ≤ horizon Z H mesh+err)
    (hmin:max 0 (115/1000-c) ≤ Real.logb Z (max 1 Lf)+err) :
    r.kLog + horizon Z H mesh/6 - Real.logb Z (max 1 Lf) -
        (r.colLog+r.twistLog+u') ≤ -(3036/100000) +
         (3*mesh+Real.logb Z 2) + (17/6)*err := by
  have hd:=native_dual_upper r x fit H he
  have hl:=le_max_right 0 ((115/1000:ℝ)-c)
  norm_num [QRH.SourceCertificate.u] at hu
  linarith

#print axioms native_row_cap
#print axioms native_dual_upper
#print axioms native_frame_excess
end QRH.Cycle092.FixedFramePacking
