/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Mathlib.Tactic

set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section

def naturalLow (a Bc sigma k t K b F c d J : ℝ) : ℝ :=
  -a-Bc-sigma+k*max (t+K*b-F-min c d-J) 0

def naturalDelta (a k t K b F : ℝ) : ℝ := k*(t+K*b-F)-a

/-- Favorable reductions are dropped before, rather than after, clipping the
natural defect. -/
theorem natural_low_clipped (a Bc sigma k t K b F c d J : ℝ)
    (hk : 0 ≤ k) (hJ : 0 ≤ J) :
    naturalLow a Bc sigma k t K b F c d J ≤
      max (-a) (naturalDelta a k t K b F-k*min c d)-Bc-sigma := by
  dsimp [naturalLow,naturalDelta]
  by_cases hpos : 0 ≤ t+K*b-F-min c d-J
  · rw [max_eq_left hpos]
    have hm := le_max_right (-a) (k*(t+K*b-F)-a-k*min c d)
    nlinarith only [hm,mul_nonneg hk hJ]
  · rw [max_eq_right (le_of_lt (lt_of_not_ge hpos))]
    have hm := le_max_left (-a) (k*(t+K*b-F)-a-k*min c d)
    linarith

theorem common_penalty (k c d sigma : ℝ) (hk : 0 ≤ k) (hkhi : k ≤ 3/4)
    (hsigma : 0 ≤ sigma) (hcone : c+d ≤ 3*min c d+4*sigma) :
    k*(c+d)/3 ≤ k*min c d+sigma := by
  have h := mul_le_mul_of_nonneg_left hcone hk
  have h' := mul_le_mul_of_nonneg_right hkhi hsigma
  nlinarith only [h,h']

theorem natural_low_outside_cut (a Bc sigma k t K b F c d J u : ℝ)
    (ha : 0 ≤ a) (hBc : 0 ≤ Bc) (hsigma : 0 ≤ sigma)
    (hk : 0 ≤ k) (hkhi : k ≤ 3/4) (hJ : 0 ≤ J)
    (hcone : c+d ≤ 3*min c d+4*sigma) (hout : u ≤ c+d)
    (hcut : 3*naturalDelta a k t K b F ≤ k*u) :
    naturalLow a Bc sigma k t K b F c d J ≤ 0 := by
  apply (natural_low_clipped a Bc sigma k t K b F c d J hk hJ).trans
  have hp := common_penalty k c d sigma hk hkhi hsigma hcone
  have hu := mul_le_mul_of_nonneg_left hout hk
  have hmax : max (-a) (naturalDelta a k t K b F-k*min c d) ≤ Bc+sigma := by
    apply max_le
    · linarith
    · linarith
  linarith

def rawExcess (a R E Bc Lc R0c g2 t2 b2 sigma : ℝ) : ℝ :=
  -a-2*R-E-Bc+Lc+R0c+g2-t2-b2-sigma

def rawGap (a q b t B F lam : ℝ) : ℝ := a-q*(b+(t-B*F)/lam)

def rawCommon (R Bc Lc R0c sigma q lam c B d : ℝ) : ℝ :=
  -2*R-Bc+Lc+R0c-sigma-(q/lam)*(c+B*(Lc-R-max (c-d) 0))

/-- The exact first-cap identity. The frozen-width term retains its sign. -/
theorem raw_erasure_identity (a R E Bc Lc R0c g2 t2 b2 sigma q lam c B d b t f F : ℝ)
    (hlam : lam ≠ 0) :
    rawExcess a R E Bc Lc R0c g2 t2 b2 sigma+
      q*((b-f)-(B*(F+Lc-R-max (c-d) 0)-(t-c+f))/lam) =
    -rawGap a q b t B F lam+rawCommon R Bc Lc R0c sigma q lam c B d-
      E-(b2-g2+t2)-(q-q/lam)*f := by
  dsimp [rawExcess,rawGap,rawCommon]
  field_simp
  <;> ring

/-- R15 follows with the one-slot mesh price and all favorable terms paid. -/
theorem raw_low_after_erasure (a R E Bc Lc R0c g2 t2 b2 sigma q lam c B d b t f F mesh : ℝ)
    (hlam : 1 ≤ lam) (hq : 0 ≤ q) (hE : 0 ≤ E)
    (hsecond : 0 ≤ b2-g2+t2) (hf : 0 ≤ f) :
    rawExcess a R E Bc Lc R0c g2 t2 b2 sigma+
      q*((b-f)-(B*(F+Lc-R-max (c-d) 0)-(t-c+f))/lam+mesh) ≤
    -rawGap a q b t B F lam+rawCommon R Bc Lc R0c sigma q lam c B d+q*mesh := by
  have hL : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hqdiv : q/lam ≤ q := (div_le_iff₀ hL).mpr (by nlinarith only [mul_nonneg hq (sub_nonneg.mpr hlam)])
  have hid := raw_erasure_identity a R E Bc Lc R0c g2 t2 b2 sigma q lam c B d b t f F hL.ne'
  nlinarith only [hid,hE,hsecond,mul_nonneg (sub_nonneg.mpr hqdiv) hf]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.natural_low_clipped
#print axioms QRH.Record12518109Source.common_penalty
#print axioms QRH.Record12518109Source.natural_low_outside_cut
#print axioms QRH.Record12518109Source.raw_erasure_identity
#print axioms QRH.Record12518109Source.raw_low_after_erasure
