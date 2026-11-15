/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CoarseGates
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.HighGates

/-! Uniform structural HIGH gates. Only the actual long-branch reserve is
left as an input; all other conditions follow from one fixed rational box. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Set Qrh.TwoSlot.AnchorZeroLoss.High

theorem structural_high_gates {d : Stg} {fee : ℝ}
    (hR : d.R ∈ Icc (3/4:ℝ) (7/9)) (hH : d.H ∈ Icc (9/10:ℝ) 1)
    (hz : d.z ∈ Icc (0:ℝ) (11/10000))
    (hk : 45457/125000 ≤ d.k ∧ d.k < 1/2)
    (ha : d.a1 ∈ Icc (0:ℝ) (1/10))
    (hgap : d.z-d.a0+d.a1*d.R ∈ Icc (0:ℝ) (1/1000000))
    (hu : d.u ≤ 1/10000) (hF : fee < d.H*d.F0) : d.Hyp fee := by
  have hR0 : 0 < d.R := by linarith [hR.1]
  have hH0 : 0 < d.H := by linarith [hH.1]
  have hk0 : 0 < d.k := by linarith [hk.1]
  have hD : 2/5 ≤ d.D := by unfold Stg.D; linarith [ha.2]
  have hD0 : 0 < d.D := by linarith
  have hu0 : 0 ≤ d.u := by unfold Stg.u; linarith [hH.2]
  have hi : 1/d.k ≤ 3 := (div_le_iff₀ hk0).mpr (by linarith [hk.1])
  have huk : d.u/d.k ≤ 3*d.u := by
    have hm := mul_le_mul_of_nonneg_left hi hu0
    calc d.u/d.k = d.u*(1/d.k) := by ring
      _ ≤ d.u*3 := hm
      _ = 3*d.u := by ring
  have hnum (ν : ℝ) : d.g ν*d.D =
      d.H*(d.R*d.D+(d.z-d.a0+d.a1*d.R))+d.u/d.k-d.u/ν := by
    unfold Stg.g
    rw [div_mul_cancel₀ _ hD0.ne']
    unfold Stg.r Stg.s Stg.D
    ring
  have hDprod : (9/25:ℝ) ≤ d.H*d.D := by
    have h := mul_le_mul hH.1 hD (by norm_num : (0:ℝ) ≤ 2/5) hH0.le
    norm_num at h
    exact h
  have hbase : (27/125:ℝ) ≤ d.H*(d.R-1/2-d.z) := by
    have hb : (6/25:ℝ) ≤ d.R-1/2-d.z := by linarith [hR.1,hz.2]
    have h := mul_le_mul hH.1 hb (by norm_num : (0:ℝ) ≤ 6/25) hH0.le
    norm_num at h
    exact h
  have hfrac : d.u/(d.k*d.k)/d.D ≤ (45/2)*d.u := by
    have hkk : (1:ℝ) ≤ 9*(d.k*d.k) := by
      have hk3 : (1/3:ℝ) ≤ d.k := by linarith [hk.1]
      have hm := mul_le_mul hk3 hk3 (by norm_num : (0:ℝ) ≤ 1/3) hk0.le
      nlinarith only [hm]
    have hf : d.u/(d.k*d.k) ≤ 9*d.u := by
      rw [div_le_iff₀ (mul_pos hk0 hk0)]
      nlinarith only [mul_le_mul_of_nonneg_left hkk hu0]
    rw [div_le_iff₀ hD0]
    have hm := mul_le_mul_of_nonneg_left hD (show 0 ≤ (45/2)*d.u by positivity)
    nlinarith only [hf,hm]
  have hcorr : (3/2)*(5/6-d.k)*(d.u/(d.k*d.k))/d.D ≤ 30*d.u := by
    have hc : (3/2)*(5/6-d.k) ≤ 5/4 := by linarith [hk0]
    have hm := mul_le_mul hc hfrac (by positivity : 0 ≤ d.u/(d.k*d.k)/d.D)
      (by norm_num : (0:ℝ) ≤ 5/4)
    calc (3/2)*(5/6-d.k)*(d.u/(d.k*d.k))/d.D =
        (3/2)*(5/6-d.k)*(d.u/(d.k*d.k)/d.D) := by ring
      _ ≤ (5/4)*((45/2)*d.u) := hm
      _ ≤ 30*d.u := by linarith
  have hg9 : 0 ≤ d.gate9 := by
    have heq : d.gate9 = d.H*(d.R-1/2-d.z)-d.u/d.k-
        (3/2)*(5/6-d.k)*(d.u/(d.k*d.k))/d.D := by
      unfold Stg.gate9 Stg.r Stg.s
      ring
    rw [heq]
    linarith
  have hg10 : 3/100 < d.H+d.u-d.H/6-1/15-(3/4)*d.r-d.s := by
    have hc : (3/25:ℝ) ≤ 1/3-d.R/4-d.z := by linarith [hR.2,hz.2]
    have hm := mul_le_mul hH.1 hc (by norm_num : (0:ℝ) ≤ 3/25) hH0.le
    norm_num at hm
    have heq : d.H+d.u-d.H/6-1/15-(3/4)*d.r-d.s =
        d.H*(1/3-d.R/4-d.z)+d.u-d.u/d.k-1/15 := by
      unfold Stg.r Stg.s
      ring
    rw [heq]
    linarith
  have hlow : d.R ≤ d.g d.k/d.H := by
    rw [le_div_iff₀ hH0]
    apply (mul_le_mul_iff_right₀ hD0).mp
    have he := hnum d.k
    have hn := mul_nonneg hH0.le hgap.1
    nlinarith only [he,hn]
  have htop : d.g (3/4)/d.H ≤ d.R+1/100 := by
    rw [div_le_iff₀ hH0]
    apply (mul_le_mul_iff_right₀ hD0).mp
    have he := hnum (3/4)
    have hpg := mul_le_mul_of_nonneg_right hH.2 hgap.1
    have hnu : 0 ≤ d.u/(3/4) := div_nonneg hu0 (by norm_num)
    have hsmall : d.H*(d.z-d.a0+d.a1*d.R)+d.u/d.k-d.u/(3/4) ≤ d.H*d.D/100 := by
      linarith [hgap.2]
    nlinarith only [he,hsmall]
  refine ⟨hR0,hH0,hH.2,by linarith [hk.1],by linarith [hk.2],
    ha.1,by linarith [ha.2],?_,?_,hF,hg9,hg10,?_,?_⟩
  · linarith [hgap.1]
  · linarith [hR.2,hz.1]
  · unfold Stg.w cutLo
    linarith [hR.1]
  · unfold Stg.w cutHi
    linarith [hR.2]

end
end Qrh.TwoSlot.AnchorContinuum
