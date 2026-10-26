/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Homogeneous

set_option autoImplicit false
namespace Record12518109Gain
noncomputable section

/-- R35 and R37 use this same cost identity with their distinct common credits. -/
theorem fixed_cost_payment (ν ρ γ Q L F R H b fee : ℝ)
    (hν : ν≤1) (hρ : 1/6≤ρ) (hγ : 0≤γ)
    (hQ : 0≤Q) (hR : 0≤R) (hwidth : F≤2*R+Q) (hL : L≤b)
    (hcommon : fee≤H+γ*F/2-(1-ν)*b)
    (hradius : fee≤H+(ρ-1/6)*F-(1-ν)*b) :
    Q/6+L+fee≤H+ρ*Q+ν*L+γ*R := by
  have hslots : (1-ν)*L≤(1-ν)*b:=mul_le_mul_of_nonneg_left hL (by linarith)
  by_cases h : γ≤2*(ρ-1/6)
  · have hr:=mul_le_mul_of_nonneg_left hwidth hγ
    have hq:=mul_le_mul_of_nonneg_right h hQ
    nlinarith
  · have hr:=mul_le_mul_of_nonneg_right (le_of_not_ge h) hR
    have hw:=mul_le_mul_of_nonneg_left hwidth (show 0≤ρ-1/6 by linarith)
    nlinarith

/-- Both affine first-common branches must be supplied; paired RAW Γ is separate. -/
theorem first_fixed_cost_payment (ν ρ Q L F R H b fee : ℝ)
    (hν : ν≤1) (hρ : 1/6≤ρ)
    (hγ : 0≤min (ν-3/19) (ν-4*ρ+5/4))
    (hQ : 0≤Q) (hR : 0≤R) (hwidth : F≤2*R+Q) (hL : L≤b)
    (hfirst : fee≤H+(ν-3/19)*F/2-(1-ν)*b)
    (hsecond : fee≤H+(ν-4*ρ+5/4)*F/2-(1-ν)*b)
    (hradius : fee≤H+(ρ-1/6)*F-(1-ν)*b) :
    Q/6+L+fee≤H+ρ*Q+ν*L+min (ν-3/19) (ν-4*ρ+5/4)*R := by
  apply fixed_cost_payment ν ρ _ Q L F R H b fee hν hρ hγ hQ hR hwidth hL _ hradius
  rcases le_total (ν-3/19) (ν-4*ρ+5/4) with h|h
  · simpa only [min_eq_left h] using hfirst
  · simpa only [min_eq_right h] using hsecond

/-- R36/R37: Q0 remains a positive external cutoff, independent of raw/core mesh. -/
theorem tiny_cost_payment (ν ρ γ Q Q₀ L F R H b fee : ℝ)
    (hν : ν≤1) (hρ : ρ≤1) (hγ : 0≤γ)
    (hQ : Q≤Q₀) (hwidth : F≤2*R+Q) (hL : L≤b)
    (hreserve : fee≤H+γ*(F-Q₀)/2-(1-ρ)*Q₀-(1-ν)*b) :
    Q+L+fee≤H+ρ*Q+ν*L+γ*R := by
  have hslots:=mul_le_mul_of_nonneg_left hL (show 0≤1-ν by linarith)
  have hrad:=mul_le_mul_of_nonneg_left hQ (show 0≤1-ρ by linarith)
  have hcommon:=mul_le_mul_of_nonneg_left (show F-Q₀≤2*R by linarith) hγ
  nlinarith

end
end Record12518109Gain
