/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/FloorExponent.lean
Original SHA-256: 58b42d63d2d242af02e070eac1d5765b0c23a9cd33b48ff2c4bf79e2ce85a2e2
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.TunedExponent

namespace LW56e2.Transport.PhysicalHigh
noncomputable section

/-- The actual floor-bin estimate has a fixed positive margin at tuned geometry. -/
theorem tuned_floor_saving (N : ℕ) (v e eps loss mesh nu saving : ℝ)
    (hv : v≤TunedCandidate.h+TunedCandidate.zeta) (he : 0≤e) (heps : 0≤eps)
    (hbudget : 26*e+eps*(N+8)+loss+mesh*TunedCandidate.ell+nu+saving≤1/200) :
    profileExponent (51/100) e+v*(67/100+12*e+eps*(N+8))+loss-
      (3/20)*TunedCandidate.ell+mesh*TunedCandidate.ell+nu≤
      TunedCandidate.signal TunedCandidate.B-saving := by
  have htop : profileExponent (51/100) 0+
      (TunedCandidate.h+TunedCandidate.zeta)*(67/100)-(3/20)*TunedCandidate.ell≤
      TunedCandidate.signal TunedCandidate.B-1/200 := by
    norm_num [profileExponent,TunedCandidate.signal,TunedCandidate.signalAt,
      TunedCandidate.B,TunedCandidate.boundaryAt,TunedCandidate.lx,TunedCandidate.lxAt,
      TunedCandidate.ly,TunedCandidate.lyAt,TunedCandidate.h,TunedCandidate.hAt,
      TunedCandidate.ell,Geometry.ell,TunedCandidate.p,TunedCandidate.b,TunedCandidate.zeta]
  have hv1 : v≤1 := hv.trans TunedCandidate.buffered_upper_scale_lt_one.le
  have hbase := mul_le_mul_of_nonneg_right hv (show (0:ℝ)≤67/100 by norm_num)
  have hly : (1/3:ℝ)≤TunedCandidate.ly := by
    rw [TunedCandidate.geometry_values.2.2.1]
    norm_num
  have hprof : profileExponent (51/100) e=
      profileExponent (51/100) 0+(16-6*TunedCandidate.ly)*e := by
    unfold profileExponent
    ring
  have hp := mul_le_mul_of_nonneg_right (show 16-6*TunedCandidate.ly≤(14:ℝ) by linarith) he
  have hve := mul_le_mul_of_nonneg_right hv1 he
  have hveps := mul_le_mul_of_nonneg_right hv1 (show 0≤eps*(N+8) by positivity)
  rw [hprof]
  nlinarith only [htop,hbase,hp,hve,hveps,hbudget]

end
end LW56e2.Transport.PhysicalHigh
