import Cycle25.Assembly.Transport.GeometryFacts
import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
noncomputable section
namespace Cycle25.Transport
def centralScale (a e : ℝ) : ℝ := lx*(4/25)+(a+16*e-33/50)+ly*(-a-6*e)
lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^lx)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^ly)^(-a-6*e)=Z^(centralScale a e) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ, ←Real.rpow_add hZ]
  rfl
def floorSourceExponent (v : ℝ) : ℝ := centralScale (51/100) 0+v*(67/100)-3*ell/20
def floorRealLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (16-6*ly)*e+v*(12*e+eps*(N+8))+loss+mesh*ell
lemma floor_source_margin {v : ℝ} (hv : v≤h+rowExtension) :
    floorSourceExponent v≤signal theta-1/100 := by
  dsimp [floorSourceExponent, centralScale, signal, Cycle25.b, rowExtension] at *
  rw [Cycle25.theta_eq]
  nlinarith [Cycle25.length_sum, Cycle25.h_interval, Cycle25.ell_interval, Cycle25.ly_coarse]
lemma floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ} (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    floorRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+mesh*ell := by
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤12*e+eps*(N+8) by positivity)
  dsimp [floorRealLoss]
  nlinarith [Cycle25.ly_coarse, mul_nonneg he (by linarith [Cycle25.ly_coarse] : 0≤ly-1/3)]
end Cycle25.Transport
