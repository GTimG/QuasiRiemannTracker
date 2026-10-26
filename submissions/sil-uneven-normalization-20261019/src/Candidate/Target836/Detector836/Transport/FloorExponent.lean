/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
import Candidate.Target836.Detector836.Transport.GeometryFacts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
noncomputable section
namespace Target836.Transport
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
    floorSourceExponent v≤ signal theta-1/100 := by
  norm_num [floorSourceExponent, centralScale, signal, Target836.Assembly.signal,
    Target836.Assembly.signalShift, rowExtension, h, theta, lx, ly, ell,
    Target836.Arithmetic.x, Target836.Arithmetic.y, Target836.Arithmetic.ell,
    Target836.Arithmetic.h, Target836.Arithmetic.theta] at *
  linarith
lemma floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ} (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    floorRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+mesh*ell := by
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤12*e+eps*(N+8) by positivity)
  dsimp [floorRealLoss]
  nlinarith [Target836.Transport.ly_coarse, mul_nonneg he (by linarith [Target836.Transport.ly_coarse] : 0≤ly-1/3)]
end Target836.Transport

#print axioms Target836.Transport.physical_scale_identity
#print axioms Target836.Transport.floor_source_margin
#print axioms Target836.Transport.floor_loss_bound
