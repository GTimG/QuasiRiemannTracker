/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Transport.GeometryFacts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.Constants

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Transport_FloorExponent : Cycle63.AffineLedger := Cycle153.Root.rootLedger

noncomputable section
namespace Cycle153Endpoint.Transport
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
  have hh := Cycle153Endpoint.Arithmetic.h_bounds
  have hz := Cycle153Endpoint.Arithmetic.dPlusOffset_bounds
  norm_num [floorSourceExponent, centralScale, signal, Cycle153Endpoint.Assembly.signal,
    Cycle153Endpoint.Assembly.signalShift, rowExtension, h, theta, lx, ly, ell, Cycle153Endpoint.Arithmetic.dPlusOffset,
    Cycle153Endpoint.Arithmetic.x, Cycle153Endpoint.Arithmetic.y, Cycle153Endpoint.Arithmetic.ell,
    Cycle153Endpoint.Arithmetic.h, Cycle153Endpoint.Arithmetic.theta] at *
  linarith
lemma floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ} (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    floorRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+mesh*ell := by
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤12*e+eps*(N+8) by positivity)
  dsimp [floorRealLoss]
  nlinarith [Cycle153Endpoint.Transport.ly_coarse, mul_nonneg he (by linarith [Cycle153Endpoint.Transport.ly_coarse] : 0≤ly-1/3)]
end Cycle153Endpoint.Transport
