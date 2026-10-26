/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
import Candidate.Uneven.EndpointProbeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
noncomputable section
namespace UnevenEndpointPhysical.Transport
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
def centralScale (a e : ℝ) : ℝ := lx*(4/25)+(a+16*e-33/50)+ly*(-a-6*e)
lemma physical_scale_identity (Z a e : ℝ) (hZ : 0< Z) :
    (Z^lx)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^ly)^(-a-6*e)=Z^(centralScale a e) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ, ←Real.rpow_add hZ]
  rfl
def floorSourceExponent (v : ℝ) : ℝ := centralScale (51/100) 0+v*(67/100)-3*ell/20
def floorRealLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (16-6*ly)*e+v*(12*e+eps*(N+8))+loss+mesh*ell
lemma floor_source_margin {v : ℝ} (hv : v≤ h+rowExtension) :
    floorSourceExponent v≤ signal theta-1/100 := by
  rcases config with ⟨stage⟩
  cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,floorSourceExponent, centralScale, signal, UnevenEndpointPhysical.Assembly.signal,
    UnevenEndpointPhysical.Assembly.signalShift, rowExtension, h, theta, lx, ly, ell,
    UnevenEndpointPhysical.Arithmetic.x, UnevenEndpointPhysical.Arithmetic.y, UnevenEndpointPhysical.Arithmetic.ell,
    UnevenEndpointPhysical.Arithmetic.h, UnevenEndpointPhysical.Arithmetic.theta] at * <;> linarith
lemma floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ} (hv : v≤1) (he : 0≤ e) (heps : 0≤ eps) :
    floorRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+mesh*ell := by
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤12*e+eps*(N+8) by positivity)
  dsimp [floorRealLoss]
  nlinarith [UnevenEndpointPhysical.Transport.ly_coarse, mul_nonneg he (by linarith [UnevenEndpointPhysical.Transport.ly_coarse] : 0≤ ly-1/3)]
end UnevenEndpointPhysical.Transport

