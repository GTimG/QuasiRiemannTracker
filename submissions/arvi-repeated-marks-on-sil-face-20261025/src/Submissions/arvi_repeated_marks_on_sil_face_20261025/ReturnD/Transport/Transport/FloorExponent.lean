/- Repeated marks: fork of Collet's generic return module Transport.Transport.FloorExponent (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
namespace RepeatedMarksReturn.Transport.Transport
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
    floorSourceExponent v≤ signal theta-1/200 := by
  have hb := QRH.Record1252270103Return.Geometry.BoundsR.floor_margin
  dsimp [floorSourceExponent,centralScale]
  dsimp [QRH.Record1252270103Return.Geometry.dPlus] at hb
  have he : signal theta=QRH.Record1252270103Return.Geometry.signal theta := by
    dsimp [signal,Assembly.signal,QRH.Record1252270103Return.Geometry.signal,QRH.Record1252270103Return.Geometry.signalShift]
    rw [Assembly.signalShift_eq]
    change theta + -(4+(ly-lx))/6=theta + -(4+ly-lx)/6
    ring
  rw [he]
  dsimp [rowExtension] at hv
  linarith
lemma floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ} (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    floorRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+mesh*ell := by
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤12*e+eps*(N+8) by positivity)
  dsimp [floorRealLoss]
  nlinarith [RepeatedMarksReturn.Transport.Transport.ly_coarse, mul_nonneg he (by linarith [RepeatedMarksReturn.Transport.Transport.ly_coarse] : 0≤ly-1/3)]
end RepeatedMarksReturn.Transport.Transport

