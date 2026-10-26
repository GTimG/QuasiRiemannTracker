/- Repeated marks: fork of Record1252270103StepScalar.Geometry (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103StepScalar.Geometry
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103StepScalar
noncomputable section
open Record1252270103Finite QRH.Record1252270103Graph

theorem nf_real_geometry_rm (n low : Source) (high : Option Source)
    (hv : QRH.RepeatedMarks.Finite.SourceValidC n low high) (hlow : ParentGood low) {b : ℝ}
    (hb : b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    RealGeometry (9/2) n low b := by
  have hν : (n.q:ℝ)∈Set.Icc (n.q:ℝ) (3/4) := ⟨le_rfl,by
    have h : (n.q:ℝ)≤((3/4:ℚ):ℝ) := Rat.cast_le.mpr hv.2.2.2.2.2.2.1
    norm_num at h ⊢
    exact h⟩
  obtain ⟨hg,hw,_⟩:=QRH.RepeatedMarks.Finite.sourceC_full_width_gates n low high hv hb hν
  exact real_geometry_of_gates _ _ _ _ hlow hg hw

end
end QRH.Record1252270103StepScalar
