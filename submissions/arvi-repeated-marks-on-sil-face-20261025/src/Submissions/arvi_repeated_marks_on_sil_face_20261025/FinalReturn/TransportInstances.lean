/- Repeated marks: fork of Collet's final-stage module TransportInstances (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.TransportGeometry
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Geometry
namespace QRH.RepeatedMarks.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalBounds : @BoundsR finalParameters := by
  refine @BoundsR.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,QRH.Record1252270103Return.Geometry.dPlus,QRH.Record1252270103Return.Geometry.signal,QRH.Record1252270103Return.Geometry.signalShift,finalParameters,
    QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.h,QRH.RepeatedMarks.Return.ell,QRH.RepeatedMarks.Return.x,QRH.RepeatedMarks.Return.y,QRH.RepeatedMarks.Return.c] <;> norm_num
end QRH.RepeatedMarks.Return.Geometry
#print axioms QRH.RepeatedMarks.Return.Geometry.finalBounds
