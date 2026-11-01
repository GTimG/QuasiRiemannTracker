/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module TransportInstances (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the widened box `BoundsN` (not PR76 `BoundsR`, which fails here) at the new parameters -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.TransportGeometry
import Candidate.Local.Qrh.PositiveGap.Return.Geometry
set_option autoImplicit false
namespace QRH.PositiveGap.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalBounds : @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN finalParameters := by
  refine @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,QRH.Record1252270103Return.Geometry.dPlus,Qrh.JointDetector.BoundaryPhysical.Return.Geometry.dPlus,QRH.Record1252270103Return.Geometry.signal,QRH.Record1252270103Return.Geometry.signalShift,finalParameters,
    QRH.PositiveGap.Return.theta,QRH.PositiveGap.Return.h,QRH.PositiveGap.Return.ell,QRH.PositiveGap.Return.x,QRH.PositiveGap.Return.y,QRH.PositiveGap.Return.c] <;> norm_num
end QRH.PositiveGap.Return.Geometry
