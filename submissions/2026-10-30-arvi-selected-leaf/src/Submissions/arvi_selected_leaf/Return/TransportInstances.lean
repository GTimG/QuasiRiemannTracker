/- Repeated marks: fork of Collet's final-stage module TransportInstances (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the widened box `BoundsN` (not PR76 `BoundsR`, which fails here) at the new parameters -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Submissions.arvi_density.ReturnD.TransportGeometry
import Submissions.arvi_selected_leaf.Return.Geometry
set_option autoImplicit false
namespace QRH.ArviDensity.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalBounds : @BoundsN finalParameters := by
  refine @BoundsN.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,QRH.Record1252270103Return.Geometry.dPlus,QRH.Record1252270103Return.Geometry.signal,QRH.Record1252270103Return.Geometry.signalShift,finalParameters,
    QRH.ArviDensity.Return.theta,QRH.ArviDensity.Return.h,QRH.ArviDensity.Return.ell,QRH.ArviDensity.Return.x,QRH.ArviDensity.Return.y,QRH.ArviDensity.Return.c] <;> norm_num
end QRH.ArviDensity.Return.Geometry
