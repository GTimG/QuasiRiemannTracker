/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.TransportGeometry
namespace QRH.Record1252270103Return.Geometry
noncomputable def finalBounds : @Bounds finalParameters := by
  refine @Bounds.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,QRH.Record1252270103Return.Geometry.dPlus,QRH.Record1252270103Return.Geometry.signal,QRH.Record1252270103Return.Geometry.signalShift,finalParameters,
    Record1252270103Finite.theta,Record1252270103Finite.h,Record1252270103Finite.ell,Record1252270103Finite.x,Record1252270103Finite.y,Record1252270103Finite.c] <;> norm_num
noncomputable def intermediateBounds : @Bounds intermediateParameters := by
  refine @Bounds.mk intermediateParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,QRH.Record1252270103Return.Geometry.dPlus,QRH.Record1252270103Return.Geometry.signal,QRH.Record1252270103Return.Geometry.signalShift,intermediateParameters,
    Record1252270103Finite.theta,Record1252270103Finite.h,Record1252270103Finite.ell,Record1252270103Finite.x,Record1252270103Finite.y,Record1252270103Finite.c] <;> norm_num
end QRH.Record1252270103Return.Geometry
#print axioms QRH.Record1252270103Return.Geometry.finalBounds
#print axioms QRH.Record1252270103Return.Geometry.intermediateBounds
