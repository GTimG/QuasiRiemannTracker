/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.TransportGeometry
namespace QRH.LewkoStage2Return.Geometry
noncomputable def finalBounds : @Bounds finalParameters := by
  refine @Bounds.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.LewkoStage2Return.Geometry.theta,QRH.LewkoStage2Return.Geometry.h,QRH.LewkoStage2Return.Geometry.ell,QRH.LewkoStage2Return.Geometry.x,QRH.LewkoStage2Return.Geometry.y,QRH.LewkoStage2Return.Geometry.dPlus,QRH.LewkoStage2Return.Geometry.signal,QRH.LewkoStage2Return.Geometry.signalShift,finalParameters,
    LewkoStage2Finite.theta,LewkoStage2Finite.h,LewkoStage2Finite.ell,LewkoStage2Finite.x,LewkoStage2Finite.y,LewkoStage2Finite.c] <;> norm_num
noncomputable def intermediateBounds : @Bounds intermediateParameters := by
  refine @Bounds.mk intermediateParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.LewkoStage2Return.Geometry.theta,QRH.LewkoStage2Return.Geometry.h,QRH.LewkoStage2Return.Geometry.ell,QRH.LewkoStage2Return.Geometry.x,QRH.LewkoStage2Return.Geometry.y,QRH.LewkoStage2Return.Geometry.dPlus,QRH.LewkoStage2Return.Geometry.signal,QRH.LewkoStage2Return.Geometry.signalShift,intermediateParameters,
    LewkoStage2Finite.theta,LewkoStage2Finite.h,LewkoStage2Finite.ell,LewkoStage2Finite.x,LewkoStage2Finite.y,LewkoStage2Finite.c] <;> norm_num
end QRH.LewkoStage2Return.Geometry
#print axioms QRH.LewkoStage2Return.Geometry.finalBounds
#print axioms QRH.LewkoStage2Return.Geometry.intermediateBounds
