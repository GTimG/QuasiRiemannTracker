/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.TransportGeometry
namespace QRH.LewkoStage1Return.Geometry
noncomputable def finalBounds : @Bounds finalParameters := by
  refine @Bounds.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.LewkoStage1Return.Geometry.theta,QRH.LewkoStage1Return.Geometry.h,QRH.LewkoStage1Return.Geometry.ell,QRH.LewkoStage1Return.Geometry.x,QRH.LewkoStage1Return.Geometry.y,QRH.LewkoStage1Return.Geometry.dPlus,QRH.LewkoStage1Return.Geometry.signal,QRH.LewkoStage1Return.Geometry.signalShift,finalParameters,
    LewkoStage1Finite.theta,LewkoStage1Finite.h,LewkoStage1Finite.ell,LewkoStage1Finite.x,LewkoStage1Finite.y,LewkoStage1Finite.c] <;> norm_num
noncomputable def intermediateBounds : @Bounds intermediateParameters := by
  refine @Bounds.mk intermediateParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.LewkoStage1Return.Geometry.theta,QRH.LewkoStage1Return.Geometry.h,QRH.LewkoStage1Return.Geometry.ell,QRH.LewkoStage1Return.Geometry.x,QRH.LewkoStage1Return.Geometry.y,QRH.LewkoStage1Return.Geometry.dPlus,QRH.LewkoStage1Return.Geometry.signal,QRH.LewkoStage1Return.Geometry.signalShift,intermediateParameters,
    LewkoStage1Finite.theta,LewkoStage1Finite.h,LewkoStage1Finite.ell,LewkoStage1Finite.x,LewkoStage1Finite.y,LewkoStage1Finite.c] <;> norm_num
end QRH.LewkoStage1Return.Geometry
#print axioms QRH.LewkoStage1Return.Geometry.finalBounds
#print axioms QRH.LewkoStage1Return.Geometry.intermediateBounds
