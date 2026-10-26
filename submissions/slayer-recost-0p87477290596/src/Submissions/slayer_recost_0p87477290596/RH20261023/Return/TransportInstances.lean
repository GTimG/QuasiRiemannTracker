/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.TransportGeometry
namespace QRH.RH20261023Return.Geometry
noncomputable def finalBounds : @Bounds finalParameters := by
  refine @Bounds.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.RH20261023Return.Geometry.theta,QRH.RH20261023Return.Geometry.h,QRH.RH20261023Return.Geometry.ell,QRH.RH20261023Return.Geometry.x,QRH.RH20261023Return.Geometry.y,QRH.RH20261023Return.Geometry.dPlus,QRH.RH20261023Return.Geometry.signal,QRH.RH20261023Return.Geometry.signalShift,finalParameters,
    RH20261023Finite.theta,RH20261023Finite.h,RH20261023Finite.ell,RH20261023Finite.x,RH20261023Finite.y,RH20261023Finite.c] <;> norm_num
noncomputable def intermediateBounds : @Bounds intermediateParameters := by
  refine @Bounds.mk intermediateParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [QRH.RH20261023Return.Geometry.theta,QRH.RH20261023Return.Geometry.h,QRH.RH20261023Return.Geometry.ell,QRH.RH20261023Return.Geometry.x,QRH.RH20261023Return.Geometry.y,QRH.RH20261023Return.Geometry.dPlus,QRH.RH20261023Return.Geometry.signal,QRH.RH20261023Return.Geometry.signalShift,intermediateParameters,
    RH20261023Finite.theta,RH20261023Finite.h,RH20261023Finite.ell,RH20261023Finite.x,RH20261023Finite.y,RH20261023Finite.c] <;> norm_num
end QRH.RH20261023Return.Geometry
#print axioms QRH.RH20261023Return.Geometry.finalBounds
#print axioms QRH.RH20261023Return.Geometry.intermediateBounds
