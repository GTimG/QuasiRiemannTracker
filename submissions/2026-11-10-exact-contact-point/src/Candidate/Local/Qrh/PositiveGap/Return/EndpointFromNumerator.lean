import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.FinalCommonProbe
import Candidate.Local.Qrh.PositiveGap.Return.TransportInstances
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return
open QRH.Record1252270103Return Qrh.JointDetector.BoundaryPhysical.Return
noncomputable section
variable [TargetC]
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace Final
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN := Geometry.finalBounds
abbrev LiteralNumeratorInput : Prop := GenericPhysical.FinalAssembly.ChosenFiniteNumeratorInput
theorem beta_of_literal_numerator (h : LiteralNumeratorInput) :
 HeckeZeroSupremum.beta≤QRH.PositiveGap.Return.theta :=
 GenericPhysical.FinalAssembly.beta_le_theta_of_finite_numerator h
end Final
end
end QRH.PositiveGap.Return
