/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native error gates follow from the exact advertised outer reserve. -/
import Candidate.C092.transport.MixedUpperFinalReserve
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MixedOffsetBank QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

theorem native_early_guards (D : BaselineData) (P : TransportParameters D)
    (affineError loss : ℝ) (haff : 0<affineError) (hloss : 0<loss)
    (hr : 159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss+2*rowPad ≤ 1/100000000000000) :
    D.ε ≤ 1/10000000 ∧ D.t ≤ 1/10000000 ∧ D.ε ≤ 3*witnessCollar := by
  have hpad : 0≤rowPad:=by unfold rowPad;positivity
  have hε:=D.epsilon_pos
  have ht:=D.t_pos
  have he:=D.e_pos
  have hm:=P.mesh_pos
  have hep:=P.eps_pos
  norm_num [witnessCollar]
  constructor
  · nlinarith only [hr,hε,ht,he,hm,hep,haff,hloss,hpad]
  constructor <;> nlinarith only [hr,hε,ht,he,hm,hep,haff,hloss,hpad]

#print axioms native_early_guards
end
end QRH.Cycle092.MixedUpperFinal
