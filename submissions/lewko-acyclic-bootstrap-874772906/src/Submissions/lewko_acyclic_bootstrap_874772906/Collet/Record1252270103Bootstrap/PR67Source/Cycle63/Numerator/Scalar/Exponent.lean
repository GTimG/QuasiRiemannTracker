import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Geometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Count.ArithmeticIdentity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Physical exponent bookkeeping adapted from Cycle25/Numerator/Scalar;
weighted PR6 predecessor 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
noncomputable section
namespace Cycle63.Numerator.Scalar
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein

/-- C is total selected capacity in Z units, not capacity relative to U=Z^d. -/
def numeratorExponent (kap d C delta p : ℝ) : ℝ :=
  -y/2+ell*(17/50-1/2)+ell*delta*p+
    d*((3*countingR kap delta p+1)/4-17/50)-delta*p*C/2

def kernelExponent (a e : ℝ) : ℝ :=
  x*(1/2-17/50)+a+16*e+17/50-1

/-- Literal physical weights, frequency damping and the two external Mellin
scales give the variable-kappa row expression at the supplied capacity. -/
theorem numerator_kernel_exponent (kap d C delta p e : ℝ) :
    numeratorExponent kap d C delta p+kernelExponent ((1+delta)/2) e =
      rowExponentAt kap d C delta p+Assembly.signalShift+16*e := by
  unfold numeratorExponent kernelExponent rowExponentAt Assembly.signalShift
  rw [x_eq,y_eq]
  ring

theorem numerator_packet_exponent (kap d C delta q scalar mass count moment selection mesh slack : ℝ)
    (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    -y/2-(4/25)*ell+slack*ell+
      d*(scalar+mass+q*(ell/d)-q*(C/d)/2+
        (3*(countingR kap delta (q/delta)+count)+1+moment)/4+
        selection/2+delta*mesh/4-17/50) =
      numeratorExponent kap d C delta (q/delta)+slack*ell+
        d*(scalar+mass+(3*count+moment)/4+selection/2+delta*mesh/4) := by
  unfold numeratorExponent
  have hq : delta*(q/delta)=q := by field_simp
  rw [hq]
  field_simp
  ring

end Cycle63.Numerator.Scalar

end
end Record1252270103Bootstrap.PR67
