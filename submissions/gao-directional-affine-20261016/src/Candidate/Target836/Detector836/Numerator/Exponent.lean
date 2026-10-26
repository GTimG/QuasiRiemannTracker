/- Private .874836 scalar specialization. Adapted from accepted Hailey Collet,
OpenAI, weighted PR6 and Cycle63 sources; Apache-2.0. -/
import Candidate.Target836.Detector836.Numerator.Geometry
noncomputable section
namespace Target836.Numerator.Scalar
open Target836.Arithmetic Target836.EndpointArithmetic

/-- C is total selected capacity in Z units, not capacity relative to U=Z^d. -/
def numeratorExponent (kap d C delta p : ℝ) : ℝ :=
  -y/2+ell*(17/50-1/2)+ell*delta*p+
    d*((3*Detector836.count kap delta p+1)/4-17/50)-delta*p*C/2

def kernelExponent (a e : ℝ) : ℝ :=
  x*(1/2-17/50)+a+16*e+17/50-1

/-- Literal physical weights, frequency damping and the two external Mellin
scales give the variable-kappa row expression at the supplied capacity. -/
theorem numerator_kernel_exponent (kap d C delta p e : ℝ) :
    numeratorExponent kap d C delta p+kernelExponent ((1+delta)/2) e =
      rowAt kap d C delta p+Assembly.signalShift+16*e := by
  unfold numeratorExponent kernelExponent rowAt rowBase Assembly.signalShift
  rw [x_eq,y_eq]
  ring

theorem numerator_packet_exponent (kap d C delta q scalar mass count moment selection mesh slack : ℝ)
    (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    -y/2-(4/25)*ell+slack*ell+
      d*(scalar+mass+q*(ell/d)-q*(C/d)/2+
        (3*(Detector836.count kap delta (q/delta)+count)+1+moment)/4+
        selection/2+delta*mesh/4-17/50) =
      numeratorExponent kap d C delta (q/delta)+slack*ell+
        d*(scalar+mass+(3*count+moment)/4+selection/2+delta*mesh/4) := by
  unfold numeratorExponent
  have hq : delta*(q/delta)=q := by field_simp
  rw [hq]
  field_simp
  ring

end Target836.Numerator.Scalar


#print axioms Target836.Numerator.Scalar.numerator_kernel_exponent
#print axioms Target836.Numerator.Scalar.numerator_packet_exponent
