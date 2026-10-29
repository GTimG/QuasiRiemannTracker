/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FiveColourNorm

/-! Exact positive-real normalization of the physical residual-radical dyad.
The input puncture b, the bad-output norm Nb, and the rounding ratio rho
are separate parameters. No analytic bound is assumed. -/
namespace Qrh.JointDetector.NaturalPhysicalBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open FiveColourNorm

/-- Physical conductor normalization with its exact radical rounding ratio. -/
theorem physical_normalization (X b R rho U V G H E F J D : ℝ)
    (hX : 0 < X) (hb : 0 < b) (hR : 0 < R) (hrho : 0 < rho)
    (hU : 0 < U) (hV : 0 < V) (hG : 0 < G) (hH : 0 < H)
    (hE : 0 < E) (hF : 0 < F) (hJ : 0 < J)
    (hD : D = rho*U*V/(G*H*E*F*J)) :
    X/(b*R*Real.sqrt ((E*F*J)*D^2))*
      Real.sqrt ((V/(H*J*F))*(V/(H*J*E))) =
      (X*G/(U*R*Real.sqrt J))/(b*rho) := by
  have hDp : 0 < D := by rw [hD]; positivity
  have hA : 0 ≤ (E*F*J)*D^2 := by positivity
  have hB : 0 ≤ (V/(H*J*F))*(V/(H*J*E)) := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow,div_pow,Real.sq_sqrt hA,Real.sq_sqrt hB,Real.sq_sqrt hJ.le]
  rw [hD]
  field_simp

/-- The actual shell/dual scale identity retains the bad output and both
powers of the physical rounding ratio. -/
theorem physical_dual_scale (r b R rho U V G H E F J D X Nb : ℝ)
    (hX : 0 < X) (hNb : 0 < Nb) (hG : 0 < G) (hH : 0 < H)
    (hE : 0 < E) (hF : 0 < F) (hJ : 0 < J)
    (hD : D = rho*U*V/(G*H*E*F*J)) :
    r*b*R*(E*F*J)*D^2/(X*Nb) =
      (r*(b*rho^2/Nb))*sharedDualScale U V X G H J E F R := by
  rw [hD]
  unfold sharedDualScale
  field_simp

/-- Defining the physical radial shell parameter is exactly equivalent to
recovering the ordinary-source dyadic scale T. -/
theorem physical_frequency_relation (X Nb T b R E F J D r : ℝ)
    (hX : 0 < X) (hNb : 0 < Nb) (hb : 0 < b) (hR : 0 < R)
    (hE : 0 < E) (hF : 0 < F) (hJ : 0 < J) (hD : 0 < D)
    (hr : r = X*Nb*T/(b*R*(E*F*J)*D^2)) :
    T = r*b*R*(E*F*J)*D^2/(X*Nb) := by
  rw [hr]
  field_simp

/-- The literal source dyad equals the common dual scale times its exact
physical-shell multiplier. -/
theorem physical_frequency_shared_scale (r b R rho U V G H E F J D X Nb T : ℝ)
    (hX : 0 < X) (hNb : 0 < Nb) (hb : 0 < b) (hR : 0 < R)
    (hU : 0 < U) (hV : 0 < V) (hrho : 0 < rho)
    (hG : 0 < G) (hH : 0 < H) (hE : 0 < E) (hF : 0 < F) (hJ : 0 < J)
    (hD : D = rho*U*V/(G*H*E*F*J))
    (hr : r = X*Nb*T/(b*R*(E*F*J)*D^2)) :
    T = (r*(b*rho^2/Nb))*sharedDualScale U V X G H J E F R := by
  have hDp : 0 < D := by rw [hD]; positivity
  rw [physical_frequency_relation X Nb T b R E F J D r hX hNb hb hR hE hF hJ hDp hr]
  exact physical_dual_scale r b R rho U V G H E F J D X Nb hX hNb hG hH hE hF hJ hD

end
end Qrh.JointDetector.NaturalPhysicalBudget

#print axioms Qrh.JointDetector.NaturalPhysicalBudget.physical_normalization
#print axioms Qrh.JointDetector.NaturalPhysicalBudget.physical_dual_scale
#print axioms Qrh.JointDetector.NaturalPhysicalBudget.physical_frequency_relation
#print axioms Qrh.JointDetector.NaturalPhysicalBudget.physical_frequency_shared_scale
