/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.Rescale
import Submissions.hailey_collet_1252270103.Record12518109Gain.RootCompletion
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open OAI OAI.SevenEighths LocalMoment HeckeFamily HeckeInverseAmplification
open ConcretePrimeRowBridge ProbeHighRowFamily ProbePhysical

theorem ordinary_large_root_power {E A C Z F n nu S bin eta loss : ℝ}
    (hZ : 1<Z) (hn : 1≤n) (heta : 0≤eta) (hA : 0≤A) (hC : A≤C)
    (hloss : eta*F+2*bin*S≤loss)
    (hb : E≤A*Z^(nu*S+2*bin*S)*(Z^F/n^6)^(rho nu+eta)) :
    E≤(C*Z^loss)*Z^(rho nu*F+nu*S)*n^(-6*rho nu) := by
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hnp : 0<n := zero_lt_one.trans_le hn
  rw [sixth_window_power (Z^F) n (rho nu+eta)
    (Real.rpow_pos_of_pos hZp _) hnp,←Real.rpow_mul hZp.le] at hb
  have htail : n^(-6*(rho nu+eta))≤n^(-6*rho nu) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hexp := Real.rpow_le_rpow_of_exponent_le hZ.le hloss
  calc
    E≤A*Z^(nu*S+2*bin*S)*Z^(F*(rho nu+eta))*n^(-6*(rho nu+eta)) := by
      simpa only [mul_assoc] using hb
    _≤A*Z^(nu*S+2*bin*S)*Z^(F*(rho nu+eta))*n^(-6*rho nu) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _=(A*Z^(eta*F+2*bin*S))*Z^(rho nu*F+nu*S)*n^(-6*rho nu) := by
      have he : (nu*S+2*bin*S)+F*(rho nu+eta)=(eta*F+2*bin*S)+(rho nu*F+nu*S) := by ring
      rw [mul_assoc A,←Real.rpow_add hZp,he,Real.rpow_add hZp]
      ring
    _≤_ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hC hexp (by positivity) (hA.trans hC)

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.ordinary_large_root_power
