/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalLow/LowInverseNormalize.lean
Original SHA-256: 0cb6ef1589c2ce17e6fdb6149590714fd34862afe0f4db78462686a7a4f20bce
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry

/-!
Transport of OpenAI Detector/LowInverseNormalize.lean, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; license: upstream-config/LICENSE.
The row normalization identity holds for an arbitrary real row-width exponent.
-/

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma transport_low_inverse_power_cancel (rowWidth Z d α : ℝ) (hZ : 0<Z) :
    Z^(rowWidth-2*d+α)*(Z^d)^2/Z^(rowWidth:ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma transport_low_inverse_sqrt_normalized (rowWidth q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0<q) (hC : 0≤C) (_hB : 0≤B) (hZ : 0<Z) (hL : 0<L) (hH : 1≤H)
    (hE : 0≤E) (hEL : E≤C*H^n*Z^(rowWidth-2*d+α)) (hLB : L≤B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^(rowWidth:ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^(rowWidth:ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^(rowWidth-2*d+α))/(q*Z^(rowWidth:ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^(rowWidth-2*d+α))*L^2/(q*Z^(rowWidth:ℝ)) := by field_simp
      _≤(C*H^n*Z^(rowWidth-2*d+α))*(B*Z^d)^2/(q*Z^(rowWidth:ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^(rowWidth-2*d+α)*(Z^d)^2/Z^(rowWidth:ℝ)) := by ring
      _=_ := by rw [transport_low_inverse_power_cancel rowWidth Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI
