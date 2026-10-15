/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Finite physical slot bookkeeping adapted from Cycle25/Numerator/Scalar;
weighted PR6 predecessor 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
import Candidate.Cycle62.Numerator.Scalar.Loss

noncomputable section
open scoped Classical BigOperators
namespace Cycle62.Numerator.Scalar
open Cycle62.Arithmetic Cycle62.Arithmetic.Bernstein

theorem error_main_source_scale {K : ℕ} (J : Finset (Fin K))
    (Y : Fin K→ℝ) (r : ℝ) :
    (∏j:J,(Y j.val)^r)*(∏j:{i:Fin K//i∉J},(Y j.val)^r)=∏j,(Y j)^r := by
  convert Fintype.prod_subtype_mul_prod_subtype (fun j=>j∈J) (fun j=>(Y j)^r) using 1
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl

theorem error_main_source_power {K : ℕ} (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0 < Z) (lengths : Fin K→ℝ) :
    (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) =
      Z^(-(4/25:ℝ)*(∑j,lengths j)) := by
  have hm : (∏j:{i:Fin K//i∉J},(Z^(lengths j.val))^(-(4/25:ℝ))) =
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) := by
    simp_rw [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)
  have hp := error_main_source_scale J (fun j=>Z^(lengths j)) (-(4/25:ℝ))
  rw [hm] at hp
  rw [hp]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul]
  congr 1
  ring

/-- Error and main slots partition the original source widths. The selected
capacity C is in Z units; neither the row endpoint nor kappa is specialized. -/
theorem source_packet_multiplicative_identity {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z kap d C delta q A : ℝ) (L : LossData)
    (hZ : 0 < Z) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    ((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (A*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(countingR kap delta (q/delta)+L.count)+1+L.moment)/4+
        L.selection/2+delta*L.mesh/4+L.slack*(ell/d))) =
    A*Z^(numeratorExponent kap d C delta (q/delta)+weightedSourceLoss d delta L) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E := L.mass+q*(ell/d)-q*(C/d)/2+
    (3*(countingR kap delta (q/delta)+L.count)+1+L.moment)/4+
    L.selection/2+delta*L.mesh/4+L.slack*(ell/d)
  calc
    _ = A*((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
        Z^(-(4/25:ℝ)*ell)*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*(Z^d)^E) := by
      rw [←hsplit]
      dsimp only [E]
      ring
    _ = A*Z^(d*L.scalar+d*(-(17/50:ℝ))+L.frequency+(-(4/25))*ell+
        L.front+(d*(y/d))*(-(1/2:ℝ))+d*E) := by
      simp_rw [←Real.rpow_mul hZ.le]
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
        ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by
      congr 2
      rw [←source_packet_exponent kap d C delta q L hd hdelta]
      dsimp only [E]
      field_simp
      ring

theorem source_kernel_multiplicative_identity (Z kap d C delta p e A : ℝ)
    (L : LossData) (hZ : 0 < Z) :
    A*Z^(numeratorExponent kap d C delta p+weightedSourceLoss d delta L)*
      (Z^x)^(1/2-17/50:ℝ)*Z^((1+delta)/2+16*e+17/50-1) =
    A*Z^(rowExponentAt kap d C delta p+Assembly.signalShift+16*e+weightedSourceLoss d delta L) := by
  rw [←Real.rpow_mul hZ.le,mul_assoc,←Real.rpow_add hZ,mul_assoc,←Real.rpow_add hZ]
  congr 2
  have hi := numerator_kernel_exponent kap d C delta p e
  unfold kernelExponent at hi
  linarith only [hi]

end Cycle62.Numerator.Scalar
