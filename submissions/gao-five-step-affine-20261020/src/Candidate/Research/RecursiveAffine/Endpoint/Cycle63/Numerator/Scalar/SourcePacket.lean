/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Finite physical slot bookkeeping adapted from Cycle25/Numerator/Scalar;
weighted PR6 predecessor 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Numerator.Scalar.Loss
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.NumeratorSourceExponent

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Numerator_Scalar_SourcePacket : Cycle63.AffineLedger := Cycle153.Root.rootLedger


noncomputable section
open scoped Classical BigOperators
namespace Cycle153Endpoint.Numerator.Scalar
open Cycle153Endpoint.Arithmetic Cycle153Endpoint.Arithmetic.Bernstein

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
  have hsplit := WeightedQRH.Numerator.error_main_source_power J Z hZ lengths
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

end Cycle153Endpoint.Numerator.Scalar
