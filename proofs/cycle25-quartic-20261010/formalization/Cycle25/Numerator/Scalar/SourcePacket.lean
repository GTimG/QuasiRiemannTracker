/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
import Cycle25.Numerator.Scalar.SourceLoss
import Cycle25.Numerator.PhysicalFront

noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Numerator.Scalar

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
  simpa only [hm] using Cycle25.Numerator.error_main_source_scale J Z hZ lengths

/-- Collapse the physical front, frequency, count and packet powers using
the same moment parameter as the detector count. -/
theorem source_packet_multiplicative_identity {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z kap d delta q epsilon eps t mesh C Ccount C0 B : ℝ)
    (hZ : 0 < Z) (hk : kap ≠ 0) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    ((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*t)*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (C*(Ccount*C0*Z^(3*t))*B*((Z^d)^(ly/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(t+q*(ell/d)-q*((2*(ly/d)-1)/(6*kap)-t/(3*kap))/2+
        (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
          159*epsilon+9*t)+1+2*t)/4+
        delta*mesh/4+delta*t/4+t*(ell/d))) =
    (C*Ccount*C0*B)*Z^(numeratorExponent kap d delta (q/delta)+
      weightedSourceLoss kap d delta q epsilon eps t mesh t (2*t) t t) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E : ℝ := t+q*(ell/d)-q*((2*(ly/d)-1)/(6*kap)-t/(3*kap))/2+
    (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
      159*epsilon+9*t)+1+2*t)/4+delta*mesh/4+delta*t/4+t*(ell/d)
  calc
    _ = (C*Ccount*C0*B)*
        ((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*t)*
          Z^(-(4/25:ℝ)*ell)*Z^(3*t)*((Z^d)^(ly/d))^(-(1/2:ℝ))*(Z^d)^E) := by
      rw [←hsplit]
      dsimp only [E]
      ring
    _ = (C*Ccount*C0*B)*Z^(d*(2*eps)+d*(-(17/50:ℝ))+(17/25)*t+
        -(4/25:ℝ)*ell+3*t+(d*(ly/d))*(-(1/2:ℝ))+d*E) := by
      simp_rw [←Real.rpow_mul hZ.le]
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
        ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by
      congr 2
      rw [←weighted_source_packet_exponent kap d delta q epsilon eps t mesh t (2*t) t t hk hd hdelta]
      dsimp only [E]
      field_simp
      ring

end Cycle25.Numerator.Scalar
