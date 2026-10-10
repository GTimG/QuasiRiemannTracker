import WeightedQRH.HighRows.WeightedSourceLoss
import WeightedQRH.NumeratorPhysicalFront

/-! Exact multiplicative bookkeeping for the literal source packet. Error
normalizers and main normalizers partition the same original physical slots. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
namespace WeightedQRH.Numerator

theorem error_main_source_power {K : ℕ} (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0 < Z) (lengths : Fin K→ℝ) :
    (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val))=
      Z^(-(4/25:ℝ)*(∑j,lengths j)) := by
  have hm : (∏j:{i:Fin K//i∉J},(Z^(lengths j.val))^(-(4/25:ℝ)))=
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) := by
    simp_rw [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)
  simpa only [hm] using error_main_source_scale J Z hZ lengths

/-- Collapse the complete scalar, frequency, count, and packet powers. The
unrestricted factor B accommodates the fixed polynomial height factor. -/
theorem source_packet_multiplicative_identity {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z d δ q ε eps t mesh C Ccount C0 B : ℝ)
    (hZ : 0 < Z) (hd : d≠0) (hδ : δ≠0) :
    ((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*t)*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (C*(Ccount*C0*Z^(3*t))*B*((Z^d)^(ly/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(t+q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*t/9)/2+
        (3*(rowCount δ (q/δ)+159*ε+9*t)+1+2*t)/4+
        δ*mesh/4+δ*t/4+t*(ell/d)))=
    (C*Ccount*C0*B)*Z^(numeratorExponent d δ (q/δ)+
      weightedSourceLoss d δ q ε eps t mesh t (2*t) t t) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E : ℝ := t+q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*t/9)/2+
    (3*(rowCount δ (q/δ)+159*ε+9*t)+1+2*t)/4+
    δ*mesh/4+δ*t/4+t*(ell/d)
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
      rw [←weighted_source_packet_exponent d δ q ε eps t mesh hd hδ]
      dsimp only [E]
      field_simp
      <;> ring

end WeightedQRH.Numerator
end
