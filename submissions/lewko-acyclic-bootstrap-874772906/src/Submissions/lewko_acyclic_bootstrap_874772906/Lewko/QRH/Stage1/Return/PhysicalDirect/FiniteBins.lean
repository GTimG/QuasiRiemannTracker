/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Adapted from Gao Target830 physical closure, inherited OpenAI/Hailey Collet/Akash Levy; Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.PhysicalDirect.BinBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped BigOperators Classical
namespace QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Packet
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.LewkoStage1Return.GenericArithmetic
open QRH.LewkoStage1Return.GenericArithmetic QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect
open Cycle25.Numerator

theorem finite_weighted_dilation_bins {ι : Type*} (s : Finset ι) (n : ℕ)
    (S Q : ℕ → ι → ℂ) (P f : ι → ℂ)
    (d U R q L xi ann delta loss epsilon Ccount Cmoment M : ℝ)
    (hd : dm ≤ d ∧ d ≤ dp)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (s.card : ℝ) ≤ Ccount*U^R)
    (hsplit : ∀ i ∈ s, f i = ∑ j ∈ Finset.range (n+1),
      ((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i ∈ s,
      U^(q*scheduledCapacity d (2*((j : ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : ∀ j ∈ Finset.range (n+1),
      (∑ i ∈ s, ‖S j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i ∈ s, ‖f i * P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*zeroCapacity d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hdelta : 0 ≤ delta := by linarith
  let E : ℝ := q*L-q*zeroCapacity d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2
  have hj (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i ∈ s, ‖(((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i) * P i‖) ≤
      M*Ccount*Cmoment*U^E := by
    have hb := weighted_dilation_bin s (S j) (Q j) P d U R q L ((j : ℝ)*xi) xi ann delta
      loss epsilon Ccount Cmoment hd hU hc hm hq hqdelta (mul_nonneg (Nat.cast_nonneg _) hxi)
      hxi hann hcard (hselected j hj) hfull (henergy j hj)
    have hpow : U^(E-2*dampingRate*delta*((j : ℝ)*xi+xi+ann)) ≤ U^E :=
      Real.rpow_le_rpow_of_exponent_le hU (by
        have hv : 0 ≤ (j : ℝ)*xi+xi+ann := by positivity
        have := mul_nonneg (mul_nonneg (by norm_num [dampingRate] : (0:ℝ)≤dampingRate) hdelta) hv
        dsimp only [E]
        nlinarith)
    calc
      _ = M * (U^(-delta*((j : ℝ)*xi)/2) * (∑ i ∈ s, ‖S j i * P i‖)) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_assoc,norm_mul,Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg hM (Real.rpow_nonneg hU0.le _))]
        ring
      _ ≤ M * (Ccount*Cmoment*U^(E-2*dampingRate*delta*((j : ℝ)*xi+xi+ann))) :=
        mul_le_mul_of_nonneg_left hb hM
      _ ≤ M * (Ccount*Cmoment*U^E) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (by have hc0 := zero_le_one.trans hc; have hm0 := zero_le_one.trans hm; positivity)) hM
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ Finset.range (n+1),
        ‖(((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i) * P i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hsplit i hi,Finset.sum_mul]
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n+1), ∑ i ∈ s,
        ‖(((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i) * P i‖ := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (n+1), M*Ccount*Cmoment*U^E := Finset.sum_le_sum hj
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; dsimp only [E]; ring

end QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Packet


/- Adapted from Cycle25/Numerator/FiniteBins.lean; original predecessor:
akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

#print axioms QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Packet.finite_weighted_dilation_bins
