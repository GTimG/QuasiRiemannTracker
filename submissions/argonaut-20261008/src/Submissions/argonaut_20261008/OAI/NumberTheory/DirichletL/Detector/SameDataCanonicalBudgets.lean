import Submissions.argonaut_20261008.ParametersHighDataPerturbed
import Submissions.argonaut_20261008.PerturbedCentralExponent

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.PerturbedCanonicalLocalPrep
open SevenEighths.Parameters SevenEighths.PerturbedCentral

/-- The small dyadic sum's fixed rho surcharge is paid by the same datum. -/
theorem same_D_small_rho_reserve {Delta : ℝ} (D : HighDataPerturbed Delta) :
    D.sigma + 8 * D.e + D.t / 8 + 51 * rho0 / 100 ≤ 63 / 800 := by
  have ht := D.t_pos
  have he := D.e_pos
  have heps := D.eps_pos
  have hepsilon := D.epsilon_pos
  have hcount : 0 ≤ 159 * D.ε + D.t + D.t + 7 * D.t := by positivity
  have hphys := mul_nonneg height_nonneg hcount
  have hEt := mul_nonneg totalE_pos.le ht.le
  have hNeps : 0 ≤ (D.N + 8 : ℝ) * D.eps := by positivity
  have hnew :
      physicalHeight * (159 * D.ε + D.t + D.t + 7 * D.t) + 2 * D.t +
        (3 / 2) * (2 * D.t) +
        (26 * D.e + (D.N + 8) * D.eps + D.t + totalE * D.t) +
        (D.t + D.t + D.t) + D.t < perturbedBv6 / 2 := by
    simpa only [physicalHeight, totalE, rho0, perturbedHeight,
      perturbedTotalE, perturbedRho] using D.new_central_budget
  have hsmall : 8 * D.e + 2 * D.t < perturbedBv6 / 2 := by
    nlinarith
  have hsave := D.high_saving
  have hnum : perturbedBv6 / 2 + 51 * rho0 / 100 < (63 / 800 : ℝ) := by
    norm_num [perturbedBv6, rho0]
  linarith

theorem same_D_small_exponent {Delta : ℝ} (D : HighDataPerturbed Delta) (beta : ℝ) :
    beta - 11 / 16 - 63 / 800 + 8 * D.e + 51 * rho0 / 100 ≤
      beta - 11 / 16 - D.sigma - D.t / 8 := by
  linarith [same_D_small_rho_reserve D]

theorem same_D_small_power {Delta : ℝ} (D : HighDataPerturbed Delta)
    (beta Z : ℝ) (hZ : 1 ≤ Z) :
    Z ^ (beta - 11 / 16 - 63 / 800 + 8 * D.e + 51 * rho0 / 100) ≤
      Z ^ (beta - 11 / 16 - D.sigma - D.t / 8) :=
  Real.rpow_le_rpow_of_exponent_le hZ (same_D_small_exponent D beta)

/-- The actual source is moved together with the row cap; the large-line slope stays negative. -/
theorem same_D_large_line_slope {Delta : ℝ} (D : HighDataPerturbed Delta) :
    (13 / 16 : ℝ) + 3 * rho0 / 2 - (physicalHeight + D.t) = -D.t := by
  unfold physicalHeight
  ring

/-- Choose a genuine large-tail line before eta, paying the exact shifted-scale cost. -/
theorem exists_large_line_same_D {Delta : ℝ} (D : HighDataPerturbed Delta)
    (delta saving : ℝ) :
    ∃r : ℝ, (17 / 50 : ℝ) ≤ r ∧ 8 / 5 + delta < r ∧
      (53 / 32 : ℝ) + (13 / 16 : ℝ) * r + rho0 * (3 * r / 2 - 3 / 4) +
        (physicalHeight + D.t) * (8 / 5 + delta - r) ≤ -saving := by
  let A : ℝ := (53 / 32 : ℝ) + ((13 / 16 : ℝ) + D.t) * (8 / 5 + delta) +
    rho0 * (33 / 20 + 3 * delta / 2)
  obtain ⟨r, hr⟩ := exists_gt
    (max (17 / 50 : ℝ) (max (8 / 5 + delta) ((A + saving) / D.t)))
  have h1 := (le_max_left (17 / 50 : ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8 / 5 + delta) _)
    (le_max_right (17 / 50 : ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8 / 5 + delta) _)
    (le_max_right (17 / 50 : ℝ) _)).trans_lt hr
  have hdiv := (div_lt_iff₀ D.t_pos).mp h3
  refine ⟨r, h1.le, h2, ?_⟩
  have hid :
      (53 / 32 : ℝ) + (13 / 16 : ℝ) * r + rho0 * (3 * r / 2 - 3 / 4) +
        (physicalHeight + D.t) * (8 / 5 + delta - r) = A - D.t * r := by
    dsimp [A]
    unfold physicalHeight
    ring
  rw [hid]
  nlinarith

theorem same_D_height_cap {Delta : ℝ} (D : HighDataPerturbed Delta) :
    physicalHeight + D.t + 2 * D.t ≤ 7 / 8 := by
  simpa only [physicalHeight, rho0, perturbedHeight, perturbedRho]
    using D.physical_conductor_cap

/-- Saving D.t pays the t/8 normalizer cost in large-tail and finite-cube errors. -/
theorem same_D_tail_saving_exponent {Delta : ℝ} (D : HighDataPerturbed Delta)
    {beta : ℝ} (hbeta : boundary < beta) :
    -D.t + D.t / 8 ≤ beta - 11 / 16 - D.sigma := by
  have hboundary : (11 / 16 : ℝ) < boundary := by norm_num [boundary, rho0]
  have hs := D.high_saving
  have ht := D.t_pos
  linarith

/-- Existing theta conditions suffice for both the central overhead and height cap. -/
theorem same_D_canonical_theta_costs {Delta : ℝ} (D : HighDataPerturbed Delta)
    {theta : ℝ} (htheta2 : 2 * theta ≤ D.t) :
    physicalHeight + D.t ≤ (7 / 8 : ℝ) - 2 * D.t ∧
      D.t + 2 * theta + D.t ≤ 3 * D.t ∧
      physicalHeight * (159 * D.ε + D.t + D.t + 7 * D.t) + 2 * D.t +
        (3 / 2) * (2 * D.t) +
        (26 * D.e + (D.N + 8) * D.eps + D.t + totalE * D.t) +
        (D.t + 2 * theta + D.t) + D.t + 15 * rho0 / 8 ≤ 49 / 440640 := by
  have hcap := same_D_height_cap D
  have hover : D.t + 2 * theta + D.t ≤ 3 * D.t := by linarith
  have hnew :
      physicalHeight * (159 * D.ε + D.t + D.t + 7 * D.t) + 2 * D.t +
        (3 / 2) * (2 * D.t) +
        (26 * D.e + (D.N + 8) * D.eps + D.t + totalE * D.t) +
        (D.t + D.t + D.t) + D.t < perturbedBv6 / 2 := by
    simpa only [physicalHeight, totalE, rho0, perturbedHeight,
      perturbedTotalE, perturbedRho] using D.new_central_budget
  have hnum : perturbedBv6 / 2 + 15 * rho0 / 8 < (49 / 440640 : ℝ) := by
    norm_num [perturbedBv6, rho0]
  exact ⟨by linarith, hover, by linarith⟩

/-- Select theta from D, with arbitrary eta-independent growth order J. -/
theorem exists_canonical_theta_same_D {Delta : ℝ} (D : HighDataPerturbed Delta)
    (J : ℝ) (hJ : 0 ≤ J) :
    ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
      4 * theta < (1 / 200 : ℝ) * D.cost ∧ theta < D.t ∧
      2 * theta * (1 + J) ≤ D.t ∧ theta * (2 + 4 * D.eps) < D.t ∧
      2 * theta ≤ D.t := by
  obtain ⟨theta, hpos, hd, hcost, ht, hJcost, heps⟩ := D.height_choice J hJ
  refine ⟨theta, hpos, hd, hcost, ht, hJcost, heps, ?_⟩
  nlinarith

/-- Auxiliary decay order, distinct from the detector-bin number n. -/
theorem exists_canonical_decay_order (theta saving : ℝ) (htheta : 0 < theta) :
    ∃m : ℕ, (9 : ℝ) + saving < theta * m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (((9 : ℝ) + saving) / theta)
  exact ⟨m, (div_lt_iff₀ htheta).mp hm |>.trans_eq (mul_comm _ _)⟩

end SevenEighths.PerturbedCanonicalLocalPrep
end
end OAI
