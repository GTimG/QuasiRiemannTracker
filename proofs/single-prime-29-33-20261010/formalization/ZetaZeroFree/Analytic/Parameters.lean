import ZetaZeroFree.Analytic.LossBudget

/-! Positive common losses are fixed from the supremum gap. Height parameters
are chosen after the polynomial orders, without changing the common saving. -/

namespace ZetaZeroFree.Analytic.CommonParameters
noncomputable section

def saving (beta : ℝ) : ℝ := min ((beta - Exponent.b) / 16) (1 / 16000)
def smallLoss (beta : ℝ) : ℝ := saving beta / 1000000
def contourE (beta : ℝ) : ℝ := smallLoss beta / 1000000000
def arithmeticEpsilon (beta : ℝ) : ℝ := smallLoss beta / 1000000
def witnessEpsilon (beta : ℝ) : ℝ := smallLoss beta / 1000

theorem saving_pos {beta : ℝ} (hbeta : Exponent.b < beta) : 0 < saving beta := by
  unfold saving
  exact lt_min (by linarith) (by norm_num)

theorem smallLoss_pos {beta : ℝ} (hbeta : Exponent.b < beta) : 0 < smallLoss beta :=
  div_pos (saving_pos hbeta) (by norm_num)

theorem saving_le_constant (beta : ℝ) : saving beta ≤ 1 / 16000 :=
  min_le_right _ _

theorem saving_le_gap (beta : ℝ) : saving beta ≤ (beta - Exponent.b) / 16 :=
  min_le_left _ _

theorem smallLoss_le_constant (beta : ℝ) : smallLoss beta ≤ 1 / 16000000000 := by
  have hs := saving_le_constant beta
  unfold smallLoss
  linarith

/-- The finite row losses and reciprocal-normalizer loss leave a common saving. -/
theorem central_slack {beta : ℝ} (hbeta : Exponent.b < beta) :
    20 * smallLoss beta + smallLoss beta + saving beta < (beta - Exponent.b) / 2 := by
  have hs := saving_le_gap beta
  have hp := saving_pos hbeta
  unfold smallLoss
  linarith

theorem physical_slack {beta : ℝ} (hbeta : Exponent.b < beta) :
    0 < (beta - Exponent.b) / 4 ∧ (beta - Exponent.b) / 4 < beta - Exponent.b := by
  constructor <;> linarith

/-- Fixed geometry and local loss gates for the one-prime construction. -/
theorem fixed_guards {beta : ℝ} (hbeta : Exponent.b < beta) :
    0 < contourE beta ∧ contourE beta < 1 / 1000 ∧
    0 < arithmeticEpsilon beta ∧ 0 < witnessEpsilon beta ∧
    witnessEpsilon beta ≤ 1 / 1000 ∧
    smallLoss beta ≤ 1 / 48 ∧
    (25 / 33 : ℝ) + smallLoss beta + 2 * arithmeticEpsilon beta ≤ 4 / 5 ∧
    288 * contourE beta + 8 * contourE beta + 2 * arithmeticEpsilon beta ≤
      witnessEpsilon beta / 2 ∧
    8 * contourE beta * 100 + contourE beta ≤ witnessEpsilon beta ∧
    witnessEpsilon beta < (1 / 10 : ℝ) * smallLoss beta ∧
    saving beta + 8 * contourE beta + smallLoss beta ≤ 1 / 25 ∧
    saving beta + smallLoss beta ≤ 1 / 4000 ∧
    saving beta + contourE beta ≤ 35 / 264 ∧
    9 * arithmeticEpsilon beta ≤ 1 := by
  have hp := smallLoss_pos hbeta
  have hu := smallLoss_le_constant beta
  have hs := saving_le_constant beta
  unfold contourE arithmeticEpsilon witnessEpsilon
  refine ⟨by positivity, ?_, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals linarith

/-- All central row, bin, height and dyad losses at the proposed fixed scales. -/
theorem central_loss_bound {beta : ℝ} (hbeta : Exponent.b < beta) :
    2 * smallLoss beta + 6 * arithmeticEpsilon beta + (146 / 11) * contourE beta +
      ((25 / 33 : ℝ) + smallLoss beta + 2 * arithmeticEpsilon beta) *
        (7 * witnessEpsilon beta + 12 * contourE beta + 9 * arithmeticEpsilon beta) +
      (5 / 33) * smallLoss beta + smallLoss beta + smallLoss beta +
      smallLoss beta / 8 + smallLoss beta ≤ 10 * smallLoss beta := by
  have hp := smallLoss_pos hbeta
  rcases fixed_guards hbeta with ⟨_, _, _, _, _, _, hcap, _⟩
  have herror : 0 ≤ 7 * witnessEpsilon beta + 12 * contourE beta +
      9 * arithmeticEpsilon beta := by
    unfold witnessEpsilon contourE arithmeticEpsilon
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcap herror
  unfold witnessEpsilon contourE arithmeticEpsilon at *
  linarith

/-- The floor bin has an absolute margin even before using the supremum gap. -/
theorem floor_loss_bound {beta : ℝ} (hbeta : Exponent.b < beta) :
    (137 / 825 : ℝ) + (67 / 100) * smallLoss beta + (146 / 11) * contourE beta +
      ((25 / 33 : ℝ) + smallLoss beta) *
        (12 * contourE beta + 9 * arithmeticEpsilon beta) +
      (5 / 33) * smallLoss beta + smallLoss beta ≤ 20 / 99 + 10 * smallLoss beta := by
  have hp := smallLoss_pos hbeta
  have hu := smallLoss_le_constant beta
  have hcap : (25 / 33 : ℝ) + smallLoss beta ≤ 4 / 5 := by linarith
  have herror : 0 ≤ 12 * contourE beta + 9 * arithmeticEpsilon beta := by
    unfold contourE arithmeticEpsilon
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcap herror
  unfold contourE arithmeticEpsilon at *
  linarith

/-- Choose the frequency allowance and then the cube height, after all orders.
The loss `u` stays fixed while the order `N` varies. -/
theorem exists_height_choices {u eps cost dmin N : ℝ}
    (hu : 0 < u) (heps : 0 ≤ eps) (hcost : 0 < cost)
    (hdmin : 0 < dmin) (hN : 0 ≤ N) :
    ∃ q tau : ℝ, 0 < q ∧ 0 < tau ∧ tau < q ∧
      N * q ≤ u / 8 ∧ q ≤ u / 8 ∧ tau < dmin / 2 ∧
      4 * tau < dmin * cost ∧ tau * (2 + 4 * eps) < u := by
  obtain ⟨q, hq, horder⟩ := exists_height_budget hu (show 0 ≤ N + 1 by linarith)
  have hNq : 0 ≤ N * q := mul_nonneg hN hq.le
  have hqsmall : q ≤ u / 8 := by nlinarith
  have hNqsmall : N * q ≤ u / 8 := by nlinarith
  let tau := min (q / 2) (min (dmin / 4)
    (min (dmin * cost / 8) (u / (2 * (3 + 4 * eps)))))
  have ht : 0 < tau := by
    dsimp [tau]
    exact lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))
  have htq : tau ≤ q / 2 := min_le_left _ _
  have htd : tau ≤ dmin / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have htc : tau ≤ dmin * cost / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htl : tau ≤ u / (2 * (3 + 4 * eps)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hden : 0 < 2 * (3 + 4 * eps) := by positivity
  have htl' := (le_div_iff₀ hden).mp htl
  refine ⟨q, tau, hq, ht, by linarith, hNqsmall, hqsmall, by linarith, ?_, ?_⟩
  · have hc := mul_pos hdmin hcost
    linarith
  · nlinarith

end
end ZetaZeroFree.Analytic.CommonParameters
