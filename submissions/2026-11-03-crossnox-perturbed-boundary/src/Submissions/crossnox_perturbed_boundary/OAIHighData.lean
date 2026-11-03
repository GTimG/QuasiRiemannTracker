/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighData.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighCentralBudget
import Submissions.crossnox_perturbed_boundary.OAIHighSlotLengths
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersDetectorScales

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters
open AsymmetricGeometry

structure PerturbedHighData (gap : ℝ) where
  small : ℝ
  N : ℕ
  ell : Fin N → ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  small_pos : 0 < small
  small_gap : small < gap / 4
  small_cap : small ≤ 1 / 10000000000000000
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑ j, ell j) = 1 / 6 + perturbedSlotLengthShift
  slots_bounds : ∀ j, 0 < ell j ∧ (7 / 8) * rmin ≤ ell j ∧
    ell j ≤ (1 / 200) * ((1 + 6 * perturbedSlotLengthShift) * small)
  rmin_pos : 0 < rmin
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1 / 1000
  epsilon_gap : ε < rmin * small
  e_pos : 0 < e
  e_small : e < 1 / 1000
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  sigma_pos : 0 < sigma
  detector_budget : 288 * e + 8 * κ + 2 * cost ≤ ε / 2
  phase_budget : 8 * e * ((1 + 6 * perturbedSlotLengthShift) * small) + κ ≤ ε
  count_budget : 159 * ε + small +
    (1 + 6 * perturbedSlotLengthShift) * small + 7 * small ≤ 1 / 32
  central_budget :
    (rowBase + 3 * perturbedSlotLengthShift / 2) * (159 * ε + small +
      (1 + 6 * perturbedSlotLengthShift) * small + 7 * small) +
      2 * small + (3 / 2) * (2 * small) +
      (26 * e + (N + 8) * eps + small + small / 6) +
      (small + small + small) + small +
      perturbedSlotLengthShift * (3 * e + small) + 6 * skew * e ≤ highMargin
  row_threshold : rowBase + 3 * perturbedSlotLengthShift / 2 +
    3 * small ≤ 7 / 8
  geometric_budget : sigma + 8 * e + small / 8 +
    51 * perturbedSlotLengthShift / 100 + 49 * skew / 150 ≤ 63 / 800
  principal_budget : sigma + small / 8 ≤ 1 / 3000
  window_budget : sigma + e ≤ (boundary) * ((7 / 8) * rmin)
  floor_budget : 2 * small + 26 * e + (N + 8) * eps +
    small + small / 6 + small / 8 + sigma + boundaryReduction +
    perturbedSlotLengthShift * (121 / 40 + 3 * e + small) +
      skew * (67 / 100 + 6 * e) ≤ 7 / 1200
  high_saving : sigma + small / 8 + small / 8 ≤ small
  height_choice : ∀ J : ℝ, 0 ≤ J → ∃ τ : ℝ,
    0 < τ ∧ τ < (1 / 200) / 2 ∧
    4 * τ < (1 / 200) * cost ∧ τ < small ∧
    2 * τ * (1 + J) ≤ small ∧ τ * (2 + 4 * eps) < small

theorem exists_perturbed_high_data_fine
    (gap : ℝ) (hgap : 0 < gap)
    (mesh : ℝ → ℝ) (hmesh : ∀ small : ℝ, 0 < small → 0 < mesh small) :
    ∃ D : PerturbedHighData gap,
      ∀ j, D.ell j ≤ mesh D.small / 200 := by
  obtain ⟨small, hsmall, hsmall_gap, hsmall_cap, hrow, hallow⟩ :=
    exists_perturbed_central_budget gap hgap
  let slotMesh := (1 + 6 * perturbedSlotLengthShift) * small
  have hslotMesh : 0 < slotMesh := by
    dsimp [slotMesh, perturbedSlotLengthShift]
    positivity
  obtain ⟨N, hN, ell, rmin, hrmin, hinj, hsum, hbounds, _⟩ :=
    exists_physical_slot_lengths_with_mass
      (1 / 6 + perturbedSlotLengthShift) (1 / 200) (7 / 8)
      (min slotMesh (mesh small)) small
      (by dsimp [perturbedSlotLengthShift]; norm_num)
      (by norm_num) (by norm_num)
      (lt_min hslotMesh (hmesh small hsmall)) hsmall
  obtain ⟨allowance, hallowance, hallowance_bound, hbud⟩ := hallow N
  let ellMin := (7 / 8 : ℝ) * rmin
  have hellMin : 0 < ellMin := mul_pos (by norm_num) hrmin
  obtain ⟨ε, e, κ, cost, _, hε, hε1, hεgap, hεa,
    he, he1, heell, hea, hκ, hκ1, hcost,
    hdet, hphase, _, _, _, _, _⟩ :=
    exists_detector_scales slotMesh rmin small (1 / 200)
      small ellMin allowance 0
      hslotMesh.le hrmin hsmall (by norm_num) hsmall hellMin
      hallowance (by norm_num)
  let eps := allowance / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heps_allowance : eps ≤ allowance := by
    dsimp [eps]
    linarith
  have hallowance_cap : allowance ≤ small / 2000 :=
    hallowance_bound.trans
      (div_le_div_of_nonneg_left hsmall.le (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) N]))
  have heps1 : eps ≤ 1 := by
    dsimp [eps]
    linarith
  have hbud' := hbud ε e eps hε.le hεa he.le hea heps.le heps_allowance
  have he8 : ((N : ℝ) + 8) * eps ≤ small := by
    have h := mul_le_mul_of_nonneg_left
      (heps_allowance.trans hallowance_bound)
      (show 0 ≤ (N : ℝ) + 2000 by positivity)
    have hcancel : ((N : ℝ) + 2000) *
        (small / ((N : ℝ) + 2000)) = small := by
      field_simp
    nlinarith
  let sigma := min (small / 2) (ellMin / 4)
  have hsigma : 0 < sigma := lt_min (by positivity) (by positivity)
  have hsigma_small : sigma ≤ small / 2 := min_le_left _ _
  have hsigma_ell : sigma ≤ ellMin / 4 := min_le_right _ _
  refine ⟨{
    small := small, N := N, ell := ell, rmin := rmin,
    ε := ε, e := e, κ := κ, cost := cost, eps := eps, sigma := sigma,
    small_pos := hsmall, small_gap := hsmall_gap, small_cap := hsmall_cap,
    slots_pos := hN, slots_injective := hinj, slots_sum := hsum,
    slots_bounds := fun j => ⟨(hbounds j).1, (hbounds j).2.1,
      (hbounds j).2.2.1.trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))⟩,
    rmin_pos := hrmin, epsilon_pos := hε, epsilon_small := hε1,
    epsilon_gap := hεgap, e_pos := he, e_small := he1,
    kappa_pos := hκ, kappa_small := hκ1, cost_pos := hcost,
    eps_pos := heps, eps_small := heps1, sigma_pos := hsigma,
    detector_budget := by linarith only [hdet], phase_budget := hphase,
    count_budget := hbud'.1, central_budget := hbud'.2,
    row_threshold := hrow,
    geometric_budget := ?_, principal_budget := ?_,
    window_budget := ?_, floor_budget := ?_,
    high_saving := ?_, height_choice := ?_ }, ?_⟩
  · dsimp [perturbedSlotLengthShift]
    linarith only [hsigma_small, hea, hallowance_cap, hsmall_cap]
  · linarith only [hsigma_small, hsmall_cap]
  · have hsum : sigma + e ≤ ellMin / 2 := by
      linarith only [hsigma_ell, heell]
    have hcoef : (1 / 2 : ℝ) ≤ boundary := by norm_num
    have hscaled := mul_le_mul_of_nonneg_right hcoef hellMin.le
    dsimp [ellMin] at hsum hscaled ⊢
    linarith
  · dsimp [perturbedSlotLengthShift]
    linarith only [hsigma_small, hea, hallowance_cap,
      he8, hsmall_cap]
  · linarith only [hsigma_small, hsmall.le]
  · intro J hJ
    let τ := min ((1 / 200 : ℝ) * cost / 16)
      (min (1 / 800) (small / (4 * (J + 7))))
    have hτ : 0 < τ :=
      lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτcost : τ ≤ (1 / 200 : ℝ) * cost / 16 := min_le_left _ _
    have hτcap : τ ≤ 1 / 800 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hτJ : τ ≤ small / (4 * (J + 7)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hτbound : τ * (4 * (J + 7)) ≤ small :=
      (le_div_iff₀ (by positivity)).mp hτJ
    have hprod : 0 ≤ τ * J := mul_nonneg hτ.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 hτ.le
    refine ⟨τ, hτ, by linarith only [hτcap],
      by linarith only [hτcost, hcost],
      by nlinarith only [hτbound, hprod, hτ],
      by nlinarith only [hτbound, hprod, hτ],
      by nlinarith only [hτbound, hprod, hprodeps, hτ]⟩
  · intro j
    change ell j ≤ mesh small / 200
    calc
      ell j ≤ (1 / 200 : ℝ) * min slotMesh (mesh small) :=
        (hbounds j).2.2.1
      _ ≤ (1 / 200 : ℝ) * mesh small :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ = mesh small / 200 := by ring

theorem exists_perturbed_high_data (gap : ℝ) (hgap : 0 < gap) :
    Nonempty (PerturbedHighData gap) := by
  obtain ⟨D, _⟩ := exists_perturbed_high_data_fine gap hgap
    (fun _ => 1) (by intros; norm_num)
  exact ⟨D⟩

end SevenEighths.Parameters

end

end OAI
