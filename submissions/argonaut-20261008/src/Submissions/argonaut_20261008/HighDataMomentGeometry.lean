import Submissions.argonaut_20261008.ParametersHighDataPerturbed
import Submissions.argonaut_20261008.PerturbedMomentConstruction

namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.PerturbedMomentConstruction

open Parameters
open CenteredMomentEnergyWidthRanges

/-!
Candidate adapter, NOT_RUN. The original scalar record and browser-returned
moment record stay unchanged. Every geometric quantity is projected from the
same actual HighDataPerturbedBudget, with the prescribed fine mesh.
-/

lemma detectorMesh_positive_scalar (t : ℝ) (ht : 0 < t) :
    0 < detectorMesh t := by
  have hs : 0 < stageError t := by
    dsimp [stageError]
    positivity
  unfold detectorMesh
  exact fineMesh_pos 2 0 1 momentKappa (stageError t)
    (by norm_num) (by norm_num)
    (show 0 ≤ momentKappa by linarith [momentKappa_ge_three_quarters]) hs

def momentGeometryOfPerturbed {Δ B : ℝ} (D : HighDataPerturbedBudget Δ B)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200) : MomentGeometry where
  t := D.t
  N := D.N
  ell := D.ell
  rmin := D.rmin
  ε := D.ε
  e := D.e
  cost := D.cost
  eps := D.eps
  sigma := D.sigma
  t_pos := D.t_pos
  t_small := D.t_small
  slots_pos := D.slots_pos
  slots_injective := D.slots_injective
  slots_sum := by
    simpa only [perturbedTotalE, perturbedRho,
      HighFrontierTargets.totalE, HighFrontierTargets.rho] using D.slots_sum
  slots_bounds := D.slots_bounds
  rmin_pos := D.rmin_pos
  epsilon_pos := D.epsilon_pos
  epsilon_small := D.epsilon_small
  e_pos := D.e_pos
  e_small := D.e_small
  cost_pos := D.cost_pos
  eps_pos := D.eps_pos
  eps_small := D.eps_small
  sigma_pos := D.sigma_pos
  fine_slots := hfine
  height_choice := D.height_choice

theorem exists_perturbed_data_with_moment_geometry
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ D : HighDataPerturbed Δ,
      ∃ hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200,
        let G := momentGeometryOfPerturbed D hfine
        G.t = D.t ∧ G.N = D.N ∧ G.ell = D.ell ∧ G.e = D.e := by
  obtain ⟨D, hfine⟩ := exists_high_data_perturbed_fine
    Δ hΔ detectorMesh detectorMesh_positive_scalar
  exact ⟨D, hfine, rfl, rfl, rfl, rfl⟩

end SevenEighths.PerturbedMomentConstruction
end
end OAI
