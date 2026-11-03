/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/Tensors/FiniteReferenceProducts.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.HarishChandraTailInvariance

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.CurrentReferenceProduct

theorem finite_update_factorization {J : Type*} [DecidableEq J]
    {G : J → Type*} [∀ j, One (G j)]
    (φ : (∀ j, G j) → ℂ) (r : ∀ j, G j → ℂ) (s : Finset J)
    (hs : ∀ j ∈ s, ∀ g, φ g = r j (g j) * φ (Function.update g j 1))
    (g : ∀ j, G j) :
    φ g = (∏ j ∈ s, r j (g j)) * φ (fun j => if j ∈ s then 1 else g j) := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | @insert a s ha ih =>
    rw [hs a (Finset.mem_insert_self _ _) g]
    rw [ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))]
    rw [Finset.prod_insert ha]
    have hp : (∏ j ∈ s, r j (Function.update g a 1 j)) = ∏ j ∈ s, r j (g j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hn : j ≠ a := by intro h; subst j; exact ha hj
      rw [Function.update_of_ne hn]
    have he : (fun j => if j ∈ s then 1 else Function.update g a 1 j) =
        (fun j => if j ∈ insert a s then 1 else g j) := by
      funext j
      by_cases hj : j = a
      · subst j; simp [ha]
      · simp [hj, Function.update_of_ne hj]
    rw [hp, he, mul_assoc]
end DedekindZetaZeroFree.FourierContinuation.CurrentReferenceProduct

end
