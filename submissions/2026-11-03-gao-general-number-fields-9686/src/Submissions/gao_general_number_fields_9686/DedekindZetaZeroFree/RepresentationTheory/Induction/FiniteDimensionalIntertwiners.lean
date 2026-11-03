/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Induction/FiniteDimensionalIntertwiners.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.Induction.CovariantSampling

@[expose] public section

namespace DedekindZetaZeroFree.CovariantSampling

variable {G : Type*} [Group G]

theorem sampleMap_injective
    (C K J : Subgroup G) (chi : C →* ℂ) (n : ℕ) (r : Fin n → G)
    (hcover : ∀ g : G, ∃ (i : Fin n) (c : C) (k : K) (j : J),
      g = c.val * r i * k.val * j.val)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (tau : Representation ℂ K W) :
    Function.Injective (sampleMap C K J chi hnormalize tau n r) := by
  intro T U h
  ext w g
  obtain ⟨i, c, k, j, rfl⟩ := hcover g
  rw [right_fixed, right_fixed]
  rw [mul_assoc, covariance, covariance]
  have hs : (T (tau k w)).val (r i) = (U (tau k w)).val (r i) :=
    congrArg (fun s => s i (tau k w)) h
  have ht := congrArg (fun f : V_J C J chi => f.val (r i))
    (Representation.IntertwiningMap.isIntertwining tau
      (rho_J C K J chi hnormalize) T k w)
  have hu := congrArg (fun f : V_J C J chi => f.val (r i))
    (Representation.IntertwiningMap.isIntertwining tau
      (rho_J C K J chi hnormalize) U k w)
  simp only [rho_J_apply] at ht hu
  change chi c * (T w).val (r i * k.val) =
    chi c * (U w).val (r i * k.val)
  rw [← ht, ← hu, hs]

theorem intertwiningMap_finiteDimensional
    (C K J : Subgroup G) (chi : C →* ℂ) (n : ℕ) (r : Fin n → G)
    (hcover : ∀ g : G, ∃ (i : Fin n) (c : C) (k : K) (j : J),
      g = c.val * r i * k.val * j.val)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (tau : Representation ℂ K W) :
    FiniteDimensional ℂ (tau.IntertwiningMap (rho_J C K J chi hnormalize)) := by
  exact FiniteDimensional.of_injective
    (sampleMap C K J chi hnormalize tau n r)
    (sampleMap_injective C K J chi n r hcover hnormalize tau)

end DedekindZetaZeroFree.CovariantSampling
