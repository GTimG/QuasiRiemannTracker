/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Geometry/TranslatedLatticeGap.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

namespace DedekindZetaZeroFree

theorem thetaTranslateGap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (z : E) :
    ∃ η : ℝ, 0 < η ∧ ∀ ℓ : L, z + (ℓ : E) ≠ 0 → η ≤ ‖z + (ℓ : E)‖ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hdisc : IsDiscrete ((L : Set E)) := DiscreteTopology.isDiscrete
  have hclosed : IsClosed ((L : Set E)) :=
    AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)

  have hbdd : Bornology.IsBounded (Metric.closedBall (0 : E) (1 + ‖z‖)) :=
    Metric.isBounded_closedBall
  have hSfin : Set.Finite ({x : E | x ∈ (L : Set E) ∧ ‖z + x‖ ≤ 1}) := by
    refine (Metric.finite_isBounded_inter_isClosed hdisc hbdd hclosed).subset ?_
    intro x hx
    refine ⟨?_, hx.1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
      have := norm_sub_le (z + x) z
      simpa using this
    linarith [hx.2]
  have hfin : Set.Finite ({ℓ : L | ‖z + (ℓ : E)‖ ≤ 1} : Set L) :=
    (hSfin.preimage_embedding (Function.Embedding.subtype (· ∈ (L : Set E)))).subset
      (by intro ℓ hℓ; exact ⟨ℓ.2, hℓ⟩)
  rcases Set.eq_empty_or_nonempty
      ({ℓ : L | z + (ℓ : E) ≠ 0 ∧ ‖z + (ℓ : E)‖ ≤ 1} : Set L) with hempty | hne
  ·
    refine ⟨1, one_pos, fun ℓ hℓ => ?_⟩
    by_contra hcon
    have h2 : ‖z + (ℓ : E)‖ ≤ 1 := le_of_lt (not_le.mp hcon)
    have hmem : ℓ ∈ ({ℓ : L | z + (ℓ : E) ≠ 0 ∧ ‖z + (ℓ : E)‖ ≤ 1} : Set L) := ⟨hℓ, h2⟩
    rw [hempty] at hmem
    exact hmem
  · have hfin' : ({ℓ : L | z + (ℓ : E) ≠ 0 ∧ ‖z + (ℓ : E)‖ ≤ 1} : Set L).Finite :=
      hfin.subset (by intro ℓ hℓ; exact hℓ.2)
    obtain ⟨b, hb, hmin⟩ :=
      Set.exists_min_image _ (fun ℓ : L => ‖z + (ℓ : E)‖) hfin' hne
    refine ⟨min 1 ‖z + (b : E)‖, lt_min one_pos (norm_pos_iff.mpr hb.1), fun ℓ hℓ => ?_⟩
    by_cases h2 : ‖z + (ℓ : E)‖ ≤ 1
    · have hmem : ℓ ∈ ({ℓ : L | z + (ℓ : E) ≠ 0 ∧ ‖z + (ℓ : E)‖ ≤ 1} : Set L) :=
        ⟨hℓ, h2⟩
      exact (min_le_right _ _).trans (hmin ℓ hmem)
    · exact (min_le_left _ _).trans (le_of_lt (not_le.mp h2))

end DedekindZetaZeroFree
