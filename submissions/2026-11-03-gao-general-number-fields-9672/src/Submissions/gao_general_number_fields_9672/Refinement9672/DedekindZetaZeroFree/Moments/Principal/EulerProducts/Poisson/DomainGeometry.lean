/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Moments/Principal/EulerProducts/Poisson/DomainGeometry.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.Domain

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.EulerGeometry

open _root_.DedekindZetaZeroFree.Quantitative.EulerDomain
open DedekindZetaZeroFree.Quantitative.EulerDomain

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree

private def initialPt : Coordinates := ((4 : ℂ), (4 : ℂ), (2 : ℂ))

private theorem initialPt_mem : initialPt ∈ OmegaStar := by
  simp only [OmegaStar, Set.mem_setOf_eq, initialPt]
  norm_num

theorem OmegaStar_isOpen : IsOpen OmegaStar := by
  simp only [OmegaStar, Set.setOf_and]
  repeat' apply IsOpen.inter
  all_goals
    first
    | exact isOpen_lt continuous_const (by fun_prop)
    | exact isOpen_lt (by fun_prop) continuous_const

theorem OmegaStar_convex : Convex ℝ OmegaStar := by
  simp only [OmegaStar, Set.setOf_and]
  repeat' apply Convex.inter
  all_goals (apply convex_halfSpace_gt; constructor <;> intros <;> simp <;> ring)

theorem OmegaStar_isConnected : IsConnected OmegaStar :=
  OmegaStar_convex.isConnected ⟨initialPt, initialPt_mem⟩

theorem OmegaStarMargin_convex (δ : ℝ) : Convex ℝ (OmegaStarMargin δ) := by
  simp only [OmegaStarMargin, Set.setOf_and]
  repeat' apply Convex.inter
  all_goals (apply convex_halfSpace_ge; constructor <;> intros <;> simp <;> ring)

private theorem box₁_subset_OmegaStar : box₁ ⊆ OmegaStar := by
  intro p hp
  simp only [box₁, box, Set.mem_setOf_eq, Scales.goodLine] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [OmegaStar, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem box₂_subset_OmegaStar : box₂ ⊆ OmegaStar := by
  intro p hp
  simp only [box₂, box, Set.mem_setOf_eq, Scales.rightLine, Scales.contourOffset] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [OmegaStar, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem box₃_subset_OmegaStar : box₃ ⊆ OmegaStar := by
  intro p hp
  simp only [box₃, box, Set.mem_setOf_eq, Scales.rightLine, Scales.contourOffset] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [OmegaStar, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem boxes_subset_OmegaStar' : boxes ⊆ OmegaStar := by
  intro p hp
  rcases hp with (h | h) | h
  · exact box₁_subset_OmegaStar h
  · exact box₂_subset_OmegaStar h
  · exact box₃_subset_OmegaStar h

theorem box₁_margins : ∀ p ∈ box₁,
    1 + 152 / 100 ≤ 6 * p.2.2.re + p.2.1.re ∧
    1 + 22801 / 10000 ≤ p.1.re + 6 * p.2.2.re ∧
    1 + 1 / 10000 ≤ p.1.re + p.2.1.re ∧
    2 + 14001 / 10000 ≤ p.1.re + p.2.1.re + 6 * p.2.2.re ∧
    5 + 26806 / 10000 ≤ 6 * p.1.re + 6 * p.2.2.re ∧
    1 / 2 + 3801 / 10000 ≤ p.1.re ∧
    5 / 2 + 2603 / 10000 ≤ 3 * p.1.re + p.2.1.re := by
  intro p hp
  simp only [box₁, box, Set.mem_setOf_eq, Scales.goodLine] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem paddedBox₁_xy_margin : ∀ p ∈ paddedBox₁, 1 + 98 / 1000000 ≤ p.1.re + p.2.1.re := by
  intro p hp
  simp only [paddedBox₁, box, Set.mem_setOf_eq, Scales.goodLine, pad] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  linarith

theorem paddedBoxes_subset_OmegaStarMargin_explicit :
    paddedBoxes ⊆ OmegaStarMargin (98 / 1000000) := by
  intro p hp
  rcases hp with (h | h) | h
  · simp only [paddedBox₁, box, Set.mem_setOf_eq, Scales.goodLine, pad] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [OmegaStarMargin, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [paddedBox₂, box, Set.mem_setOf_eq, Scales.rightLine, Scales.contourOffset, pad] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [OmegaStarMargin, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [paddedBox₃, box, Set.mem_setOf_eq, Scales.rightLine, Scales.contourOffset, pad] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [OmegaStarMargin, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem paddedBox₁_subset_OmegaStar : paddedBox₁ ⊆ OmegaStar := by
  intro p hp
  exact OmegaStarMargin_subset _ (by norm_num)
    (paddedBoxes_subset_OmegaStarMargin_explicit (Or.inl (Or.inl hp)))

theorem paddedBox₂_subset_OmegaStar : paddedBox₂ ⊆ OmegaStar := by
  intro p hp
  exact OmegaStarMargin_subset _ (by norm_num)
    (paddedBoxes_subset_OmegaStarMargin_explicit (Or.inl (Or.inr hp)))

theorem paddedBox₃_subset_OmegaStar : paddedBox₃ ⊆ OmegaStar := by
  intro p hp
  exact OmegaStarMargin_subset _ (by norm_num)
    (paddedBoxes_subset_OmegaStarMargin_explicit (Or.inr hp))

def initialPoint : Coordinates := ((4 : ℂ), (4 : ℂ), (2 : ℂ))

theorem OmegaStar_right_line (p : Coordinates) (hx : p.1.re = 4) (hy : p.2.1.re = 4)
    (hv : 2 ≤ p.2.2.re) : p ∈ OmegaStar := by
  simp only [OmegaStar, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem paddedBoxes_joinedIn_initial :
    ∀ p ∈ paddedBoxes, JoinedIn OmegaStar p initialPoint := by
  have hinit : initialPoint ∈ OmegaStar := by
    have := initialPt_mem
    simpa [initialPoint, initialPt] using this
  intro p hp
  have hO : p ∈ OmegaStar := by
    rcases hp with (h | h) | h
    · exact paddedBox₁_subset_OmegaStar h
    · exact paddedBox₂_subset_OmegaStar h
    · exact paddedBox₃_subset_OmegaStar h
  exact (OmegaStar_convex.isPathConnected ⟨initialPoint, hinit⟩).joinedIn p hO initialPoint hinit

theorem boxes_joinedIn_initial :
    ∀ p ∈ boxes, JoinedIn OmegaStar p initialPoint := by
  have hinit : initialPoint ∈ OmegaStar := by
    have := initialPt_mem
    simpa [initialPoint, initialPt] using this
  intro p hp
  exact (OmegaStar_convex.isPathConnected ⟨initialPoint, hinit⟩).joinedIn p
    (boxes_subset_OmegaStar' hp) initialPoint hinit

end

end DedekindZetaZeroFree.Quantitative.EulerGeometry

end Refinement9672
