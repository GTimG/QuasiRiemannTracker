import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Arithmetic.Bernstein.NewRow
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Arithmetic.Bernstein.OldJunction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Arithmetic.Bernstein.OldHalf

namespace Cycle61.Arithmetic.Bernstein

theorem six_box_cover {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    (δ ∈ Set.Icc 0 (3/8) ∧ p ∈ Set.Icc 0 (1/2)) ∨
    (δ ∈ Set.Icc (3/8) (3/4) ∧ p ∈ Set.Icc 0 (1/4)) ∨
    (δ ∈ Set.Icc (3/8) (9/16) ∧ p ∈ Set.Icc (1/4) (3/8)) ∨
    (δ ∈ Set.Icc (3/8) (15/32) ∧ p ∈ Set.Icc (3/8) (1/2)) ∨
    (δ ∈ Set.Icc (15/32) (9/16) ∧ p ∈ Set.Icc (3/8) (1/2)) ∨
    (δ ∈ Set.Icc (9/16) (3/4) ∧ p ∈ Set.Icc (1/4) (1/2)) := by
  rcases le_total δ (3/8) with hd | hd
  · exact Or.inl ⟨⟨hδ.1, hd⟩, hp⟩
  · right
    rcases le_total p (1/4) with hp' | hp'
    · exact Or.inl ⟨⟨hd, hδ.2⟩, hp.1, hp'⟩
    · right
      rcases le_total δ (9/16) with hd' | hd'
      · rcases le_total p (3/8) with hp'' | hp''
        · exact Or.inl ⟨⟨hd, hd'⟩, hp', hp''⟩
        · right
          rcases le_total δ (15/32) with hd'' | hd''
          · exact Or.inl ⟨⟨hd, hd''⟩, hp'', hp.2⟩
          · exact Or.inr (Or.inl ⟨⟨hd'', hd'⟩, hp'', hp.2⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨⟨hd', hδ.2⟩, hp', hp.2⟩))

theorem newRowPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < newRowPower δ p := by
  rcases six_box_cover hδ hp with h | h | h | h | h | h
  · exact newRowBox0_pos h.1 h.2
  · exact newRowBox1_pos h.1 h.2
  · exact newRowBox2_pos h.1 h.2
  · exact newRowBox3_pos h.1 h.2
  · exact newRowBox4_pos h.1 h.2
  · exact newRowBox5_pos h.1 h.2

theorem oldJunctionPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldJunctionPower δ p := by
  rcases six_box_cover hδ hp with h | h | h | h | h | h
  · exact oldJunctionBox0_pos h.1 h.2
  · exact oldJunctionBox1_pos h.1 h.2
  · exact oldJunctionBox2_pos h.1 h.2
  · exact oldJunctionBox3_pos h.1 h.2
  · exact oldJunctionBox4_pos h.1 h.2
  · exact oldJunctionBox5_pos h.1 h.2

theorem oldHalfPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldHalfPower δ p :=
  oldHalfBox0_pos hδ hp

end Cycle61.Arithmetic.Bernstein
