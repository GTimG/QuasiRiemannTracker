import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Hecke.CommonProbeBoundaryGeneric

namespace OAI
noncomputable section
open scoped Classical

namespace SevenEighths.HeckeDirichlet
open HeckeFamily

theorem dirichlet_boundary_of_hecke
    (b0 : ℝ) (hb0 : 0 < b0)
    (hH : ∀ (η : Character) (s : ℂ), b0 < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : b0 < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by
    intro h
    have hp : 0 < s.re := hb0.trans hs
    simpa [h] using hp
  have h := hH (character χ) s hs (Or.inl hs1)
  rw [LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_boundary_of_hecke
    (b0 : ℝ) (hb0 : 0 < b0)
    (hH : ∀ (η : Character) (s : ℂ), b0 < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (s : ℂ) (hs : b0 < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_boundary_of_hecke b0 hb0 hH
    (1 : DirichletCharacter ℂ 1) s hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end SevenEighths.HeckeDirichlet

namespace SevenEighths.HeckeCommonProbe
open HeckeFamily

theorem dirichlet_of_common_probe_boundary
    {b0 : ℝ} (h : UniformCommonProbeBoundary b0)
    (q : ℕ) (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : b0 < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  letI : NeZero q := ⟨hq⟩
  have hb0 : 0 < b0 := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) h.1
  exact HeckeDirichlet.dirichlet_boundary_of_hecke b0 hb0
    (hecke_ne_zero_of_common_probe_boundary h) χ s hs hexc

theorem zeta_of_common_probe_boundary
    {b0 : ℝ} (h : UniformCommonProbeBoundary b0)
    (s : ℂ) (hs : b0 < s.re) : riemannZeta s ≠ 0 := by
  have hb0 : 0 < b0 := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) h.1
  exact HeckeDirichlet.zeta_boundary_of_hecke b0 hb0
    (hecke_ne_zero_of_common_probe_boundary h) s hs

end SevenEighths.HeckeCommonProbe
end
end OAI
