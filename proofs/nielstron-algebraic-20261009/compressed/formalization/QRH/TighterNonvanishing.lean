import QRH.Nonvanishing

/-! Stronger nonvanishing at `tightTheta`. The original `theta` and its final
theorems remain unchanged; `tightTheta_lt_theta` certifies strict improvement. -/
namespace QRH
open scoped _root_.DirichletCharacter

theorem Hecke.LFunction_ne_zero_of_tightTheta_lt_re
    (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : tightTheta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 :=
  OAI.SevenEighths.HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    (OAI.SevenEighths.QRHFinalAssembly.beta_le_tightTheta.trans_lt hs) hpole

theorem DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : tightTheta < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
    linarith [NumericFacts.theta_lower]
  have hh := Hecke.LFunction_ne_zero_of_tightTheta_lt_re
    (OAI.SevenEighths.HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [OAI.SevenEighths.HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at hh
  exact (mul_ne_zero_iff.mp hh).1

theorem riemannZeta_ne_zero_of_tightTheta_lt_re {s : ℂ}
    (hs : tightTheta < s.re) : riemannZeta s ≠ 0 := by
  by_cases h : s = 1
  · subst s; exact riemannZeta_one_ne_zero
  · simpa only [_root_.DirichletCharacter.LFunction_modOne_eq] using
      DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re
        (1 : _root_.DirichletCharacter ℂ 1) hs (fun hexc => h hexc.2)

theorem riemannZeta_zero_re_le_tightTheta {s : ℂ}
    (hz : riemannZeta s = 0) : s.re ≤ tightTheta :=
  le_of_not_gt fun hs => riemannZeta_ne_zero_of_tightTheta_lt_re hs hz

end QRH
