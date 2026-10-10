import QRH.TighterNonvanishing

namespace QRHPalomar
open scoped _root_.DirichletCharacter

private theorem root_eq (e : ℝ) (he : e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ))
    (hp : 657*e^3-954*e^2+21*e+20=0) : e = QRH.Algebraic.root := by
  have hz : QRH.Algebraic.cubic e = 0 := hp
  exact QRH.Algebraic.cubic_strictAnti.injOn he QRH.Algebraic.root_spec.1
    (hz.trans QRH.Algebraic.root_spec.2.symm)

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (874957019420098946128603850561452983 / 1000000000000000000000000000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re χ
    (QRH.Algebraic.limitingTheta_upper.trans hs) hpole

theorem zeta {s : ℂ}
    (hs : (874957019420098946128603850561452983 / 1000000000000000000000000000000000000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  exact QRH.riemannZeta_ne_zero_of_tightTheta_lt_re
    (QRH.Algebraic.limitingTheta_upper.trans hs)

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (874957019420098946128603850561452983 / 1000000000000000000000000000000000000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re χ s
    (QRH.Algebraic.limitingTheta_upper.trans hs) hpole

theorem allDirichletExact (e : ℝ) (he : e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ))
    (hp : 657*e^3-954*e^2+21*e+20=0)
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 11/12-e/4 < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  rw [root_eq e he hp] at hs
  exact QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re χ hs hpole

theorem zetaExact (e : ℝ) (he : e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ))
    (hp : 657*e^3-954*e^2+21*e+20=0) {s : ℂ}
    (hs : 11/12-e/4 < s.re) : riemannZeta s ≠ 0 := by
  rw [root_eq e he hp] at hs
  exact QRH.riemannZeta_ne_zero_of_tightTheta_lt_re hs

theorem allHeckeExact (e : ℝ) (he : e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ))
    (hp : 657*e^3-954*e^2+21*e+20=0)
    (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : 11/12-e/4 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  rw [root_eq e he hp] at hs
  exact QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re χ s hs hpole

theorem existsUniqueRoot :
    ∃! e : ℝ, e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ) ∧ 657*e^3-954*e^2+21*e+20=0 := by
  exact QRH.Algebraic.exists_unique_root

end QRHPalomar
