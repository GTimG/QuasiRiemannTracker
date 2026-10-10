import Solution
import QRH.TighterNonvanishing
import QRH.Nonvanishing
import QRH.IndependentTargets
import QRH.StatementParity
import QRH.ZeroBounds

namespace QRHPalomar.NativeAudit
open scoped _root_.DirichletCharacter

-- The protected original propositions are inhabited at their literal bound.
example : QRH.Independent.allDirichlet :=
  @QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re
example : QRH.Independent.zeta := @QRH.riemannZeta_ne_zero_of_theta_lt_re
example : QRH.Independent.allHecke := @QRH.Hecke.LFunction_ne_zero_of_theta_lt_re
example : QRH.theta = (874957019421 / 1000000000000 : ℝ) := rfl

-- The three rational targets are literal corollaries of the exact endpoint.
example : ∀ {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ},
    (874957019420098946128603850561452983 / 1000000000000000000000000000000000000 : ℝ) < s.re →
    ¬ (χ = 1 ∧ s = 1) → _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  @QRHPalomar.allDirichlet
example : ∀ {s : ℂ},
    (874957019420098946128603850561452983 / 1000000000000000000000000000000000000 : ℝ) < s.re →
    riemannZeta s ≠ 0 := @QRHPalomar.zeta
example : ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ),
    (874957019420098946128603850561452983 / 1000000000000000000000000000000000000 : ℝ) < s.re →
    (s ≠ 1 ∨ χ.residue ≠ 1) → OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 :=
  @QRHPalomar.allHecke

-- Explicit universal root quantification, without importing a challenge axiom.
example : ∀ (e : ℝ), e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ) →
    657*e^3-954*e^2+21*e+20=0 →
    ∀ {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ},
    11/12-e/4 < s.re → ¬ (χ = 1 ∧ s = 1) →
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := @QRHPalomar.allDirichletExact
example : ∀ (e : ℝ), e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ) →
    657*e^3-954*e^2+21*e+20=0 →
    ∀ {s : ℂ}, 11/12-e/4 < s.re → riemannZeta s ≠ 0 := @QRHPalomar.zetaExact
example : ∀ (e : ℝ), e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ) →
    657*e^3-954*e^2+21*e+20=0 →
    ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ),
    11/12-e/4 < s.re → (s ≠ 1 ∨ χ.residue ≠ 1) →
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := @QRHPalomar.allHeckeExact

-- Nonvacuity: existence as well as uniqueness is proved, not merely assumed.
example : ∃! e : ℝ, e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ) ∧
    657*e^3-954*e^2+21*e+20=0 := QRHPalomar.existsUniqueRoot

example : QRH.tightTheta <
    (874957019420098946128603850561452983 / 1000000000000000000000000000000000000 : ℝ) :=
  QRH.Algebraic.limitingTheta_upper
example : QRH.tightTheta <
    (874957019420098946128604623 / 1000000000000000000000000000 : ℝ) :=
  QRH.Algebraic.limitingTheta_lt_N24
example : (874957019420098946128603850561452983 / 1000000000000000000000000000000000000 : ℝ) <
    (874957019420098946128604623 / 1000000000000000000000000000 : ℝ) := by norm_num

-- Preserve the previous independently checked N24 statements by monotonicity.
theorem n24Dirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (874957019420098946128604623 / 1000000000000000000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re χ
    (QRH.Algebraic.limitingTheta_lt_N24.trans hs) hpole

theorem n24Zeta {s : ℂ}
    (hs : (874957019420098946128604623 / 1000000000000000000000000000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  exact QRH.riemannZeta_ne_zero_of_tightTheta_lt_re
    (QRH.Algebraic.limitingTheta_lt_N24.trans hs)

theorem n24Hecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (874957019420098946128604623 / 1000000000000000000000000000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re χ s
    (QRH.Algebraic.limitingTheta_lt_N24.trans hs) hpole

end QRHPalomar.NativeAudit

#print axioms QRHPalomar.allDirichlet
#print axioms QRHPalomar.zeta
#print axioms QRHPalomar.allHecke
#print axioms QRHPalomar.allDirichletExact
#print axioms QRHPalomar.zetaExact
#print axioms QRHPalomar.allHeckeExact
#print axioms QRHPalomar.existsUniqueRoot
#print axioms QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re
#print axioms QRH.riemannZeta_ne_zero_of_theta_lt_re
#print axioms QRH.Hecke.LFunction_ne_zero_of_theta_lt_re
#print axioms QRH.DirichletCharacter.LFunction_ne_zero_of_tightTheta_lt_re
#print axioms QRH.riemannZeta_ne_zero_of_tightTheta_lt_re
#print axioms QRH.Hecke.LFunction_ne_zero_of_tightTheta_lt_re
#print axioms QRH.riemannZeta_zero_re_le
#print axioms QRH.DirichletCharacter.zero_re_le_or_exception
#print axioms QRH.DirichletCharacter.zero_re_le
#print axioms QRH.Hecke.zero_re_le_or_exception
#print axioms QRH.Hecke.zero_re_le
#print axioms QRH.Algebraic.exists_unique_root
#print axioms QRH.Algebraic.limitingTheta_upper
#print axioms QRH.Algebraic.limitingTheta_lt_N24
#print axioms QRHPalomar.NativeAudit.n24Dirichlet
#print axioms QRHPalomar.NativeAudit.n24Zeta
#print axioms QRHPalomar.NativeAudit.n24Hecke
