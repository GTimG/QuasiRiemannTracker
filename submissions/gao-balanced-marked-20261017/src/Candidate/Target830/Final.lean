/- The unconditional .874830 nonvanishing region.
Predecessor OpenAI, Hailey Collet, DaysSky and Zhongpai Gao attribution is
retained. Apache-2.0. -/
import Candidate.Target830.Source.RecordEndpoint

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Final
noncomputable section
open scoped _root_.DirichletCharacter

/-- The actual source theorem bounds the supremum for every finite-order
Hecke character; the only exceptional pair is the principal pole. -/
theorem hecke_nonzero (χ : HeckeFamily.Character) (s : ℂ)
    (hs : (87483/100000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    (Source.RecordEndpoint.beta_le_rational.trans_lt hs) hpole

/-- Canonical all-Dirichlet region, including imprimitive characters. -/
theorem allDirichlet {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (87483/100000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Cycle25.dirichlet_of_hecke (by norm_num) hecke_nonzero χ s hs hpole

theorem allHecke (χ : HeckeFamily.Character) {s : ℂ}
    (hs : (87483/100000 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    HeckeFamily.LFunction χ s ≠ 0 := by
  exact hecke_nonzero χ s hs (by tauto)

/-- Mathlib's total zeta convention also assigns a nonzero value at 1. -/
theorem zeta_total {s : ℂ} (hs : (87483/100000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 :=
  Cycle25.zeta_of_hecke (by norm_num) hecke_nonzero s hs

/-- The conventional statement explicitly excludes the pole. -/
theorem zeta {s : ℂ} (hs : (87483/100000 : ℝ) < s.re) (_hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := zeta_total hs

end
end OAI.SevenEighths.Target830.Final
#print axioms OAI.SevenEighths.Target830.Final.allDirichlet
#print axioms OAI.SevenEighths.Target830.Final.allHecke
#print axioms OAI.SevenEighths.Target830.Final.zeta
