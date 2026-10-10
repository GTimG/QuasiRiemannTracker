import Cycle25.Assembly.Final.CommonProbe

/-! Unconditional Cycle25 nonvanishing for the exact quartic boundary and
its rational catalogue rounding. The common probe is constructed from the
actual low, high, count and physical numerator estimates. Apache-2.0 attribution:
OpenAI/math family003 and weighted upstream PR6,
revision 2fd60c0926b66ea18d7436f5ed55250fd006ab5d. -/
namespace Cycle25
open OAI.SevenEighths

theorem beta_le_theta : HeckeZeroSupremum.beta ≤ theta :=
  beta_le_of_common_probe theta_gt_half.le theta_lt_seven_eighths.le
    Cycle25WeightedHighFinalAssembly.actual_common_probe

theorem hecke_nonzero (χ : HeckeFamily.Character) (s : ℂ)
    (hs : theta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (beta_le_theta.trans_lt hs) hpole

theorem dirichlet_nonzero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : theta < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 :=
  dirichlet_of_hecke theta_pos hecke_nonzero χ s hs hexc

theorem zeta_nonzero (s : ℂ) (hs : theta < s.re) : riemannZeta s ≠ 0 :=
  zeta_of_hecke theta_pos hecke_nonzero s hs

theorem beta_le_catalogue : HeckeZeroSupremum.beta ≤ Arithmetic.theta :=
  beta_le_theta.trans Arithmetic.b0_lt_theta.le

theorem hecke_nonzero_catalogue (χ : HeckeFamily.Character) (s : ℂ)
    (hs : Arithmetic.theta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (beta_le_catalogue.trans_lt hs) hpole

theorem dirichlet_nonzero_catalogue {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : Arithmetic.theta < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 :=
  dirichlet_of_hecke (theta_pos.trans Arithmetic.b0_lt_theta)
    hecke_nonzero_catalogue χ s hs hexc

theorem zeta_nonzero_catalogue (s : ℂ) (hs : Arithmetic.theta < s.re) :
    riemannZeta s ≠ 0 :=
  zeta_of_hecke (theta_pos.trans Arithmetic.b0_lt_theta) hecke_nonzero_catalogue s hs
end Cycle25
