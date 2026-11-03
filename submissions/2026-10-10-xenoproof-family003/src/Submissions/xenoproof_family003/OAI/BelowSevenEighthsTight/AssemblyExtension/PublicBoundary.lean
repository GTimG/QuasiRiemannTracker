import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.AssemblyExtension.RationalNonvanishing

/- Public numeric statements. The hypotheses contain no probe, moment,
   capacity, or analytic-contract assumptions. See receipts for check status. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.PublicResults
noncomputable section

theorem rational_boundary_lt_frozen_baseline :
    (8749570194201 / 10000000000000 : ℝ) < 43747851 / 50000000 := by norm_num

theorem rational_boundary_lt_seven_eighths :
    (8749570194201 / 10000000000000 : ℝ) < 7 / 8 := by norm_num

theorem riemannZeta_ne_zero_of_rational_lt_re (s : ℂ)
    (hs : (8749570194201 / 10000000000000 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  exact Results.zeta_nonvanishing s hs

theorem dirichlet_LFunction_ne_zero_of_rational_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (8749570194201 / 10000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Results.dirichlet_nonvanishing χ s hs hpole

theorem hecke_LFunction_ne_zero_of_rational_lt_re
    (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (8749570194201 / 10000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  apply Results.hecke_nonvanishing χ s hs
  rcases not_and_or.mp hpole with hχ | hs
  · exact Or.inr hχ
  · exact Or.inl hs

#print axioms rational_boundary_lt_frozen_baseline
#print axioms rational_boundary_lt_seven_eighths
#print axioms riemannZeta_ne_zero_of_rational_lt_re
#print axioms dirichlet_LFunction_ne_zero_of_rational_lt_re
#print axioms hecke_LFunction_ne_zero_of_rational_lt_re
end
end BelowSevenEighthsTight.PublicResults
