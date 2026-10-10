import WeightedQRH.NumeratorActualSource
import WeightedQRH.HighRows.WeightedSourceRawCells

/-! Unconditional endpoints at theta = 10499/12000.

The raw full-w source estimate `actual_raw_fullW_input` discharges the only analytic
input of the conditional assembly in `HighRows/ConditionalFinal.lean`. -/
noncomputable section
namespace WeightedQRH
open OAI.SevenEighths OAI.SevenEighths.WeightedHighFinalAssembly

/-- The literal weighted full-w cell estimates hold at the chosen geometry. -/
theorem fullW_analytic_input : FullWAnalyticInput :=
  fullW_input_of_raw_source Numerator.actual_raw_fullW_input

/-- The supremum of real parts of zeros of the residue Hecke L-functions over
`Q(ζ₃)` is at most `10499/12000`. -/
theorem beta_le_theta : HeckeZeroSupremum.beta ≤ (10499/12000:ℝ) :=
  beta_le_theta_of_fullW_input fullW_analytic_input

/-- Every residue Hecke L-function over `Q(ζ₃)` is nonzero on `Re s > 10499/12000`,
away from the pole of the trivial character at `s = 1`. -/
theorem hecke_nonzero (χ : HeckeFamily.Character) (s : ℂ)
    (hs : (10499/12000:ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  hecke_of_fullW_input fullW_analytic_input χ s hs hpole

/-- Every Dirichlet L-function, of every positive modulus, is nonzero on
`Re s > 10499/12000`, away from the pole of the trivial character at `s = 1`. -/
theorem dirichlet_nonzero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (10499/12000:ℝ) < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 :=
  dirichlet_of_fullW_input fullW_analytic_input χ s hs hpole

/-- The Riemann zeta function is analytic and nonzero on `Re s > 10499/12000`, `s ≠ 1`. -/
theorem zeta_nonzero (s : ℂ) (hs : (10499/12000:ℝ) < s.re) (h1 : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s ∧ riemannZeta s ≠ 0 :=
  ⟨analyticOn_riemannZeta s h1,zeta_of_fullW_input fullW_analytic_input s hs⟩

end WeightedQRH
end
