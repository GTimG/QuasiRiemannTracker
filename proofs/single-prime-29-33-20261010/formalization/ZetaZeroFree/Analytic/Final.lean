import ZetaZeroFree.Analytic.Probe.Band
import ZetaZeroFree.Analytic.Moments.AppendixD3
import ZetaZeroFree.Analytic.Energy.GaussianSource
import ZetaZeroFree.Analytic.Continuation
import OAI.NumberTheory.DirichletL.Hecke.Dirichlet

/-!
The unconditional closing step for the new one-prime analytic argument.
The actual physical probe, central band, residue comparison and transport
estimates are constructed before applying continuation. The common saving
is fixed before choosing the target character. No earlier terminal
nonvanishing theorem is used.
-/

namespace ZetaZeroFree.Analytic
noncomputable section
open Filter Asymptotics
open OAI.SevenEighths
open HeckeFamily CommonParameters PrincipalSignalComparison

private theorem isBigO_of_eventual_power_bound (f : ℝ → ℂ) (p C : ℝ)
    (hbound : ∀ᶠ Z : ℝ in atTop, ‖f Z‖ ≤ C * Z ^ p) :
    f =O[atTop] (fun Z : ℝ => Z ^ p) := by
  apply IsBigO.of_bound C
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with Z hZ hpos
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos p)] using hZ

/-- The estimates required by continuation are consequences of the actual
source construction, with the same positive saving for every character. -/
theorem common_deleted_probe_estimates
    (hbeta : Exponent.b < HeckeZeroSupremum.beta) :
    ∃ ε σ : ℝ, 0 < ε ∧ ε < HeckeZeroSupremum.beta - Exponent.b ∧ 0 < σ ∧
      ∀ χ : Character, FiniteFourier.IsPrimitiveOnIdeals χ.residue →
        Nonempty (DeletedProbeEstimates χ HeckeZeroSupremum.beta ε σ) := by
  let beta := HeckeZeroSupremum.beta
  let u := smallLoss beta
  let sigma := saving beta
  let e := contourE beta
  have hu : 0 < u := smallLoss_pos hbeta
  have hsigma : 0 < sigma := saving_pos hbeta
  rcases fixed_guards hbeta with
    ⟨he, he1, _har, _hw, _hwcap, hucap, _hgeom, _hcount, _hbudget, _hgap,
      hsmall, hprincipal, hwindow, _hepsBudget⟩
  obtain ⟨F⟩ := exists_source_data e he
  obtain ⟨tau, htau, hband⟩ := Probe.source_data_central_band_bound hbeta F
  have hbetaOld : (7 / 8 : ℝ) ≤ beta :=
    (Exponent.original_boundary_comparison.trans hbeta).le
  have hlarge : sigma + u ≤ (1 : ℝ) + 157 / 792 := by
    linarith only [hprincipal]
  have hp : (20 / 99 : ℝ) + 11 * u + u ≤ beta - 67 / 99 - sigma := by
    have hslack := central_slack hbeta
    norm_num [Exponent.b] at hslack
    dsimp [u, sigma, beta] at hu hsigma ⊢
    linarith only [hslack, hu, hsigma]
  have herror := Probe.source_data_error_from_band F (1 / 4) u 1 tau u sigma
    ((20 / 99 : ℝ) + 11 * u) he he1 (by norm_num) (by norm_num)
    hu hucap htau hu hsigma hbetaOld hsmall hprincipal
    (by norm_num; exact hwindow) hlarge hp hband
  rcases physical_slack hbeta with ⟨hepsilon, hepsilonGap⟩
  refine ⟨(beta - Exponent.b) / 4, sigma, hepsilon, hepsilonGap, hsigma, ?_⟩
  intro chi _hprimitive
  obtain ⟨Cphysical, _hCphysical, hphysical⟩ :=
    Energy.source_probe_bound F chi ((beta - Exponent.b) / 4) hepsilon
  obtain ⟨Cerror, _hCerror, herror⟩ := herror chi
  have hk : Exponent.k = (67 / 99 : ℝ) := by
    norm_num [Exponent.k, Exponent.x, Exponent.ell]
  refine ⟨⟨F.S, F.exclusions.prime,
    ⟨sourceCorrection chi F.S, F.probe chi, F.correction_analytic chi,
      F.correction_bound chi, ?_, ?_⟩⟩⟩
  · rw [Exponent.physical_exponent]
    exact isBigO_of_eventual_power_bound _ _ Cphysical
      (hphysical.mono (fun _ hz => hz.2.2))
  · simpa only [hk, neg_div] using isBigO_of_eventual_power_bound _ _ Cerror
      (herror.mono (fun _ hz => hz.2))

/-- The manuscript's new analytic estimates imply the unconditional bound. -/
theorem beta_le_twenty_nine_thirty_thirds :
    HeckeZeroSupremum.beta ≤ Exponent.b :=
  beta_le_of_common_deleted_probe common_deleted_probe_estimates

theorem heckeL_ne_zero_of_twenty_nine_thirty_thirds_lt_re
    (chi : Character) {s : ℂ} (hs : (29 / 33 : ℝ) < s.re)
    (hpole : ¬ (chi.residue = 1 ∧ s = 1)) : LFunction chi s ≠ 0 := by
  apply HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt chi
  · exact beta_le_twenty_nine_thirty_thirds.trans_lt hs
  · simpa only [not_and_or, or_comm] using hpole

theorem dirichletL_ne_zero_of_twenty_nine_thirty_thirds_lt_re
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction chi s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact chi.LFunction_ne_zero_of_one_le_re (not_and_or.mp hpole) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hn := heckeL_ne_zero_of_twenty_nine_thirty_thirds_lt_re
    (HeckeDirichlet.character chi) hs (by simp [hs1])
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product chi hs0 hs1] at hn
  exact (mul_ne_zero_iff.mp hn).1

theorem riemannZeta_ne_zero_of_twenty_nine_thirty_thirds_lt_re
    {s : ℂ} (hs : (29 / 33 : ℝ) < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  have hn := dirichletL_ne_zero_of_twenty_nine_thirty_thirds_lt_re
    (1 : DirichletCharacter ℂ 1) hs (by simp [hpole])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hn

theorem heckeL_deleted_ne_zero
    (chi : Character) (S : Finset (Ideal HeckeFamily.O))
    (hS : ∀ P ∈ S, Prime P) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re) (hpole : ¬ (chi.residue = 1 ∧ s = 1)) :
    LFunction (chi.excludePrimes S hS) s ≠ 0 := by
  apply heckeL_ne_zero_of_twenty_nine_thirty_thirds_lt_re _ hs
  rintro ⟨hprincipal, hsone⟩
  have hmask := excludePrimes_mask chi S hS
  exact hpole ⟨(HeckeFiniteDeletion.principal_iff_of_mask _ _ hmask).mp hprincipal, hsone⟩

end
end ZetaZeroFree.Analytic
