import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Dirichlet

/- This file makes the analytic obligations explicit. Its final theorem is
   CONDITIONAL on an actual retuned common-probe construction. It does not
   assert that the algebraic certificate constructs those analytic objects. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight
noncomputable section
open Filter Asymptotics MeasureTheory Set
open scoped Classical Topology
open OAI OAI.SevenEighths
open HeckeFamily HeckeZeroSupremum Continuation

def RetunedPrimitiveContract (s₀ ω ε c : ℝ) : Prop :=
  ∀ η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | s₀ < s.re} ∧
      (∀ s : ℂ, s₀ < s.re → ‖H s - 1‖ ≤ 1/2) ∧
      J =O[atTop] (fun x : ℝ => x^(s₀+c+ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
        (fun x : ℝ => x^(beta+c-ε))

def RetunedUniformCommonProbe (s₀ : ℝ) : Prop :=
  s₀ < beta → ∃ ω ε c : ℝ,
    0 < ω ∧ ω < beta-s₀ ∧ 0 < ε ∧ RetunedPrimitiveContract s₀ ω ε c

theorem hecke_nonzero_of_retuned_probe
    (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ) (s₀ β ω ε c : ℝ)
    (hhalf : 1/2 < s₀) (hold : s₀ ≤ 7/8) (hβ : β ≤ 1)
    (hω0 : 0 < ω) (hω : ω < β-s₀) (hε : 0 < ε)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | s₀ < s.re})
    (hb : ∀ s : ℂ, s₀ < s.re → ‖H s-1‖ ≤ 1/2)
    (hJ : J =O[atTop] (fun x : ℝ => x^(s₀+c+ω)))
    (herr : (fun x => J x-HeckeSignal.signal χ H c x) =O[atTop]
      (fun x : ℝ => x^(β+c-ε)))
    {ρ : ℂ} (hρ : max (s₀+ω) (β-ε) < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ ρ ≠ 0 := by
  let a := max (s₀+ω) (β-ε)
  have haβ : a < β := max_lt (by linarith) (by linarith)
  have ha2 : a < 2 := by linarith
  have ha₀ : s₀ < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have htop : HeckeSignal.signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
    have ht := common_signal_bound J (HeckeSignal.signal χ H c)
      (s₀+c+ω) (β+c-ε) hJ herr
    have he : max (s₀+c+ω) (β+c-ε) = a+c := by
      dsimp [a]
      rw [← max_add_add_right]
      congr 1 <;> ring
    simpa only [he] using ht
  have hH7 : AnalyticOnNhd ℂ H {s : ℂ | 7/8 < s.re} :=
    hH.mono (fun s hs => hold.trans_lt hs)
  have hb7 : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2 :=
    fun s hs => hb s (hold.trans_lt hs)
  have hHd := hH7.differentiableOn
  apply nonzero_of_regularized_signal a 1 c (LFunction χ)
    (HeckeSignal.regularL χ) (HeckeSignal.targetRegularizer χ)
    (gaussianMultiplier H) (HeckeSignal.signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
    (gaussianMultiplier_analytic (hH.mono (fun s hs => ha₀.trans hs)))
    (HeckeSignal.signal_locallyIntegrable χ H hHd hb7 c) htop
    (HeckeSignal.signal_rapidDecayAtZero χ H hHd hb7 c) ?_ hρ ?_
    (HeckeSignal.targetRegularizer_ne_zero χ hpole)
    (gaussianMultiplier_ne_zero (hb ρ (ha₀.trans hρ)))
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
      HeckeSignal.signalMellin_eq_amplitude χ H hHd hb7 c a ha2 htop hs]
    unfold HeckeSignal.amplitude HeckeSignal.quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply HeckeSignal.regularL_eq χ ?_ hpole
    intro h
    rw [h] at hρ
    norm_num at hρ
    linarith

theorem beta_le_of_retuned_contract (s₀ : ℝ)
    (hhalf : 1/2 < s₀) (hold : s₀ ≤ 7/8)
    (h : RetunedUniformCommonProbe s₀) : beta ≤ s₀ := by
  by_contra hn
  obtain ⟨ω, ε, c, hω0, hω, hε, hc⟩ := h (lt_of_not_ge hn)
  let a := max (s₀+ω) (beta-ε)
  have ha : a < beta := max_lt (by linarith) (by linarith)
  have hbase : 1/2 ≤ beta-(beta-a) := by
    have hle := le_max_left (s₀+ω) (beta-ε)
    dsimp [a]
    linarith
  obtain ⟨η, ρ, hp, _, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta (sub_pos.mpr ha) hbase
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hc η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc => hη
        ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hρ : a < ρ.re := by linarith
  have hzχ : LFunction χ ρ = 0 := by
    have hle := le_max_left (s₀+ω) (beta-ε)
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by dsimp [a] at hρ; linarith) hχpole, hz, zero_mul]
  exact (hecke_nonzero_of_retuned_probe χ H J s₀ beta ω ε c hhalf hold
    beta_le_one hω0 hω hε hH hb hJ herr hρ hχpole) hzχ

theorem rational_hecke_nonzero_of_contract
    (h : RetunedUniformCommonProbe sigmaRat) (χ : Character) (s : ℂ)
    (hs : sigmaRat < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  have hb := beta_le_of_retuned_contract sigmaRat
    (by norm_num [sigmaRat]) (by norm_num [sigmaRat]) h
  exact LFunction_ne_zero_of_beta_lt χ (hb.trans_lt hs) hpole

theorem rational_dirichlet_nonzero_of_contract
    (h : RetunedUniformCommonProbe sigmaRat) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : sigmaRat < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hpole) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; norm_num [h, sigmaRat] at hs
  have hn := rational_hecke_nonzero_of_contract h (HeckeDirichlet.character χ)
    s hs (Or.inl hs1)
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at hn
  exact (mul_ne_zero_iff.mp hn).1

theorem rational_zeta_nonzero_of_contract
    (h : RetunedUniformCommonProbe sigmaRat) (s : ℂ) (hs : sigmaRat < s.re) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have hn := rational_dirichlet_nonzero_of_contract h (1 : DirichletCharacter ℂ 1)
    s hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hn

#print axioms rational_dirichlet_nonzero_of_contract
#print axioms rational_zeta_nonzero_of_contract
end
end BelowSevenEighthsTight
