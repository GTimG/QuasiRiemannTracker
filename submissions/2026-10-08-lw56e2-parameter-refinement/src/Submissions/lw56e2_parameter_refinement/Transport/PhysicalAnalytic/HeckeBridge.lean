/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalAnalytic/HeckeBridge.lean
Original SHA-256: 70f5cb9eaeca721bfbbd56df05fa6168b921dfa871909b4a536ff43b823c0d54
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.Continuation
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalAnalytic.FamilyTransfer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum

/-!
# The actual Hecke signal at a transported boundary

The signal, L-function, primitive characters, finite deletion, and zero
supremum are the actual objects in the pinned OpenAI source. Only the boundary
and the signal shift are parameterized here. The uniform physical probe
contract is an explicit hypothesis, not an axiom or an asserted estimate.

The upper restriction B ≤ 7/8 lets us reuse the source's signal regularity
lemmas by restricting an analytic correction on Re(s)>B to Re(s)>7/8.
It does not assume that the correction extends there: the extension remains
part of the contract, as do the common probe bounds.
-/

namespace LW56e2.Transport.PhysicalAnalytic

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Classical
open OAI.SevenEighths
open HeckeFamily HeckeZeroSupremum Continuation

/-- Actual Hecke nonvanishing from bounds for one common probe. -/
theorem hecke_nonzero_of_probe_bounds
    (B β ω σ c : ℝ) (hB0 : 0 < B) (hB8 : B ≤ 7 / 8)
    (hβ : β ≤ 1) (hω0 : 0 < ω) (hω : ω < β - B) (hσ : 0 < σ)
    (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | B < s.re})
    (hb : ∀ s : ℂ, B < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (B + c + ω)))
    (herror : (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    {ρ : ℂ} (hρ : continuationBoundary B β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ ρ ≠ 0 := by
  let a := continuationBoundary B β ω σ
  have ha2 : a < 2 := by
    have hh := boundary_lt_supremum hω hσ
    dsimp [a]
    linarith
  have hH8 : AnalyticOnNhd ℂ H {s : ℂ | (7 / 8 : ℝ) < s.re} :=
    hH.mono (fun _ hs => hB8.trans_lt hs)
  have hb8 : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ) :=
    fun s hs => hb s (hB8.trans_lt hs)
  have hHd := hH8.differentiableOn
  have htop : HeckeSignal.signal χ H c =O[atTop]
      (fun x : ℝ => x ^ (a + c)) :=
    common_signal_bound_at_boundary J (HeckeSignal.signal χ H c) B β ω σ c hJ herror
  apply LW56e2.Transport.nonzero_of_common_probe B β ω σ c hω0
    (LFunction χ) (HeckeSignal.regularL χ) (HeckeSignal.targetRegularizer χ)
    H J (HeckeSignal.signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
    hH hb (HeckeSignal.signal_locallyIntegrable χ H hHd hb8 c)
    (HeckeSignal.signal_rapidDecayAtZero χ H hHd hb8 c)
    hJ herror _ hρ _ (HeckeSignal.targetRegularizer_ne_zero χ hpole)
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
      HeckeSignal.signalMellin_eq_amplitude χ H hHd hb8 c a ha2 htop hs]
    unfold HeckeSignal.amplitude HeckeSignal.quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply HeckeSignal.regularL_eq χ _ hpole
    intro hh
    have hbase := base_lt_boundary (B := B) (β := β) (σ := σ) hω0
    rw [hh] at hρ
    norm_num at hρ
    linarith

/-- Uniformity is over primitive actual Hecke characters; deletion is literal
equality of their ideal coefficients. The same J occurs in both estimates. -/
def PrimitiveProbeContract (B c ω σ : ℝ) : Prop :=
  ∀ η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | B < s.re} ∧
      (∀ s : ℂ, B < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ)) ∧
      J =O[atTop] (fun x : ℝ => x ^ (B + c + ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
        (fun x : ℝ => x ^ (beta + c - σ))

def UniformCommonProbe (B c : ℝ) : Prop :=
  B < beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < beta - B ∧ 0 < σ ∧ PrimitiveProbeContract B c ω σ

/-- The ordinary primitive-supremum contradiction at an arbitrary improved
boundary. The hypotheses include the actual uniform probe contract. -/
theorem hecke_beta_le_boundary {B c : ℝ}
    (hB : (1 / 2 : ℝ) < B) (hB8 : B ≤ 7 / 8)
    (h : UniformCommonProbe B c) : beta ≤ B := by
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := h (lt_of_not_ge hn)
  have hmargin := continuationMargin_pos hω hσ
  have hboundary := base_lt_boundary (B := B) (β := beta) (σ := σ) hω0
  have hsmall : (1 / 2 : ℝ) ≤ beta - continuationMargin B beta ω σ := by
    rw [← continuationBoundary_eq_sub_margin]
    exact (hB.trans hboundary).le
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin hsmall
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc =>
        hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith) hχpole, hz, zero_mul]
  apply (hecke_nonzero_of_probe_bounds B beta ω σ c (by linarith) hB8
    beta_le_one hω0 hω hσ χ H J hH hb hJ herr ?_ hχpole) hzχ
  simpa only [continuationBoundary_eq_sub_margin] using hnear

theorem hecke_of_common_probe {B c : ℝ}
    (hB : (1 / 2 : ℝ) < B) (hB8 : B ≤ 7 / 8)
    (h : UniformCommonProbe B c)
    (χ : Character) (s : ℂ) (hs : B < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_beta_lt χ
    ((hecke_beta_le_boundary hB hB8 h).trans_lt hs) hpole

theorem dirichlet_of_common_probe {B c : ℝ}
    (hB : (1 / 2 : ℝ) < B) (hB8 : B ≤ 7 / 8)
    (h : UniformCommonProbe B c) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : B < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 :=
  dirichlet_of_hecke_at_boundary (by linarith)
    (hecke_of_common_probe hB hB8 h) χ s hs hexc

theorem zeta_of_common_probe {B c : ℝ}
    (hB : (1 / 2 : ℝ) < B) (hB8 : B ≤ 7 / 8)
    (h : UniformCommonProbe B c) (s : ℂ) (hs : B < s.re) :
    riemannZeta s ≠ 0 :=
  zeta_of_hecke_at_boundary (by linarith)
    (hecke_of_common_probe hB hB8 h) s hs

end
end LW56e2.Transport.PhysicalAnalytic
