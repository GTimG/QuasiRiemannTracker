import OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
import OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum
import OAI.NumberTheory.DirichletL.Hecke.Dirichlet

/-!
The continuation and actual L-function transfer for a variable boundary.
These are infrastructure lemmas: their probe hypotheses must be discharged
by the physical estimates before they yield a new zero-free theorem.
-/

noncomputable section
open Filter Asymptotics
open scoped Classical
open OAI.SevenEighths

namespace WeightedQRH

def continuationMargin (θ β ω σ : ℝ) : ℝ := min (β - θ - ω) σ

theorem continuationMargin_pos {θ β ω σ : ℝ}
    (hω : ω < β - θ) (hσ : 0 < σ) :
    0 < continuationMargin θ β ω σ :=
  lt_min (sub_pos.mpr hω) hσ

theorem continuation_boundary_gt {θ β ω σ : ℝ} (hω : 0 < ω) :
    θ < β - continuationMargin θ β ω σ := by
  have h : continuationMargin θ β ω σ ≤ β - θ - ω := min_le_left _ _
  linarith

theorem max_signal_exponents (θ β ω σ c : ℝ) :
    max (θ + c + ω) (β + c - σ) =
      (β - continuationMargin θ β ω σ) + c := by
  unfold continuationMargin
  rcases le_total (β - θ - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

theorem nonzero_of_probe_bounds (χ : HeckeFamily.Character)
    (H : ℂ → ℂ) (J : ℝ → ℂ) (θ β ω σ c : ℝ)
    (hθ0 : 0 < θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (hβ : β ≤ 1) (hω0 : 0 < ω) (hω : ω < β - θ) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | θ < s.re})
    (hb : ∀ s : ℂ, θ < s.re → ‖H s - 1‖ ≤ 1/2)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (θ+c+ω)))
    (herror : (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
      (fun x : ℝ => x ^ (β+c-σ)))
    {ρ : ℂ} (hρ : β - continuationMargin θ β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : HeckeFamily.LFunction χ ρ ≠ 0 := by
  let a := β - continuationMargin θ β ω σ
  have hθa : θ < a := continuation_boundary_gt hω0
  have ha2 : a < 2 := by
    have hp := continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have hH7 : AnalyticOnNhd ℂ H {s : ℂ | (7/8 : ℝ) < s.re} :=
    hH.mono (fun _ hs => hθ7.trans_lt hs)
  have hb7 : ∀ s : ℂ, (7/8 : ℝ) < s.re → ‖H s - 1‖ ≤ 1/2 :=
    fun s hs => hb s (hθ7.trans_lt hs)
  have htop : HeckeSignal.signal χ H c =O[atTop]
      (fun x : ℝ => x ^ (a+c)) := by
    simpa only [max_signal_exponents, a] using
      Continuation.common_signal_bound J (HeckeSignal.signal χ H c)
        (θ+c+ω) (β+c-σ) hJ herror
  have hHa : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH.mono (fun _ hs => hθa.trans hs)
  apply Continuation.nonzero_of_regularized_signal a 1 c
    (HeckeFamily.LFunction χ) (HeckeSignal.regularL χ)
    (HeckeSignal.targetRegularizer χ) (Continuation.gaussianMultiplier H)
    (HeckeSignal.signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
    (Continuation.gaussianMultiplier_analytic hHa)
    (HeckeSignal.signal_locallyIntegrable χ H hH7.differentiableOn hb7 c)
    htop (HeckeSignal.signal_rapidDecayAtZero χ H hH7.differentiableOn hb7 c)
    ?_ hρ ?_ (HeckeSignal.targetRegularizer_ne_zero χ hpole)
    (Continuation.gaussianMultiplier_ne_zero (hb ρ (hθa.trans hρ)))
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
      HeckeSignal.signalMellin_eq_amplitude χ H hH7.differentiableOn hb7
        c a ha2 htop hs]
    unfold HeckeSignal.amplitude HeckeSignal.quotient Continuation.gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := HeckeFamily.LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply HeckeSignal.regularL_eq χ _ hpole
    intro h
    rw [h] at hρ
    norm_num at hρ
    linarith

def PrimitiveProbeContract (θ c ω σ : ℝ) : Prop :=
  ∀ η : HeckeFamily.Character,
    FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : HeckeFamily.Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, HeckeFamily.idealCoeff χ I =
        if IsCoprime I χ.modulus then HeckeFamily.idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | θ < s.re} ∧
      (∀ s : ℂ, θ < s.re → ‖H s - 1‖ ≤ 1/2) ∧
      J =O[atTop] (fun x : ℝ => x ^ (θ+c+ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
        (fun x : ℝ => x ^ (HeckeZeroSupremum.beta+c-σ))

def UniformCommonProbe (θ c : ℝ) : Prop :=
  θ < HeckeZeroSupremum.beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < HeckeZeroSupremum.beta - θ ∧ 0 < σ ∧
      PrimitiveProbeContract θ c ω σ

theorem beta_le_of_common_probe {θ c : ℝ}
    (hθ : (1/2 : ℝ) ≤ θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (h : UniformCommonProbe θ c) : HeckeZeroSupremum.beta ≤ θ := by
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := h (lt_of_not_ge hn)
  have hmargin := continuationMargin_pos hω hσ
  have hboundary := continuation_boundary_gt
    (θ := θ) (β := HeckeZeroSupremum.beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc => hη
        ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : HeckeFamily.LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith) hχpole, hz, zero_mul]
  exact (nonzero_of_probe_bounds χ H J θ HeckeZeroSupremum.beta ω σ c
    (by linarith) hθ7 HeckeZeroSupremum.beta_le_one hω0 hω hσ
    hH hb hJ herr hnear hχpole) hzχ

theorem hecke_ne_zero_of_common_probe {θ c : ℝ}
    (hθ : (1/2 : ℝ) ≤ θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (h : UniformCommonProbe θ c) (χ : HeckeFamily.Character) (s : ℂ)
    (hs : θ < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_of_common_probe hθ hθ7 h).trans_lt hs) hpole

theorem dirichlet_of_hecke {θ : ℝ} (hθ : 0 < θ)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), θ < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : θ < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  have h := hH (HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_of_hecke {θ : ℝ} (hθ : 0 < θ)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), θ < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    (s : ℂ) (hs : θ < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_of_hecke hθ hH (1 : DirichletCharacter ℂ 1) s hs
    (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end WeightedQRH
