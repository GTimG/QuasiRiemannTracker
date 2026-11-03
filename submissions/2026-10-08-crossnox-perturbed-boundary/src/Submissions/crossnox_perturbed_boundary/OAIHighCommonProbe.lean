/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighCommonProbe.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighSignalIdentity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.CommonProbe

namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Classical
namespace SevenEighths.HeckeCommonProbe
open HeckeFamily HeckeZeroSupremum
open HeckeSignal

def PerturbedPrimitiveContract (ω σ : ℝ) : Prop :=
  ∀ η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | perturbedBoundary < s.re} ∧
      (∀ s : ℂ, perturbedBoundary < s.re → ‖H s - 1‖ ≤ 1 / 2) ∧
      J =O[atTop] (fun x : ℝ => x ^ (perturbedBoundary + AsymmetricGeometry.signalOffset + ω)) ∧
      (fun x => J x - signal χ H (AsymmetricGeometry.signalOffset) x) =O[atTop]
        (fun x : ℝ => x ^ (beta + AsymmetricGeometry.signalOffset - σ))

def UniformPerturbedCommonProbe : Prop :=
  perturbedBoundary < beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < beta - perturbedBoundary ∧
      0 < σ ∧ PerturbedPrimitiveContract ω σ

theorem beta_le_perturbed_boundary (h : UniformPerturbedCommonProbe) :
    beta ≤ perturbedBoundary := by
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := h (lt_of_not_ge hn)
  have hmargin := perturbedContinuationMargin_pos hω hσ
  have hboundary :=
    perturbed_continuation_boundary_gt (β := beta) (σ := σ) hω0
  have hhalf : (1 / 2 : ℝ) ≤
      beta - perturbedContinuationMargin beta ω σ := by
    dsimp [perturbedBoundary, AsymmetricGeometry.boundary] at hboundary
    linarith
  obtain ⟨η, ρ, hp, _, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin hhalf
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc =>
        hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith [hboundary, hnear]) hχpole, hz, zero_mul]
  apply (nonzero_of_perturbed_probe_bounds χ H J beta ω σ (AsymmetricGeometry.signalOffset)
    beta_le_one hω0 hω hσ hH hb ?_ ?_ hnear hχpole) hzχ
  · exact hJ
  · exact herr

theorem hecke_ne_zero_of_perturbed_common_probe
    (h : UniformPerturbedCommonProbe) (χ : Character) (s : ℂ)
    (hs : perturbedBoundary < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_beta_lt χ
    ((beta_le_perturbed_boundary h).trans_lt hs) hpole

end SevenEighths.HeckeCommonProbe

end

end OAI
