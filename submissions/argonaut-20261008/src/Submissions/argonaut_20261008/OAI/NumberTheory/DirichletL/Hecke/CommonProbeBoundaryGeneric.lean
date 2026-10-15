import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Hecke.SignalIdentityBoundaryGeneric
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Dirichlet

namespace OAI

noncomputable section

open Filter Asymptotics
open scoped Classical

namespace SevenEighths.HeckeCommonProbe

open HeckeFamily HeckeZeroSupremum

def PrimitiveContractBoundary (b0 ω σ : ℝ) : Prop :=
  ∀ η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | b0 < s.re} ∧
      (∀ s : ℂ, b0 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ)) ∧
      J =O[atTop] (fun x : ℝ => x ^ (b0 - 11 / 16 + ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H (-11 / 16) x) =O[atTop]
        (fun x : ℝ => x ^ (beta - 11 / 16 - σ))

/--
This is only the common-probe interface at `b0`.  It does not construct the
contract; that construction is deliberately left to the separate analytic chain.
-/
def UniformCommonProbeBoundary (b0 : ℝ) : Prop :=
  (1 / 2 : ℝ) < b0 ∧ b0 ≤ 7 / 8 ∧
    (b0 < beta → ∃ ω σ : ℝ,
      0 < ω ∧ ω < beta - b0 ∧ 0 < σ ∧
        PrimitiveContractBoundary b0 ω σ)

theorem beta_le_b0_of_uniform_common_probe {b0 : ℝ}
    (h : UniformCommonProbeBoundary b0) : beta ≤ b0 := by
  unfold UniformCommonProbeBoundary at h
  rcases h with ⟨hb0half, hb0seven, hprobe⟩
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := hprobe (lt_of_not_ge hn)
  have hmargin := Supremum.continuationMarginBoundary_pos hω hσ
  have hboundary := Supremum.continuation_boundary_gt_b0
    (b0 := b0) (β := beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc =>
        hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith) hχpole, hz, zero_mul]
  apply (HeckeSignal.nonzero_of_probe_bounds_boundary χ H J
    b0 beta ω σ (-11 / 16) hb0half hb0seven beta_le_one
    hω0 hω hσ hH hb ?_ ?_ hnear hχpole) hzχ
  · convert hJ using 1
    ring_nf
  · convert herr using 1
    ring_nf

theorem hecke_ne_zero_of_common_probe_boundary {b0 : ℝ}
    (h : UniformCommonProbeBoundary b0)
    (χ : Character) (s : ℂ) (hs : b0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  exact LFunction_ne_zero_of_beta_lt χ
    ((beta_le_b0_of_uniform_common_probe h).trans_lt hs) hpole

theorem beta_le_targetBoundary_of_uniform_common_probe
    (h : UniformCommonProbeBoundary Supremum.targetBoundary) :
    beta ≤ Supremum.targetBoundary :=
  beta_le_b0_of_uniform_common_probe h

theorem hecke_ne_zero_of_target_common_probe
    (h : UniformCommonProbeBoundary Supremum.targetBoundary)
    (χ : Character) (s : ℂ) (hs : Supremum.targetBoundary < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 :=
  hecke_ne_zero_of_common_probe_boundary h χ s hs hpole

end SevenEighths.HeckeCommonProbe

end

end OAI