/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SphericalL2ResolventFormula.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Analysis.SpectralTheory.Resolvents.BelowThresholdMeromorphy
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSphericalL2Formula

open MeasureTheory Filter Topology

def ClearedHilbertGerm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (v : ℂ → H) (Ω : Set ℂ) (s₀ : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.ball s₀ r ⊆ Ω ∧
    ∃ w : ℂ → H, DifferentiableOn ℂ w (Metric.ball s₀ r) ∧
      ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • v s

section Formula
variable {X A H S : Type*} [MeasurableSpace X] [Fintype A]
    [AddCommGroup H] [Module ℂ H] [AddCommGroup S] [Module ℂ S]

end Formula

def ClearedSmoothGerm {X I : Type*}
    (n : I → ℕ) (balls : ∀ i, KPContLocalNorm.LocalBall (n i))
    (pullback : ∀ i, (X → ℂ) →ₗ[ℂ] (KPContLocalNorm.Space (n i) → ℂ))
    (automorphic : Submodule ℂ (X → ℂ))
    (E : ℂ → X → ℂ) (Ω : Set ℂ) (s₀ : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.ball s₀ r ⊆ Ω ∧
    ∃ w : ℂ → X → ℂ,
      (∀ s ∈ Metric.ball s₀ r, w s ∈ automorphic) ∧
      (∀ i, KPCutoffSource.ChartSmoothHolomorphicOn (balls i)
        (fun s => pullback i (w s)) (Metric.ball s₀ r)) ∧
      ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • E s

end DedekindZetaZeroFree.KPSphericalL2Formula

end
