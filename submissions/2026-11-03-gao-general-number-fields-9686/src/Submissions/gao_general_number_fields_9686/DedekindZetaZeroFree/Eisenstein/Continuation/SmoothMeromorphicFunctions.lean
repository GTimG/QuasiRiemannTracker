/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SmoothMeromorphicFunctions.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.SpectralTheory.SpectralCoordinateAndPoleOrders

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneContinuation
open MeasureTheory KPGlobalEisensteinData
open scoped Topology

variable {G H J : Type*} [TopologicalSpace G] [AddCommGroup H] [Module ℂ H]

def SmoothMeromorphicOn (D : J → H →ₗ[ℂ] C(G, ℂ))
    (f : ℂ → H) (O : Set ℂ) : Prop :=
  ∀ z₀ ∈ O, ∃ (ρ : ℝ) (m : ℕ) (a : ℕ → H) (cleared : ℂ → H),
    0 < ρ ∧ Metric.ball z₀ ρ ⊆ O ∧
    SmoothPowerSeriesOn D z₀ ρ a cleared ∧
    ∀ z ∈ Metric.ball z₀ ρ, z ≠ z₀ → cleared z = (z - z₀) ^ m • f z

end DedekindZetaZeroFree.KPRankOneContinuation

end
