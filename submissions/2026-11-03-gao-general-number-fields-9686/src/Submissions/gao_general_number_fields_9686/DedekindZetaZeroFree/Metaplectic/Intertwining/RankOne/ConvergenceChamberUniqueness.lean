/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/ConvergenceChamberUniqueness.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.StandardIntegralAndLevelContinuation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Analysis.MeromorphicGermUniqueness

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneChamberUniqueness
open scoped Topology
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation

theorem convergence_chamber_open (ε : Sign) :
    IsOpen {s : ℂ | convergenceHalfPlane ε s} := by
  cases ε with
  | plus =>
    change IsOpen {s : ℂ | -(1 / 6 : ℝ) < s.re}
    exact isOpen_lt continuous_const Complex.continuous_re
  | minus =>
    change IsOpen {s : ℂ | s.re < -(1 / 6 : ℝ)}
    exact isOpen_lt Complex.continuous_re continuous_const

theorem convergence_chamber_nonempty (ε : Sign) :
    {s : ℂ | convergenceHalfPlane ε s}.Nonempty := by
  cases ε with
  | plus => exact ⟨0, by norm_num [convergenceHalfPlane]⟩
  | minus => exact ⟨-1, by norm_num [convergenceHalfPlane]⟩

theorem chamber_identity_germ (ε : Sign) {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g)
    (he : ∀ s, convergenceHalfPlane ε s → f s = g s) (s₀ : ℂ) :
    f =ᶠ[𝓝[≠] s₀] g := by
  apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
    (O := Set.univ) (V := {s : ℂ | convergenceHalfPlane ε s})
    (fun s _ => hf s) (fun s _ => hg s) isPreconnected_univ
    (convergence_chamber_open ε) (Set.subset_univ _) (convergence_chamber_nonempty ε)
    (fun s hs => he s hs) (Set.mem_univ s₀)

theorem chamber_identity_value (ε : Sign) {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g)
    (he : ∀ s, convergenceHalfPlane ε s → f s = g s) (s₀ : ℂ)
    (hfc : ContinuousAt f s₀) (hgc : ContinuousAt g s₀) : f s₀ = g s₀ := by
  exact ((hfc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hgc).mp
    (chamber_identity_germ ε hf hg he s₀)).eq_of_nhds

end DedekindZetaZeroFree.KPRankOneChamberUniqueness

end
