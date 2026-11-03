/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/HolomorphicZeroTransfer.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Mellin.PuncturedHalfPlane

@[expose] public section

open Filter
open scoped Topology

namespace DedekindZetaZeroFree

theorem mellin_holomorphic_zero_transfer
    (σ : ℝ) (hσ : σ < 1) (L T N : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | σ < s.re ∧ s ≠ 1})
    (hT : AnalyticOnNhd ℂ T {s : ℂ | σ < s.re ∧ s ≠ 1})
    (hN : AnalyticOnNhd ℂ N {s : ℂ | σ < s.re ∧ s ≠ 1})
    (haxis : ∀ t : ℝ,
      L ((2 : ℂ) + t * Complex.I) * T ((2 : ℂ) + t * Complex.I) =
        N ((2 : ℂ) + t * Complex.I))
    (hN_ne : ∀ s ∈ {s : ℂ | σ < s.re ∧ s ≠ 1}, N s ≠ 0) :
    ∀ s ∈ {s : ℂ | σ < s.re ∧ s ≠ 1}, L s ≠ 0 := by

  have hprod : AnalyticOnNhd ℂ (fun z => L z * T z) {s : ℂ | σ < s.re ∧ s ≠ 1} :=
    hL.mul hT

  have hacc : AccPt (2 : ℂ) (𝓟 {z : ℂ | ∃ t : ℝ, t ≠ 0 ∧ z = (2 : ℂ) + t * Complex.I}) :=
    mellin_punctured_halfplane_two_accPt
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), L z * T z = N z := by
    refine (accPt_iff_frequently_nhdsNE.mp hacc).mono ?_
    rintro z ⟨t, -, rfl⟩
    exact haxis t

  have heq : Set.EqOn (fun z => L z * T z) N {s : ℂ | σ < s.re ∧ s ≠ 1} :=
    hprod.eqOn_of_preconnected_of_frequently_eq hN
      (mellin_punctured_halfplane_isPreconnected σ hσ)
      (mellin_punctured_halfplane_two_mem σ hσ) hfreq
  intro s hs hLs
  have hzero : L s * T s = N s := heq hs
  simp only [hLs, zero_mul] at hzero
  exact hN_ne s hs hzero.symm

end DedekindZetaZeroFree
