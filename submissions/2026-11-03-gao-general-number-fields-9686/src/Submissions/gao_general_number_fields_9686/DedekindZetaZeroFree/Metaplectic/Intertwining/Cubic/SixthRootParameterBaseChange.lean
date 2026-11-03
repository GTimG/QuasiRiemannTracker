/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/Cubic/SixthRootParameterBaseChange.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellRestriction
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ConditionalCubicResidueReduction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPActualResidueSources

theorem scaled_root_polynomial_ne_zero (α : ℂ) (hα : α ≠ 0)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    p.eval₂ (RatFunc.C : ℂ →+* RatFunc ℂ) (RatFunc.C α * RatFunc.X) ≠ 0 := by
  have hx : Transcendental ℂ (RatFunc.C α * RatFunc.X : RatFunc ℂ) := by
    have h := (RatFunc.transcendental_X (K := ℂ)).aeval (Polynomial.C α * Polynomial.X)
      (by simp [hα]) (by simp [hα])
    simpa [Polynomial.aeval_def] using h
  intro he
  apply hp
  apply (transcendental_iff_injective.mp hx)
  simpa only [Polynomial.aeval_def, map_zero, RatFunc.algebraMap_eq_C] using he

theorem scaled_root_rational_denom_ne_zero (α : ℂ) (hα : α ≠ 0) (R : RatFunc ℂ) :
    R.denom.eval₂ (RatFunc.C : ℂ →+* RatFunc ℂ) (RatFunc.C α * RatFunc.X) ≠ 0 :=
  scaled_root_polynomial_ne_zero α hα R.denom (RatFunc.denom_ne_zero R)

end DedekindZetaZeroFree.KPActualResidueSources

end
