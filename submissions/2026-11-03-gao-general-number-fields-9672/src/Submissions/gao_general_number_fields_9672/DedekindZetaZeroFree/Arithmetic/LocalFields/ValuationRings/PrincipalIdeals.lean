/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/ValuationRings/PrincipalIdeals.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility

theorem valuationInteger_mem_span_iff {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (r x : v.valuationSubring) (hr : (r : K) ≠ 0) :
    x ∈ Ideal.span {r} ↔ v (x : K) ≤ v (r : K) := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    have he := congrArg (fun z : v.valuationSubring => (z : K)) hy
    change (x : K) = (r : K) * (y : K) at he
    rw [he, map_mul]
    exact (mul_le_mul_of_nonneg_left y.property zero_le).trans (by simp)
  · intro hx
    let y : v.valuationSubring := ⟨(x : K) / (r : K), by
      change v ((x : K) / (r : K)) ≤ 1
      rw [map_div₀]
      exact (div_le_one₀ ((v.pos_iff).mpr hr)).mpr hx⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change (x : K) = (r : K) * ((x : K) / (r : K))
    field_simp
end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
