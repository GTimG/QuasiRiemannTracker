/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/MultiplicativeEulerProducts.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Analysis.FiniteEulerExpansion

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.IdealEuler

open scoped Classical

attribute [-instance] instCommCStarAlgebraComplex

universe u

theorem hasProd_finsupp_euler {P : Type u} (w : (P →₀ ℕ) → ℂ)
    (hzero : w 0 = 1)
    (hadd : ∀ e d : P →₀ ℕ, w (e + d) = w e * w d)
    (habs : Summable (fun e : P →₀ ℕ => ‖w e‖)) :
    HasProd (fun p : P => (1 - w (Finsupp.single p 1))⁻¹)
      (∑' e : P →₀ ℕ, w e) := by
  classical
  let g (S : Finset P) (e : P →₀ ℕ) : ℂ :=
    if e.support ⊆ S then w e else 0
  have hlim (e : P →₀ ℕ) :
      Filter.Tendsto (fun S => g S e) Filter.atTop (nhds (w e)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop e.support] with S hS
    simp [g, hS]
  have hbound : ∀ᶠ S in Filter.atTop, ∀ e : P →₀ ℕ, ‖g S e‖ ≤ ‖w e‖ := by
    apply Filter.Eventually.of_forall
    intro S e
    by_cases h : e.support ⊆ S
    · simp [g, h]
    · simp [g, h]
  have hconv := tendsto_tsum_of_dominated_convergence habs hlim hbound
  have heq (S : Finset P) :
      (∑' e : P →₀ ℕ, g S e) = ∏ p ∈ S, (1 - w (Finsupp.single p 1))⁻¹ := by
    rw [← (hasSum_finsupp_supported w hzero hadd habs S).tsum_eq]
    convert (tsum_subtype {e : P →₀ ℕ | e.support ⊆ S} w).symm using 1 <;>
      first | rfl | simp only [g, Set.indicator_apply, Set.mem_setOf_eq]
  change Filter.Tendsto (fun S : Finset P => ∏ p ∈ S,
    (1 - w (Finsupp.single p 1))⁻¹) Filter.atTop (nhds (∑' e : P →₀ ℕ, w e))
  simpa only [heq] using hconv

end DedekindZetaZeroFree.LargeSieve.IdealEuler
