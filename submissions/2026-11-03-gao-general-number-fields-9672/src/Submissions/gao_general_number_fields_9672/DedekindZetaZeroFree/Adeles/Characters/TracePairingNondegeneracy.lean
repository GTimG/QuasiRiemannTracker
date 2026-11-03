/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/TracePairingNondegeneracy.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Characters.TraceCharacter

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

theorem localFiniteCharacter_left_nondegenerate (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) (hx : x ≠ 0) :
    ∃ y : v.adicCompletion F, localFiniteCharacter F v (x * y) ≠ 1 := by
  have hn : (Module.finrank ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) :
      ℚ_[PlaceTraceAdapter.prime F v]) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos
      (R := ℚ_[PlaceTraceAdapter.prime F v]) (M := v.adicCompletion F)))
  let t : ℚ_[PlaceTraceAdapter.prime F v] :=
    ((PlaceTraceAdapter.prime F v).1 : ℚ_[PlaceTraceAdapter.prime F v])⁻¹ /
      (Module.finrank ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) :
        ℚ_[PlaceTraceAdapter.prime F v])
  refine ⟨x⁻¹ * algebraMap ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) t, ?_⟩
  rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul, localFiniteCharacter_apply]
  change rationalPadicCharacter (PlaceTraceAdapter.prime F v)
    (Algebra.trace ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F)
      (algebraMap ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) t)) ≠ 1
  rw [Algebra.trace_algebraMap, nsmul_eq_mul]
  have ht : (Module.finrank ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) :
      ℚ_[PlaceTraceAdapter.prime F v]) * t =
      ((PlaceTraceAdapter.prime F v).1 : ℚ_[PlaceTraceAdapter.prime F v])⁻¹ := by
    dsimp [t]
    exact mul_div_cancel₀ _ hn
  rw [ht]
  exact rationalPadicCharacter_inv_prime_ne_one (PlaceTraceAdapter.prime F v)

theorem localFiniteCharacter_right_nondegenerate (v : HeightOneSpectrum (𝓞 F))
    (y : v.adicCompletion F) (hy : y ≠ 0) :
    ∃ x : v.adicCompletion F, localFiniteCharacter F v (x * y) ≠ 1 := by
  obtain ⟨x, hx⟩ := localFiniteCharacter_left_nondegenerate F v y hy
  exact ⟨x, by simpa only [mul_comm] using hx⟩

end DedekindZetaZeroFree

end
