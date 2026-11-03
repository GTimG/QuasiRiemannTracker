/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/StandardAdditiveCharacter.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.LocalFields.PlacesAndCompletions
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Characters.RationalFrequencyNontriviality

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.PrincipalOfKP

def standardCharacter (F : Type) [Field F] [NumberField F] :
    ContinuousAddChar (KPAdditiveQuotient F) where
  toFun x := (adelicTraceQuotientCharacter F x : ℂ)
  map_zero_eq_one' := by
    change ((adelicTraceQuotientCharacter F 0 : Circle) : ℂ) = 1
    rw [AddChar.map_zero_eq_one (adelicTraceQuotientCharacter F), Circle.coe_one]
  map_add_eq_mul' := by
    intro a b
    change ((adelicTraceQuotientCharacter F (a + b) : Circle) : ℂ) =
      (adelicTraceQuotientCharacter F a : ℂ) * (adelicTraceQuotientCharacter F b : ℂ)
    rw [AddChar.map_add_eq_mul (adelicTraceQuotientCharacter F) a b, Circle.coe_mul]
  continuous_toFun :=
    continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)
  unitary := fun a => Circle.norm_coe _

theorem standardCharacter_nontrivial (F : Type) [Field F] [NumberField F] :
    KPReflectionSpec.NontrivialCharacter (standardCharacter F) := by
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.1 (adelicTraceQuotientCharacter_ne_one F)
  refine ⟨x, ?_⟩
  intro h
  change ((adelicTraceQuotientCharacter F x : Circle) : ℂ) = 1 at h
  apply hx
  apply Subtype.ext
  rw [h, Circle.coe_one]

end DedekindZetaZeroFree.PrincipalOfKP

end
