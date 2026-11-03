/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/Residues/UnitReduction.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.LocalFields.Residues.GlobalQuotientEquivalence

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem reduction_isUnit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (x : Residue C p n) :
    IsUnit (reduction C p n hn x) ↔ IsUnit x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) r) ↔
    IsUnit (Ideal.Quotient.mk (Ideal.span {generator C p ^ n}) r)
  rw [← Ideal.span_singleton_pow, (generator_generates C p).2]
  exact (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk _ hn).symm

theorem exterior_notMem (p : ExteriorPrime A) : p.val ∉ A.Sf := by
  intro hp
  have h := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
  rw [sup_idem] at h
  exact p.val.isPrime.ne_top h
end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
