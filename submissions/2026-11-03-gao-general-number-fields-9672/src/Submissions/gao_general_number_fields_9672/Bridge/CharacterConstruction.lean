/-
2026-11-03 Dirichlet specialization bridge by Zhongpai Gao with AI assistance.
Apache-2.0. Original source attribution and licenses below are retained.
This module is adapted from the isolated checked CharacterConstruction.lean proof:
Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Tracker adaptation changes import paths only; all theorem bodies are unchanged.
The adapter applies to the genuine strengthened native Hecke theorem; full
native endpoint compatibility and official tracker admission remain pending.
-/
/-
Faithful rational ray character attached to an arbitrary Dirichlet character.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
-/
import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
import Submissions.gao_general_number_fields_9672.Bridge.RationalIdeals

open scoped NumberField Classical
open NumberField

namespace TrackerBridge

noncomputable def ratHeckeValue {q : ℕ} (χ : DirichletCharacter ℂ q)
    (I : Ideal RatIntegers) : ℂ :=
  if I = ⊥ then 0 else χ (Ideal.absNorm I)

lemma ratHeckeValue_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (I J : Ideal RatIntegers) :
    ratHeckeValue χ (I * J) = ratHeckeValue χ I * ratHeckeValue χ J := by
  by_cases hI : I = ⊥
  · simp [ratHeckeValue, hI]
  by_cases hJ : J = ⊥
  · simp [ratHeckeValue, hJ]
  have hIJ : I * J ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hI hJ
  simp only [ratHeckeValue, if_neg hI, if_neg hJ, if_neg hIJ, map_mul, Nat.cast_mul]

lemma ratHeckeValue_zero_iff {q : ℕ} (χ : DirichletCharacter ℂ q)
    (I : Ideal RatIntegers) :
    ratHeckeValue χ I = 0 ↔ I = ⊥ ∨ I ⊔ Ideal.span {(q : RatIntegers)} ≠ ⊤ := by
  by_cases hI : I = ⊥
  · simp [ratHeckeValue, hI]
  rw [ratHeckeValue, if_neg hI]
  simp only [hI, false_or]
  rw [MulChar.apply_eq_zero_iff, ZMod.isUnit_iff_coprime]
  exact not_congr (rat_ideal_coprime_iff I q).symm

lemma positive_rat_integer_eq_nat (α : RatIntegers)
    (hpos : ∀ φ : ℚ →+* ℝ, 0 < φ (α : ℚ)) :
    ∃ n : ℕ, 0 < n ∧ α = (n : RatIntegers) := by
  let a : ℤ := Rat.ringOfIntegersEquiv α
  have hα : (α : ℚ) = (a : ℚ) := (Rat.ringOfIntegersEquiv_apply_coe α).symm
  have hp := hpos (algebraMap ℚ ℝ)
  rw [hα] at hp
  have hp' : (0 : ℝ) < (a : ℝ) := by simpa only [map_intCast] using hp
  have ha : 0 < a := by exact_mod_cast hp'
  refine ⟨a.natAbs, Int.natAbs_pos.mpr ha.ne', ?_⟩
  apply Rat.ringOfIntegersEquiv.injective
  change a = Rat.ringOfIntegersEquiv (a.natAbs : RatIntegers)
  rw [map_natCast]
  exact (by simpa only [Int.natCast_natAbs, abs_of_pos ha] : (a.natAbs : ℤ) = a).symm

lemma ratHeckeValue_span {q : ℕ} (χ : DirichletCharacter ℂ q)
    (α : RatIntegers) (hα : α ≠ 0)
    (hmod : α - 1 ∈ Ideal.span {(q : RatIntegers)})
    (hpos : ∀ φ : ℚ →+* ℝ, 0 < φ (α : ℚ)) :
    ratHeckeValue χ (Ideal.span {α}) = 1 := by
  obtain ⟨n, hn, rfl⟩ := positive_rat_integer_eq_nat α hpos
  have hq : (q : ℤ) ∣ (n : ℤ) - 1 := by
    have h := Ideal.mem_map_of_mem (Rat.ringOfIntegersEquiv : RatIntegers →+* ℤ) hmod
    rw [Ideal.map_span] at h
    simpa only [map_sub, map_natCast, map_one, Set.image_singleton,
      Ideal.mem_span_singleton] using h
  have hnq : (n : ZMod q) = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr (by convert hq.neg_right using 1 <;> ring))
  have hspan : Ideal.span {(n : RatIntegers)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  simp only [ratHeckeValue, if_neg hspan, rat_absNorm_span, hnq, map_one]

noncomputable def dirichletRayCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) :
    DedekindZetaZeroFree.RayClassCharacter ℚ (Ideal.span {(q : RatIntegers)}) where
  toFun := ratHeckeValue χ
  map_mul' := ratHeckeValue_mul χ
  map_top' := by simp [ratHeckeValue]
  eq_zero_iff' := ratHeckeValue_zero_iff χ
  map_span' := ratHeckeValue_span χ

@[simp] lemma dirichletRayCharacter_span {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    dirichletRayCharacter χ (Ideal.span {(n : RatIntegers)}) =
      if n = 0 then 0 else χ n := by
  change ratHeckeValue χ (Ideal.span {(n : RatIntegers)}) = _
  rw [ratHeckeValue, rat_absNorm_span]
  have hn : Ideal.span {(n : RatIntegers)} = ⊥ ↔ n = 0 := by
    rw [Ideal.span_singleton_eq_bot]
    exact Nat.cast_eq_zero
  simp only [hn]

lemma dirichletRayCharacter_principal_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (dirichletRayCharacter χ).IsPrincipal ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.eq_one_iff.mpr
    intro a
    let n : ℕ := (a : ZMod q).val + q
    have hn : 0 < n := Nat.add_pos_right _ (NeZero.pos q)
    have ha : (n : ZMod q) = a := by simp [n]
    have hcop : n.Coprime q := (ZMod.isUnit_iff_coprime n q).mp (ha ▸ a.isUnit)
    have hspan : Ideal.span {(n : RatIntegers)} ≠ ⊥ := by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast hn.ne'
    have hv := h (Ideal.span {(n : RatIntegers)}) hspan ((rat_span_sup_span_iff n q).mpr hcop)
    simpa only [dirichletRayCharacter_span, if_neg hn.ne', ha] using hv
  · rintro rfl I hI hcop
    change ratHeckeValue (1 : DirichletCharacter ℂ q) I = 1
    rw [ratHeckeValue, if_neg hI]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr ((rat_ideal_coprime_iff I q).mp hcop))

lemma rat_modulus_ne_bot (q : ℕ) [NeZero q] :
    Ideal.span {(q : RatIntegers)} ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast NeZero.ne q

end TrackerBridge

#print axioms TrackerBridge.dirichletRayCharacter
#print axioms TrackerBridge.dirichletRayCharacter_principal_iff
