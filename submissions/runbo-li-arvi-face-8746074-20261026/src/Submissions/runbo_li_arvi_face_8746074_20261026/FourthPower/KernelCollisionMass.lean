/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform central mass of genuine repeated-prime blocks. At least two actual
half-powers occur in each frozen block. Constants precede the prime pool,
its cutoff, equality pattern and any subset of frozen assignments.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelCollisionEnergy
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.SieveCentralReference

set_option autoImplicit false
namespace Candidate.FourthPower.KernelCollisionMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open OAI.SevenEighths.Record12518109GainDeletion
open SieveDescent SieveCentralReference KernelCollisionEnergy
local notation "Id" => Ideal ActualEisensteinCubic.O

def centralWeight (B : ℝ) (P : Id) : ℝ := B*(Ideal.absNorm P : ℝ)^(-(1/2 : ℝ))

theorem centralWeight_nonneg (B : ℝ) (hB : 0 ≤ B) (P : Id) :
    0 ≤ centralWeight B P := mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem centralWeight_le (B : ℝ) (hB : 0 ≤ B) (P : Id) (hP : Supported P) :
    centralWeight B P ≤ B := by
  exact mul_le_of_le_one_right hB
    (Real.rpow_le_one_of_one_le_of_nonpos (CenteredExceptionalCount.norm_one_le hP.1)
      (by norm_num))

theorem central_pool_energy (δ B X : ℝ) (hδ : 0 < δ) (hX : 0 < X)
    (S : Finset Id) (hS : ∀ P ∈ S, Supported P ∧ (Ideal.absNorm P : ℝ) ≤ X) :
    (∑ P : S, (centralWeight B P.val)^2) ≤ B^2*X^δ*rootMass (1+δ) := by
  have hs (P : S) : (centralWeight B P.val)^2 = B^2*(Ideal.absNorm P.val : ℝ)⁻¹ := by
    have hn : 0 < (Ideal.absNorm P.val : ℝ) := zero_lt_one.trans_le
      (CenteredExceptionalCount.norm_one_le (hS P.val P.property).1.1)
    unfold centralWeight
    rw [mul_pow,← Real.rpow_natCast ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ))) 2,
      ← Real.rpow_mul hn.le]
    norm_num [Real.rpow_neg_one]
  simp_rw [hs]
  rw [← Finset.mul_sum,Finset.sum_coe_sort S (fun P : Id => (Ideal.absNorm P : ℝ)⁻¹)]
  exact (mul_le_mul_of_nonneg_left (reciprocal_mass δ hδ X hX S hS) (sq_nonneg B)).trans_eq
    (by ring)

variable {I : Type*} [Fintype I]

/-- The entire frozen collision family costs an arbitrarily small power.
The number of available primes never appears as a multiplicative loss. -/
theorem central_collision_mass (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset Id,
      (∀ P ∈ S, Supported P ∧ (Ideal.absNorm P : ℝ) ≤ X) → ∀ r : Setoid I,
      (∑ t : {q // ¬singletonBlock r q} → S,
        ∏ q : {q // ¬singletonBlock r q}, ∏ _i ∈ collisionBlock r q.val,
          centralWeight B (t q).val) ≤ C*X^ε := by
  let K := Fintype.card I
  let δ := ε/((K : ℝ)+1)
  have hd : 0 < (K : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hd
  let Q := rootMass (1+δ)+1
  have hQ : 1 ≤ Q := by dsimp [Q]; exact le_add_of_nonneg_left (rootMass_nonneg _)
  let C := (Q*B^K)^K
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro X hX S hS r
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  let L := Q*X^δ
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hQ (Real.one_le_rpow hX hδ.le)
  have he : ∀ i : I, (∑ P : S, (centralWeight B P.val)^2) ≤ L*B^2 := by
    intro i
    apply (central_pool_energy δ B X hδ hX0 S hS).trans
    dsimp only [L,Q]
    have hp : 0 ≤ B^2*X^δ := mul_nonneg (sq_nonneg B) (Real.rpow_nonneg hX0.le _)
    nlinarith
  have hh := collision_assignments_mass r (fun _i : I => fun P : S => centralWeight B P.val)
    B L hB hL (fun _i P => centralWeight_nonneg B (zero_le_one.trans hB) P.val)
    (fun _i P => centralWeight_le B (zero_le_one.trans hB) P.val (hS P.val P.property).1)
    he K (le_refl _)
  have hexp : δ*(K : ℝ) ≤ ε := by
    have h := div_mul_cancel₀ ε (ne_of_gt hd)
    change δ*((K : ℝ)+1)=ε at h
    nlinarith
  have hcost : (L*B^K)^K = C*X^(δ*(K : ℝ)) := by
    dsimp only [L,C]
    rw [show Q*X^δ*B^K=(Q*B^K)*X^δ by ring,mul_pow,
      ← Real.rpow_natCast (X^δ) K,← Real.rpow_mul hX0.le]
  rw [hcost] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX hexp) hC.le)

/-- Literal complex frozen coefficients, including arbitrary bounded phases,
have the same mass; all additional admissibility conditions may be retained. -/
theorem actual_collision_mass (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset Id,
      (∀ P ∈ S, Supported P ∧ (Ideal.absNorm P : ℝ) ≤ X) → ∀ r : Setoid I,
      ∀ a : I → S → ℂ, (∀ i P, ‖a i P‖ ≤ centralWeight B P.val) →
      ∀ T : Finset ({q // ¬singletonBlock r q} → S),
      (∑ t ∈ T, ‖∏ q : {q // ¬singletonBlock r q},
        ∏ i ∈ collisionBlock r q.val, a i (t q)‖) ≤ C*X^ε := by
  obtain ⟨C,hC,hbound⟩ := central_collision_mass (I := I) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS r a ha T
  let w := fun t : {q // ¬singletonBlock r q} → S =>
    ∏ q : {q // ¬singletonBlock r q}, ∏ i ∈ collisionBlock r q.val,
      centralWeight B (t q).val
  have hw (t) : 0 ≤ w t := Finset.prod_nonneg (fun q _ =>
    Finset.prod_nonneg (fun _i _ => centralWeight_nonneg B (zero_le_one.trans hB) _))
  calc
    _ ≤ ∑ t ∈ T, w t := by
      apply Finset.sum_le_sum
      intro t _
      simp only [norm_prod]
      exact Finset.prod_le_prod₀
        (fun q _ => Finset.prod_nonneg (fun i _ => norm_nonneg _))
        (fun q _ => Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ha i (t q)))
    _ ≤ ∑ t, w t := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun t _ _ => hw t)
    _ ≤ _ := hbound X hX S hS r

end
end Candidate.FourthPower.KernelCollisionMass
