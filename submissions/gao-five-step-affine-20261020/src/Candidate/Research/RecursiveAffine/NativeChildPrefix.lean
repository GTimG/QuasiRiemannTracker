/- Source-native prefix count from PR67, namespaced to avoid importing unrelated density closure.
The dependent prefix type is definitionally the native ChildPrefix. Apache-2.0; inherited attribution retained. -/
/- The count of the rows of a second application of the two transforms to the children of a first one, jointly
over the child prefix and the second-level label. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.JointSourceCount

set_option autoImplicit false

/-! The rows of a second application of the two transforms, to a child presented by a multiplier `v` of the fixed
dictionary, are the joint source rows with the fixed row `v`. A pair of a child prefix `p` and a second-level label
has the row `jointSourceRow left (v p) (unit p) label`, with units that depend on the prefix. For a fixed row `w` the
prefix multiplier divides `w`, so the pairs over `w` number at most the divisors of `w`, times the prefixes over one
divisor, times the second-level labels over `w` for one prefix. -/

namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit IdealMobiusDivisorSum CenteredMomentSectorLocalization
open Cycle63Moment
local notation "O" => HeckeFamily.O

/-- A child of the first application of the two transforms: its first-source label, its second common pair and
its second inactive set. -/
def ChildPrefix := Σ _first : FirstSourceLabel, Σ second : Ideal O × Ideal O, Finset (CommonIndex second.1 second.2)

/-- The multiplier presenting the rows of a child in the fixed dictionary: the first frequency with the fixed unit
times the second frequency. -/
def childMultiplier (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O) (p : ChildPrefix) : O :=
  (u₀*unit p.1)*primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val*
    firstSourceNumerator left p.1*
    (commonFrequencyGenerator p.2.1.1 p.2.1.2*nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2)

/-- With unit label factors, the norm of a child multiplier is the norm of the fixed row times the norms of the
inactive-set generator, the first numerator, the common frequency generator and the nonunit frequency generator. -/
theorem normValue_childMultiplier (left : Bool) (u₀ : O) (unit : FirstSourceLabel → Oˣ) (p : ChildPrefix) :
    normValue (childMultiplier left u₀ (fun l => (unit l : O)) p) =
      normValue u₀*normValue (primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val)*
        normValue (firstSourceNumerator left p.1)*normValue (commonFrequencyGenerator p.2.1.1 p.2.1.2)*
        normValue (nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2) := by
  have h : childMultiplier left u₀ (fun l => (unit l : O)) p =
      u₀*primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val*
        firstSourceNumerator left p.1*commonFrequencyGenerator p.2.1.1 p.2.1.2*
        nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2*(unit p.1 : O) := by
    dsimp only [childMultiplier]
    ring
  have hunit (x : O) : normValue (x*(unit p.1 : O)) = normValue x := by
    unfold normValue
    rw [Ideal.span_singleton_mul_right_unit (unit p.1).isUnit]
  rw [h, hunit, normValue_mul, normValue_mul, normValue_mul, normValue_mul]

/-- The children whose multipliers generate one ideal `D`: at most `C Z^(m + loss)`. The first-source labels are
counted through their missing radical, the common pairs through the primes of `D`, and the inactive sets of one
pair through the primes of the pair. The constant precedes the children and the fixed unit. -/
theorem child_prefix_count (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ D : Ideal O, D ≠ ⊥ → (Ideal.absNorm D : ℝ) ≤ Z^B →
      ∀ m : ℝ, ∀ prefixes : Finset ChildPrefix,
      (∀ p ∈ prefixes, Ideal.span {childMultiplier left u₀ unit p} = D) →
      (∀ p ∈ prefixes, Supported p.1.1.1 ∧ p.1.1.2 ≠ 0 ∧ Supported p.2.1.1 ∧ p.2.1.2 ≠ 0) →
      (∀ p ∈ prefixes, primeSupport p.1.1.1 = primeSupport p.1.1.2 ∧
        primeSupport p.2.1.1 = primeSupport p.2.1.2) →
      (∀ p ∈ prefixes, ((D*firstSourceMissing left p.1).absNorm : ℝ) ≤ Z^B) →
      (∀ p ∈ prefixes, (p.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (p.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (p.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (p.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ p ∈ prefixes, ((firstSourceMissing left p.1).absNorm : ℝ) ≤ Z^m) →
        (prefixes.card : ℝ) ≤ C*Z^(m+loss) := by
  obtain ⟨C₁, hC₁, hfirst⟩ := actual_first_source_row_count B (loss/3) hB (by positivity)
  obtain ⟨C₂, hC₂, hpair⟩ := Cycle63.Physical.uniform_common_pair_count B (loss/3) hB (by positivity)
  obtain ⟨C₃, hC₃, hsubsets⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (loss/(3*(B+1)))
    (by positivity)
  refine ⟨C₁*C₂*C₃, by positivity, ?_⟩
  intro left u₀ unit Z hZ D hD hDnorm m prefixes hspan hnonzero heq hsupportnorm hnorm hmissing
  have hZ0 : 0 < Z := by linarith
  rcases prefixes.eq_empty_or_nonempty with hempty | ⟨p₀, hp₀⟩
  · rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  let g := childMultiplier left u₀ unit p₀
  have hgspan : Ideal.span {g} = D := hspan p₀ hp₀
  have hg : g ≠ 0 := by
    intro h
    apply hD
    rw [← hgspan, h, Ideal.span_singleton_eq_bot]
  -- Every multiplier generates `D`, so it is `g` up to a unit.
  have hassoc (p : ChildPrefix) (hp : p ∈ prefixes) : ∃ u : Oˣ, childMultiplier left u₀ unit p*u = g :=
    Ideal.span_singleton_eq_span_singleton.mp ((hspan p hp).trans hgspan.symm)
  have hF := hfirst left Z hZ g hg m (prefixes.image (fun p => p.1))
    (by intro f hf; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf; exact ⟨(hnonzero p hp).1, (hnonzero p hp).2.1⟩)
    (by intro f hf; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf; exact (heq p hp).1)
    (by
      intro f hf
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
      obtain ⟨u, hu⟩ := hassoc p hp
      exact ⟨u₀*unit p.1*u, commonFrequencyGenerator p.2.1.1 p.2.1.2,
        nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2, 1, by
          rw [← hu]
          dsimp only [childMultiplier, effectiveRow]
          ring⟩)
    (by intro f hf; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf; rw [hgspan]; exact hsupportnorm p hp)
    (by intro f hf; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf; exact ⟨(hnorm p hp).1, (hnorm p hp).2.1⟩)
    (by intro f hf; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf; exact hmissing p hp)
  have hP := hpair Z hZ (Ideal.span {g}) (Ideal.span_singleton_eq_bot.not.mpr hg) (by rw [hgspan]; exact hDnorm)
    (prefixes.image (fun p => p.2.1))
    (by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨(hnonzero p hp).2.2.1.1, (hnonzero p hp).2.2.2⟩)
    (by intro v hv; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv; exact (heq p hp).2)
    (by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨u, hu⟩ := hassoc p hp
      apply Cycle63.Physical.common_support_in_row _ _ (hnonzero p hp).2.2.1 (heq p hp).2 g hg
      exact ⟨(u₀*unit p.1)*primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val*
        firstSourceNumerator left p.1*nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2*u, by
          rw [← hu]
          dsimp only [childMultiplier]
          ring⟩)
    (by intro v hv; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv; exact (hnorm p hp).2.2)
  -- A child is determined by its first-source label, its common pair and the primes of its inactive set.
  let key := fun p : ChildPrefix => (p.1, p.2.1, p.2.2.image Subtype.val)
  have hinj : Set.InjOn key prefixes := by
    rintro ⟨f, cd, U⟩ - ⟨f', cd', U'⟩ - h
    simp only [key, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, hU⟩ := h
    rw [Finset.image_injective Subtype.val_injective hU]
  let keys := prefixes.image key
  let pairOf := fun k : FirstSourceLabel × (Ideal O × Ideal O) × Finset (Ideal O) => (k.1, k.2.1)
  -- The inactive sets of one pair are sets of its primes.
  have hsets (x : FirstSourceLabel × (Ideal O × Ideal O)) (hx : x ∈ keys.image pairOf) :
      ((keys.filter (fun k => pairOf k = x)).card : ℝ) ≤ C₃*Z^(loss/3) := by
    obtain ⟨k₀, hk₀, hx₀⟩ := Finset.mem_image.mp hx
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hk₀
    have hsub : (keys.filter (fun k => pairOf k = x)).image (fun k => k.2.2) ⊆
        (primeSupport x.2.1).powerset := by
      intro U hU
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨hk, hkx⟩ := Finset.mem_filter.mp hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      rw [Finset.mem_powerset]
      intro P hP
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hP
      have hcd : p.2.1 = x.2 := congrArg Prod.snd hkx
      rw [← hcd]
      exact (Finset.mem_inter.mp Q.property).1
    have hinjU : Set.InjOn (fun k : FirstSourceLabel × (Ideal O × Ideal O) × Finset (Ideal O) => k.2.2)
        (keys.filter (fun k => pairOf k = x) : Set (FirstSourceLabel × (Ideal O × Ideal O) × Finset (Ideal O))) := by
      intro k hk k' hk' h
      have e := (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hk').2.symm
      have e₁ := congrArg Prod.fst e
      have e₂ := congrArg Prod.snd e
      exact Prod.ext e₁ (Prod.ext e₂ h)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinjU, Finset.card_powerset] at hc
    have hx2 : x.2 = p₁.2.1 := (congrArg Prod.snd hx₀).symm
    have hne : x.2.1 ≠ ⊥ := by rw [hx2]; exact (hnonzero p₁ hp₁).2.2.1.1
    have hN : (Ideal.absNorm x.2.1 : ℝ) ≤ Z^B := by rw [hx2]; exact (hnorm p₁ hp₁).2.2.1
    calc ((keys.filter (fun k => pairOf k = x)).card : ℝ)
        ≤ (2:ℝ)^(primeSupport x.2.1).card := by exact_mod_cast hc
      _ ≤ C₃*(Ideal.absNorm x.2.1 : ℝ)^(loss/(3*(B+1))) := hsubsets x.2.1 hne
      _ ≤ C₃*(Z^B)^(loss/(3*(B+1))) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by positivity)) hC₃.le
      _ ≤ C₃*Z^(loss/3) := by
        rw [← Real.rpow_mul hZ0.le]
        apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) _) hC₃.le
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  -- The pairs of first-source label and common pair are at most the product of the two counts.
  have hpairs : ((keys.image pairOf).card : ℝ) ≤
      ((prefixes.image (fun p => p.1)).card : ℝ)*((prefixes.image (fun p => p.2.1)).card : ℝ) := by
    have hsub : keys.image pairOf ⊆ (prefixes.image (fun p => p.1)) ×ˢ (prefixes.image (fun p => p.2.1)) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    rw [← Nat.cast_mul, ← Finset.card_product]
    exact_mod_cast Finset.card_le_card hsub
  have he := Finset.card_eq_sum_card_fiberwise (fun k (hk : k ∈ keys) => Finset.mem_image_of_mem pairOf hk)
  calc (prefixes.card : ℝ) = (keys.card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ = ∑ x ∈ keys.image pairOf, ((keys.filter (fun k => pairOf k = x)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _x ∈ keys.image pairOf, C₃*Z^(loss/3) := Finset.sum_le_sum hsets
    _ = ((keys.image pairOf).card : ℝ)*(C₃*Z^(loss/3)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((C₁*Z^(m+loss/3))*(C₂*Z^(loss/3)))*(C₃*Z^(loss/3)) := by
      apply mul_le_mul_of_nonneg_right (hpairs.trans (mul_le_mul hF hP (Nat.cast_nonneg _) (by positivity)))
        (by positivity)
    _ = C₁*C₂*C₃*Z^(m+loss) := by
      have h : Z^(m+loss) = Z^(m+loss/3)*Z^(loss/3)*Z^(loss/3) := by
        rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        ring_nf
      rw [h]
      ring

/-- The children whose multipliers generate any given ideal: at most `C Z^(m + loss)`, when every child multiplier is
nonzero of norm at most `Z^B` and the children satisfy the support, norm and missing-radical bounds of
`child_prefix_count`. The constant precedes the children and the fixed unit. -/
theorem child_prefix_fiber_bound (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ m : ℝ, ∀ prefixes : Finset ChildPrefix,
      (∀ p ∈ prefixes, childMultiplier left u₀ unit p ≠ 0 ∧
        ((Ideal.span {childMultiplier left u₀ unit p}).absNorm : ℝ) ≤ Z^B) →
      (∀ p ∈ prefixes, Supported p.1.1.1 ∧ p.1.1.2 ≠ 0 ∧ Supported p.2.1.1 ∧ p.2.1.2 ≠ 0) →
      (∀ p ∈ prefixes, primeSupport p.1.1.1 = primeSupport p.1.1.2 ∧
        primeSupport p.2.1.1 = primeSupport p.2.1.2) →
      (∀ p ∈ prefixes,
        ((Ideal.span {childMultiplier left u₀ unit p}*firstSourceMissing left p.1).absNorm : ℝ) ≤ Z^B) →
      (∀ p ∈ prefixes, (p.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (p.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (p.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (p.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ p ∈ prefixes, ((firstSourceMissing left p.1).absNorm : ℝ) ≤ Z^m) →
      ∀ D : Ideal O,
        ((prefixes.filter (fun p => Ideal.span {childMultiplier left u₀ unit p} = D)).card : ℝ) ≤
          C*Z^(m+loss) := by
  obtain ⟨C, hC, hcount⟩ := child_prefix_count B loss hB hloss
  refine ⟨C, hC, ?_⟩
  intro left u₀ unit Z hZ m prefixes hmult hnonzero heq hsupportnorm hnorm hmissing D
  let fibre := prefixes.filter (fun p => Ideal.span {childMultiplier left u₀ unit p} = D)
  have mem (p : ChildPrefix) (hp : p ∈ fibre) :
      p ∈ prefixes ∧ Ideal.span {childMultiplier left u₀ unit p} = D := Finset.mem_filter.mp hp
  rcases fibre.eq_empty_or_nonempty with hempty | ⟨p₀, hp₀⟩
  · change ((fibre.card : ℕ) : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have hZ0 : 0 < Z := by linarith
    positivity
  have hD : D ≠ ⊥ := by
    rw [← (mem p₀ hp₀).2]
    exact Ideal.span_singleton_eq_bot.not.mpr (hmult p₀ (mem p₀ hp₀).1).1
  have hDnorm : (Ideal.absNorm D : ℝ) ≤ Z^B := by
    rw [← (mem p₀ hp₀).2]
    exact (hmult p₀ (mem p₀ hp₀).1).2
  exact hcount left u₀ unit Z hZ D hD hDnorm m fibre (fun p hp => (mem p hp).2)
    (fun p hp => hnonzero p (mem p hp).1) (fun p hp => heq p (mem p hp).1)
    (fun p hp => by rw [← (mem p hp).2]; exact hsupportnorm p (mem p hp).1)
    (fun p hp => hnorm p (mem p hp).1) (fun p hp => hmissing p (mem p hp).1)


end
end OAI.SevenEighths.Cycle153JointCount
