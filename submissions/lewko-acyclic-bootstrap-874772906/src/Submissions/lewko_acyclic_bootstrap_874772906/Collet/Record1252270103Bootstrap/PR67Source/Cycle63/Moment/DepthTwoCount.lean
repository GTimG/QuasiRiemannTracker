import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointSourceCount
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Density.JointRows
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The count of the rows of a second application of the two transforms to the children of a first one, jointly
over the child prefix and the second-level label. Released under Apache 2.0. -/
set_option autoImplicit false

/-! The rows of a second application of the two transforms, to a child presented by a multiplier `v` of the fixed
dictionary, are the joint source rows with the fixed row `v`. A pair of a child prefix `p` and a second-level label
has the row `jointSourceRow left (v p) (unit p) label`, with units that depend on the prefix. For a fixed row `w` the
prefix multiplier divides `w`, so the pairs over `w` number at most the divisors of `w`, times the prefixes over one
divisor, times the second-level labels over `w` for one prefix. -/

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit IdealMobiusDivisorSum CenteredMomentSectorLocalization
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

/-- Composite prefixes `(p, p')` with multiplier `v p * v' p'` over one ideal `D ≠ 0`: at most the divisors of `D`
times `A` first prefixes over one ideal times `A'` second prefixes over one ideal. This bounds the prefixes of a
product of child multipliers, as at a further level of the step. -/
theorem composite_prefix_fiber_card {P P' : Type*} (v : P → O) (v' : P' → O) (S : Finset (P × P'))
    (D : Ideal O) (hD : D ≠ ⊥) (A A' : ℝ)
    (hA : ∀ D₁ : Ideal O, (((S.image Prod.fst).filter (fun p => Ideal.span {v p} = D₁)).card : ℝ) ≤ A)
    (hA' : ∀ D₂ : Ideal O, (((S.image Prod.snd).filter (fun p => Ideal.span {v' p} = D₂)).card : ℝ) ≤ A') :
    ((S.filter (fun x => Ideal.span {v x.1*v' x.2} = D)).card : ℝ) ≤ (idealDivisors D).card*(A*A') := by
  have hA0 : 0 ≤ A := (Nat.cast_nonneg _).trans (hA ⊥)
  have hA'0 : 0 ≤ A' := (Nat.cast_nonneg _).trans (hA' ⊥)
  let over := fun D₁ : Ideal O => S.filter (fun x => Ideal.span {v x.1*v' x.2} = D ∧ Ideal.span {v x.1} = D₁)
  have hsub : S.filter (fun x => Ideal.span {v x.1*v' x.2} = D) ⊆ (idealDivisors D).biUnion over := by
    intro x hx
    obtain ⟨hxS, hxD⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_biUnion.mpr ⟨Ideal.span {v x.1}, ?_, Finset.mem_filter.mpr ⟨hxS, hxD, rfl⟩⟩
    rw [mem_idealDivisors hD, ← hxD, ← Ideal.span_singleton_mul_span_singleton]
    exact dvd_mul_right _ _
  have hover (D₁ : Ideal O) : ((over D₁).card : ℝ) ≤ A*A' := by
    rcases (over D₁).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
    · rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨-, hx₀D, hx₀1⟩ := Finset.mem_filter.mp hx₀
    have hD₁ : D₁ ≠ 0 := by
      intro h0
      apply hD
      rw [← hx₀D, ← Ideal.span_singleton_mul_span_singleton, hx₀1, h0, zero_mul, Ideal.zero_eq_bot]
    have hcof (x : P × P') (hx : x ∈ over D₁) : Ideal.span {v' x.2} = Ideal.span {v' x₀.2} := by
      obtain ⟨-, hxD, hx1⟩ := Finset.mem_filter.mp hx
      have h₁ : D₁*Ideal.span {v' x.2} = D := by
        rw [← hx1, Ideal.span_singleton_mul_span_singleton]
        exact hxD
      have h₂ : D₁*Ideal.span {v' x₀.2} = D := by
        rw [← hx₀1, Ideal.span_singleton_mul_span_singleton]
        exact hx₀D
      exact mul_left_cancel₀ hD₁ (h₁.trans h₂.symm)
    have hprod : over D₁ ⊆ ((S.image Prod.fst).filter (fun p => Ideal.span {v p} = D₁)) ×ˢ
        ((S.image Prod.snd).filter (fun p => Ideal.span {v' p} = Ideal.span {v' x₀.2})) := by
      intro x hx
      have hxS := (Finset.mem_filter.mp hx).1
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hxS,
        (Finset.mem_filter.mp hx).2.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hxS, hcof x hx⟩⟩
    calc ((over D₁).card : ℝ)
        ≤ ((((S.image Prod.fst).filter (fun p => Ideal.span {v p} = D₁)) ×ˢ
            ((S.image Prod.snd).filter (fun p => Ideal.span {v' p} = Ideal.span {v' x₀.2}))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hprod
      _ ≤ A*A' := by
          rw [Finset.card_product, Nat.cast_mul]
          exact mul_le_mul (hA D₁) (hA' _) (Nat.cast_nonneg _) hA0
  calc ((S.filter (fun x => Ideal.span {v x.1*v' x.2} = D)).card : ℝ)
      ≤ (((idealDivisors D).biUnion over).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ D₁ ∈ idealDivisors D, ((over D₁).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _D₁ ∈ idealDivisors D, A*A' := Finset.sum_le_sum (fun D₁ _ => hover D₁)
    _ = (idealDivisors D).card*(A*A') := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The row of a pair of a child prefix and a second-level label: the joint source row with the prefix multiplier as
fixed row and the units of the prefix. -/
def depthTwoRow {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O)
    (x : P × JointSourceLabel) : O :=
  jointSourceRow left (v x.1) (unit x.1) x.2

/-- The prefix multiplier divides the row of a pair. -/
theorem prefix_dvd_depthTwoRow {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O)
    (x : P × JointSourceLabel) : v x.1 ∣ depthTwoRow v left unit x :=
  ⟨unit x.1 x.2.1*primeSubsetGenerator (fun P : CommonIndex x.2.1.1.1 x.2.1.1.2 => P.val) x.2.1.2.val*
    firstSourceNumerator left x.2.1*commonFrequencyGenerator x.2.2.1.1 x.2.2.1.2*
    nonunitFrequencyGenerator x.2.2.1.1 x.2.2.1.2 x.2.2.2.val.1*x.2.2.2.val.2,
    by dsimp only [depthTwoRow, jointSourceRow, effectiveRow]; ring⟩

/-- The pairs with a fixed row `w`: at most `C Z^(m + loss)` second-level labels for each of at most `A` prefixes over
each divisor of `w`. The constant precedes the prefixes, their multipliers, their units and the labels. -/
theorem depth_two_source_row_count (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O),
      ∀ Z : ℝ, 2 ≤ Z → ∀ w : O, w ≠ 0 → (Ideal.absNorm (Ideal.span {w}) : ℝ) ≤ Z^B →
      ∀ m A : ℝ, ∀ prefixes : Finset P, ∀ pairs : Finset (P × JointSourceLabel),
      (∀ x ∈ pairs, x.1 ∈ prefixes) →
      (∀ D : Ideal O, ((prefixes.filter (fun p => Ideal.span {v p} = D)).card : ℝ) ≤ A) →
      (∀ x ∈ pairs, depthTwoRow v left unit x = w) →
      (∀ x ∈ pairs, Supported x.2.1.1.1 ∧ x.2.1.1.2 ≠ 0 ∧ Supported x.2.2.1.1 ∧ x.2.2.1.2 ≠ 0) →
      (∀ x ∈ pairs, primeSupport x.2.1.1.1 = primeSupport x.2.1.1.2 ∧
        primeSupport x.2.2.1.1 = primeSupport x.2.2.1.2) →
      (∀ x ∈ pairs, ((Ideal.span {w}*firstSourceMissing left x.2.1).absNorm : ℝ) ≤ Z^B) →
      (∀ x ∈ pairs, (x.2.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.2.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (x.2.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.2.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ x ∈ pairs, ((firstSourceMissing left x.2.1).absNorm : ℝ) ≤ Z^m) →
        (pairs.card : ℝ) ≤ C*Z^(m+loss)*A := by
  obtain ⟨C₁, hC₁, hlabels⟩ := actual_joint_source_row_count B (loss/2) hB (by positivity)
  obtain ⟨C₂, hC₂, hdivisors⟩ := CenteredMomentMask.polynomial_mask_divisor_bound (loss/2) B (by positivity) hB
  refine ⟨C₁*C₂, mul_pos hC₁ hC₂, ?_⟩
  intro P v left unit Z hZ w hw hwnorm m A prefixes pairs hpre hprefix hrow hnonzero heq hsupportnorm hnorm
    hmissing
  have hZ0 : 0 < Z := by linarith
  have hA : 0 ≤ A := (Nat.cast_nonneg _).trans (hprefix ⊥)
  let K := C₁*Z^(m+loss/2)
  have hK : 0 ≤ K := by positivity
  -- One prefix carries at most `K` second-level labels: they are the labels of the level-one count at the fixed row
  -- `v p` with the units `unit p`, and the label determines the pair.
  have hper (p : P) : ((pairs.filter (fun x => x.1 = p)).card : ℝ) ≤ K := by
    let over := pairs.filter (fun x => x.1 = p)
    have mem (x : P × JointSourceLabel) (hx : x ∈ over) : x ∈ pairs ∧ x.1 = p := Finset.mem_filter.mp hx
    have hinj : Set.InjOn Prod.snd (over : Set (P × JointSourceLabel)) := by
      intro x hx y hy hxy
      exact Prod.ext ((mem x hx).2.trans (mem y hy).2.symm) hxy
    have hc := hlabels left (v p) (unit p) Z hZ w hw hwnorm m (over.image Prod.snd)
      (by
        intro label hl
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
        have h := hrow x (mem x hx).1
        rw [← (mem x hx).2]
        exact h)
      (by intro label hl; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl; exact hnonzero x (mem x hx).1)
      (by intro label hl; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl; exact heq x (mem x hx).1)
      (by intro label hl; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl; exact hsupportnorm x (mem x hx).1)
      (by intro label hl; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl; exact hnorm x (mem x hx).1)
      (by intro label hl; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl; exact hmissing x (mem x hx).1)
    rw [Finset.card_image_of_injOn hinj] at hc
    exact hc
  -- Over one divisor `D` lie at most `A` prefixes.
  have hfiber (D : Ideal O) :
      ((pairs.filter (fun x => depthTwoRow v left unit x = w ∧ Ideal.span {v x.1} = D)).card : ℝ) ≤ A*K := by
    let over := prefixes.filter (fun p => Ideal.span {v p} = D)
    have hsub : pairs.filter (fun x => depthTwoRow v left unit x = w ∧ Ideal.span {v x.1} = D) ⊆
        over.biUnion (fun p => pairs.filter (fun x => x.1 = p)) := by
      intro x hx
      obtain ⟨hxp, -, hD⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_biUnion.mpr ⟨x.1, Finset.mem_filter.mpr ⟨hpre x hxp, hD⟩, Finset.mem_filter.mpr ⟨hxp, rfl⟩⟩
    calc ((pairs.filter (fun x => depthTwoRow v left unit x = w ∧ Ideal.span {v x.1} = D)).card : ℝ)
        ≤ ((over.biUnion (fun p => pairs.filter (fun x => x.1 = p))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ p ∈ over, ((pairs.filter (fun x => x.1 = p)).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ over, K := Finset.sum_le_sum (fun p _ => hper p)
      _ = (over.card : ℝ)*K := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ A*K := mul_le_mul_of_nonneg_right (hprefix D) hK
  have hall : pairs.filter (fun x => depthTwoRow v left unit x = w) = pairs :=
    Finset.filter_true_of_mem (fun x hx => hrow x hx)
  have hc := LocalMoment.composite_row_fiber_card pairs (fun x => v x.1) (depthTwoRow v left unit) w hw (A*K)
    (fun x _ hx => hx ▸ prefix_dvd_depthTwoRow v left unit x) hfiber
  rw [hall] at hc
  have hd := hdivisors Z (by linarith) (Ideal.span {w}) (Ideal.span_singleton_eq_bot.not.mpr hw) hwnorm
  calc (pairs.card : ℝ) ≤ (idealDivisors (Ideal.span {w})).card*(A*K) := hc
    _ ≤ (C₂*Z^(loss/2))*(A*K) := mul_le_mul_of_nonneg_right hd (mul_nonneg hA hK)
    _ = C₁*C₂*Z^(m+loss)*A := by
      have hsplit : Z^(m+loss) = Z^(loss/2)*Z^(m+loss/2) := by
        rw [← Real.rpow_add hZ0]
        ring_nf
      rw [hsplit]
      ring

/-- A pair with a nonzero row. -/
def NonzeroDepthTwoPair {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O) :=
  {x : P × JointSourceLabel // depthTwoRow v left unit x ≠ 0}

/-- The row of a pair with a nonzero row, as a frequency. -/
def nonzeroDepthTwoRow {P : Type*} {v : P → O} {left : Bool} {unit : P → FirstSourceLabel → O}
    (x : NonzeroDepthTwoPair v left unit) : ProbePhysical.NonzeroFrequency :=
  ⟨depthTwoRow v left unit x.val, x.property⟩

/-- The pairs whose rows have norm at most `Z^q` and, in the fixed dictionary family, a zero with real part at least
`a` and height at most `T`: the density bound of their rows times the pairs over one row. The height degree precedes
the dictionary, and the constants precede the prefixes, their multipliers, their units, the labels, both heights and
the bin position. -/
theorem depth_two_high_row_count {Dict : Type*} [Fintype Dict] (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∀ base : Dict → Character, ∃ C : ℝ, 0 < C ∧
      ∀ {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O),
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m A a T : ℝ, q ≤ Q → 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ reverse : Dict → Bool, ∀ prefixes : Finset P, ∀ pairs : Finset (NonzeroDepthTwoPair v left unit),
      (∀ x ∈ pairs, x.val.1 ∈ prefixes) →
      (∀ D : Ideal O, ((prefixes.filter (fun p => Ideal.span {v p} = D)).card : ℝ) ≤ A) →
      (∀ x ∈ pairs, LocalMoment.rawFrequencyNorm (nonzeroDepthTwoRow x) ≤ Z^q ∧
        LocalMoment.naturalActualZeroRow base reverse a T (nonzeroDepthTwoRow x)) →
      (∀ x ∈ pairs, Supported x.val.2.1.1.1 ∧ x.val.2.1.1.2 ≠ 0 ∧ Supported x.val.2.2.1.1 ∧ x.val.2.2.1.2 ≠ 0) →
      (∀ x ∈ pairs, primeSupport x.val.2.1.1.1 = primeSupport x.val.2.1.1.2 ∧
        primeSupport x.val.2.2.1.1 = primeSupport x.val.2.2.1.2) →
      (∀ x ∈ pairs, ((Ideal.span {depthTwoRow v left unit x.val}*firstSourceMissing left x.val.2.1).absNorm : ℝ) ≤
        Z^B) →
      (∀ x ∈ pairs, (x.val.2.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.val.2.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (x.val.2.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.val.2.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ x ∈ pairs, ((firstSourceMissing left x.val.2.1).absNorm : ℝ) ≤ Z^m) →
        (pairs.card : ℝ) ≤ C*(1+T)^J*Z^(m+q*LocalMoment.unmarkedDensity (2*a-1)+loss)*A := by
  let δ := loss/(2*(Q+1))
  have hδ : 0 < δ := div_pos hloss (by positivity)
  obtain ⟨J, hJ⟩ := LocalMoment.card_le_density_mul_fiber (Label := Dict) δ hδ
  obtain ⟨C, hC, hfiber⟩ := depth_two_source_row_count B (loss/2) hB (by positivity)
  refine ⟨J, fun base => ?_⟩
  obtain ⟨D, hD, hcount⟩ := hJ base
  refine ⟨D*C, mul_pos hD hC, ?_⟩
  intro P v left unit Z hZ q m A a T hq ha ha' hT reverse prefixes pairs hpre hprefix hzero hnonzero heq
    hsupportnorm hnorm hmissing
  have hZ0 : 0 < Z := by linarith
  have hA : 0 ≤ A := (Nat.cast_nonneg _).trans (hprefix ⊥)
  have hc := hcount nonzeroDepthTwoRow reverse a T ha ha' hT (Z^q) (Real.rpow_pos_of_pos hZ0 q) pairs
    (C*Z^(m+loss/2)*A) hzero (by
      intro w
      let over := pairs.filter (fun x => nonzeroDepthTwoRow x = w)
      have mem (x : NonzeroDepthTwoPair v left unit) (hx : x ∈ over) :
          x ∈ pairs ∧ depthTwoRow v left unit x.val = w.val := by
        have h := Finset.mem_filter.mp hx
        exact ⟨h.1, congrArg Subtype.val h.2⟩
      by_cases hne : over.Nonempty
      · obtain ⟨x₀, hx₀⟩ := hne
        have hwnorm : (Ideal.absNorm (Ideal.span {w.val}) : ℝ) ≤ Z^B := by
          have h := (hzero x₀ (mem x₀ hx₀).1).1
          change ((Ideal.span {depthTwoRow v left unit x₀.val}).absNorm : ℝ) ≤ Z^q at h
          rw [(mem x₀ hx₀).2] at h
          exact h.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (hq.trans hQB))
        have hinj : Set.InjOn Subtype.val (over : Set (NonzeroDepthTwoPair v left unit)) :=
          fun x _ y _ h => Subtype.ext h
        have hb := hfiber v left unit Z hZ w.val w.property hwnorm m A prefixes (over.image Subtype.val)
          (by intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hpre y (mem y hy).1)
          hprefix
          (by intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact (mem y hy).2)
          (by intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hnonzero y (mem y hy).1)
          (by intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact heq y (mem y hy).1)
          (by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
            have h := hsupportnorm y (mem y hy).1
            rwa [(mem y hy).2] at h)
          (by intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hnorm y (mem y hy).1)
          (by intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hmissing y (mem y hy).1)
        rw [Finset.card_image_of_injOn hinj] at hb
        exact hb
      · change ((over.card : ℕ) : ℝ) ≤ _
        rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (by positivity) hA)
  have habsorb := LocalMoment.density_loss_absorb (ρ := LocalMoment.unmarkedDensity (2*a-1)) (by linarith : (1:ℝ) ≤ Z)
    hQ hq hloss
  calc (pairs.card : ℝ)
      ≤ D*(1+T)^J*(Z^q)^(LocalMoment.unmarkedDensity (2*a-1)+δ)*(C*Z^(m+loss/2)*A) := hc
    _ ≤ D*(1+T)^J*Z^(q*LocalMoment.unmarkedDensity (2*a-1)+loss/2)*(C*Z^(m+loss/2)*A) := by
      gcongr
    _ = (D*C)*(1+T)^J*Z^(m+q*LocalMoment.unmarkedDensity (2*a-1)+loss)*A := by
      have h : Z^(m+q*LocalMoment.unmarkedDensity (2*a-1)+loss) =
          Z^(q*LocalMoment.unmarkedDensity (2*a-1)+loss/2)*Z^(m+loss/2) := by
        rw [← Real.rpow_add hZ0]
        ring_nf
      rw [h]
      ring

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
