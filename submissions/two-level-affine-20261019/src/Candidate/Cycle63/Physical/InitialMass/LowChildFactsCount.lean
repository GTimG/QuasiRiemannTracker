/- The count of the rows of the second expansion of the children of the first labels over one ideal of their
multipliers: the prefixes over the ideal, times the rows over one prefix. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildRowMultiplier
import Candidate.Cycle63.Physical.InitialMass.SecondCoarseSupport

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment IdealMobiusDivisorSum CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- The rows of the second expansion over one child prefix number at most the squarefree divisors of the prefix's
first common ideal times the dyad box, without any condition on the radii `K` of the blocks: the seed of a row divides
the first common ideal of its block by the gates of the common labels alone. -/
theorem second_block_rows_per_prefix_nok {Label : Type*} [Fintype Label]
    (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
    (R seed : Label → Ideal O) (hseed : ∀ l, Squarefree (seed l))
    (hz₁ : ∀ l, (s l).W₁ 0 = 0) (hz₂ : ∀ l, (s l).W₂ 0 = 0)
    (K Tsec : Label → ℝ) (Z ξ : ℝ)
    (first : Label → FirstSourceLabel) (hfirst : Function.Injective (fun l => (first l, seed l)))
    (rows : Finset ((l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ))
    (box : Finset (Fin 4 → ℤ))
    (hbox : ∀ r ∈ rows, actualSecondDyad (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2 ∈ box)
    (p : ChildPrefix) (hp : p.2.1.1 ≠ ⊥) :
    ((rows.filter (fun r => secondBlockPrefix slots s R seed K Tsec Z ξ first r = p)).card : ℝ) ≤
      (((idealDivisors p.2.1.1).filter Squarefree).card : ℝ) * box.card := by
  let fiber := rows.filter (fun r => secondBlockPrefix slots s R seed K Tsec Z ξ first r = p)
  let code := fun r : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ =>
    (seed r.1, actualSecondDyad (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2)
  have hmaps : ∀ r ∈ fiber, code r ∈ ((idealDivisors p.2.1.1).filter Squarefree) ×ˢ box := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hgates := actual_common_gates (s r.1) (R r.1) (seed r.1) (hseed r.1) (hz₁ r.1) (hz₂ r.1) _ _
      r.2.1.val.property
    have hC : p.2.1.1 = r.2.1.val.val.1 := by
      rw [← hr'.2]
      rfl
    have hdvd : seed r.1 ∣ p.2.1.1 := by
      rw [hC]
      exact hgates.2.2.2.1
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨(mem_idealDivisors hp).mpr hdvd, hseed r.1⟩,
      hbox r hr'.1⟩
  have hinj : Set.InjOn code fiber := by
    rintro ⟨l, q⟩ hr ⟨l', q'⟩ hr' he
    have hpre := (Finset.mem_filter.mp hr).2
    have hpre' := (Finset.mem_filter.mp hr').2
    have hcode := Prod.mk.inj he
    have hsame : secondBlockPrefix slots s R seed K Tsec Z ξ first ⟨l, q⟩ =
        secondBlockPrefix slots s R seed K Tsec Z ξ first ⟨l', q'⟩ := hpre.trans hpre'.symm
    have hfst : first l = first l' := congrArg Sigma.fst hsame
    have hl : l = l' := hfirst (Prod.ext hfst hcode.1)
    subst hl
    have hlabel : actualSecondArithmeticLabel (s l) (R l) (seed l) (K l) (Tsec l) Z ξ q =
        actualSecondArithmeticLabel (s l) (R l) (seed l) (K l) (Tsec l) Z ξ q' :=
      eq_of_heq (Sigma.mk.inj hsame).2
    have hq := actual_second_label_dyad_injective (s l) (R l) (seed l) (K l) (Tsec l) Z ξ
      (Prod.ext hlabel hcode.2)
    rw [hq]
  have hcard := Finset.card_le_card_of_injOn code hmaps hinj
  rw [Finset.card_product] at hcard
  exact_mod_cast hcard

omit [Fintype α] [DecidableEq α] in
/-- The rows of the second expansion over one child prefix whose first common ideal has norm at most `Z^B`: at most
`Kc Z^ε` times the dyad box. The constant precedes `Z`, the labels, the rows and the prefix. -/
theorem second_block_rows_per_prefix_small_nok (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ {Label : Type*} [Fintype Label]
      (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
      (R seed : Label → Ideal O) (_hseed : ∀ l, Squarefree (seed l))
      (_hz₁ : ∀ l, (s l).W₁ 0 = 0) (_hz₂ : ∀ l, (s l).W₂ 0 = 0)
      (K Tsec : Label → ℝ) (ξ : ℝ) (first : Label → FirstSourceLabel),
      Function.Injective (fun l => (first l, seed l)) →
      ∀ (rows : Finset ((l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ))
        (box : Finset (Fin 4 → ℤ)),
      (∀ r ∈ rows, actualSecondDyad (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2 ∈ box) →
      ∀ p : ChildPrefix, p.2.1.1 ≠ ⊥ → (p.2.1.1.absNorm : ℝ) ≤ Z ^ B →
      ((rows.filter (fun r => secondBlockPrefix slots s R seed K Tsec Z ξ first r = p)).card : ℝ) ≤
        Kc * Z ^ ε * box.card := by
  let δ := ε / (B + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨Kc, hKc, hbound⟩ := SquarefreeDivisorBound.squarefree_divisor_small_power δ hδ
  refine ⟨Kc, hKc, ?_⟩
  intro Z hZ Label _ slots s R seed hseed hz₁ hz₂ K Tsec ξ first hfirst rows box hbox p hp hnorm
  have hrows := second_block_rows_per_prefix_nok slots s R seed hseed hz₁ hz₂ K Tsec Z ξ first hfirst rows box
    hbox p hp
  have he : B * δ ≤ ε := by
    have hid : δ * (B + 1) = ε := by dsimp only [δ]; field_simp
    nlinarith
  have hdiv : (((idealDivisors p.2.1.1).filter Squarefree).card : ℝ) ≤ Kc * Z ^ ε :=
    calc (((idealDivisors p.2.1.1).filter Squarefree).card : ℝ)
        ≤ Kc * (p.2.1.1.absNorm : ℝ) ^ δ := hbound _ hp
      _ ≤ Kc * (Z ^ B) ^ δ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hδ.le) hKc.le
      _ = Kc * Z ^ (B * δ) := by rw [← Real.rpow_mul (zero_le_one.trans hZ)]
      _ ≤ Kc * Z ^ ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he) hKc.le
  exact hrows.trans (mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg _))

/-- The number of elements of the subtype of a finset with a property is the number of elements of the finset with
that property. -/
theorem card_univ_filter_subtype {ρ : Type*} (rows : Finset ρ) (P : ρ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset rows).filter (fun r => P r.val)).card = (rows.filter P).card := by
  refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
  · intro r hr
    exact Finset.mem_filter.mpr ⟨r.property, (Finset.mem_filter.mp hr).2⟩
  · intro r₁ _ r₂ _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩, rfl⟩

/-- The rows of the second expansion of the children of the first labels, whose first labels have a missing radical of
norm at most `Z^cap`, over one ideal `D` of their multipliers: at most `Capre Z^ε Z^cap` times the dyad box. The
constant `Capre` precedes `Z`, the labels, the rows, the fixed row `u₀` and the units. The rows satisfy the support
and norm bounds of the prefix count: the first labels and the second pairs have norms at most `Z^B`, and so has the
product of the multiplier with the missing radical. -/
theorem facts_rows_over_ideal (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Capre : ℝ, 0 < Capre ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ {Label : Type*} [Fintype Label]
      (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
      (R seed : Label → Ideal O) (_hseed : ∀ l, Squarefree (seed l))
      (_hz₁ : ∀ l, (s l).W₁ 0 = 0) (_hz₂ : ∀ l, (s l).W₂ 0 = 0)
      (K Tsec : Label → ℝ) (ξ : ℝ) (first : Label → FirstSourceLabel),
      Function.Injective (fun l => (first l, seed l)) →
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (rows : Finset ((l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ))
        (box : Finset (Fin 4 → ℤ)),
      (∀ r ∈ rows, actualSecondDyad (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2 ∈ box) →
      (∀ r ∈ rows, Supported (first r.1).1.1 ∧ Supported (first r.1).1.2 ∧
        primeSupport (first r.1).1.1 = primeSupport (first r.1).1.2 ∧
        ((first r.1).1.1.absNorm : ℝ) ≤ Z ^ B ∧ ((first r.1).1.2.absNorm : ℝ) ≤ Z ^ B) →
      (∀ r ∈ rows, Supported r.2.1.val.val.1 ∧ Supported r.2.1.val.val.2 ∧
        primeSupport r.2.1.val.val.1 = primeSupport r.2.1.val.val.2 ∧
        (r.2.1.val.val.1.absNorm : ℝ) ≤ Z ^ B ∧ (r.2.1.val.val.2.absNorm : ℝ) ≤ Z ^ B) →
      (∀ r ∈ rows, firstRowMultiplier first left u₀ unit r ≠ 0 ∧
        ((Ideal.span {firstRowMultiplier first left u₀ unit r} * firstSourceMissing left (first r.1)).absNorm : ℝ) ≤
          Z ^ B) →
      ∀ (cap : ℝ) (D : Ideal O),
      ((rows.filter (fun r => Real.logb Z ((firstSourceMissing left (first r.1)).absNorm : ℝ) ≤ cap ∧
        Ideal.span {firstRowMultiplier first left u₀ unit r} = D)).card : ℝ) ≤
        Capre * (box.card : ℝ) * Z ^ ε * Z ^ cap := by
  obtain ⟨Kc, hKc, hper⟩ := second_block_rows_per_prefix_small_nok (α := α) B (ε / 2) hB (by positivity)
  obtain ⟨C, hC, hfib⟩ := child_prefix_fiber_bound B (ε / 2) hB (by positivity)
  refine ⟨C * Kc, mul_pos hC hKc, ?_⟩
  intro Z hZ Label _ slots s R seed hseed hz₁ hz₂ K Tsec ξ first hfirst left u₀ unit rows box hbox hfg hsg hmult
    cap D
  have hZ0 : 0 < Z := by linarith
  let pre := secondBlockPrefix slots s R seed K Tsec Z ξ first
  obtain ⟨rows', hrows'⟩ : ∃ rows' : Finset ((l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l)
      (Tsec l) Z ξ), rows' = rows.filter
        (fun r => Real.logb Z ((firstSourceMissing left (first r.1)).absNorm : ℝ) ≤ cap) := ⟨_, rfl⟩
  have hsub : rows' ⊆ rows := by
    rw [hrows']
    exact Finset.filter_subset _ _
  have hcap : ∀ r ∈ rows', Real.logb Z ((firstSourceMissing left (first r.1)).absNorm : ℝ) ≤ cap := by
    intro r hr
    rw [hrows'] at hr
    exact (Finset.mem_filter.mp hr).2
  have hpre1 : ∀ r : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ,
      (pre r).1 = first r.1 := fun r => rfl
  have hpre2 : ∀ r : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ,
      (pre r).2.1.1 = r.2.1.val.val.1 ∧ (pre r).2.1.2 = r.2.1.val.val.2 :=
    fun r => ⟨rfl, rfl⟩
  have hmem : ∀ p ∈ rows'.image pre, ∃ r ∈ rows', pre r = p := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨r, hr, rfl⟩
  -- the rows over one prefix
  have hF : ∀ p ∈ rows'.image pre, ((rows'.filter (fun r => pre r = p)).card : ℝ) ≤
      Kc * Z ^ (ε / 2) * box.card := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    have hr' := hsub hr
    have hs := hsg r hr'
    have hne : (pre r).2.1.1 ≠ ⊥ := by
      rw [(hpre2 r).1]
      exact hs.1.1
    exact hper Z (by linarith) slots s R seed hseed hz₁ hz₂ K Tsec ξ first hfirst rows' box
      (fun r hr => hbox r (hsub hr)) (pre r) hne (by rw [(hpre2 r).1]; exact hs.2.2.2.1)
  have hF0 : 0 ≤ Kc * Z ^ (ε / 2) * box.card :=
    mul_nonneg (mul_nonneg hKc.le (Real.rpow_nonneg hZ0.le _)) (Nat.cast_nonneg _)
  have hrows := rows_over_ideal_card rows' pre (childMultiplier left u₀ unit) _ hF0 hF D
  -- the prefixes over the ideal
  have hprefix := hfib left u₀ unit Z hZ cap (rows'.image pre) ?_ ?_ ?_ ?_ ?_ ?_ D
  · have hEq : rows.filter (fun r => Real.logb Z ((firstSourceMissing left (first r.1)).absNorm : ℝ) ≤ cap ∧
        Ideal.span {firstRowMultiplier first left u₀ unit r} = D) =
        rows'.filter (fun r => Ideal.span {childMultiplier left u₀ unit (pre r)} = D) := by
      rw [hrows', Finset.filter_filter]
      rfl
    calc ((rows.filter (fun r => Real.logb Z ((firstSourceMissing left (first r.1)).absNorm : ℝ) ≤ cap ∧
          Ideal.span {firstRowMultiplier first left u₀ unit r} = D)).card : ℝ)
        = ((rows'.filter (fun r => Ideal.span {childMultiplier left u₀ unit (pre r)} = D)).card : ℝ) := by
          rw [hEq]
      _ ≤ _ := hrows
      _ ≤ (C * Z ^ (cap + ε / 2)) * (Kc * Z ^ (ε / 2) * box.card) :=
          mul_le_mul_of_nonneg_right hprefix hF0
      _ = C * Kc * (box.card : ℝ) * Z ^ ε * Z ^ cap := by
          have h1 : Z ^ (cap + ε / 2) * Z ^ (ε / 2) = Z ^ ε * Z ^ cap := by
            rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
            congr 1
            ring
          calc (C * Z ^ (cap + ε / 2)) * (Kc * Z ^ (ε / 2) * box.card)
              = C * Kc * (box.card : ℝ) * (Z ^ (cap + ε / 2) * Z ^ (ε / 2)) := by ring
            _ = _ := by rw [h1]; ring
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    have h := (hmult r (hsub hr)).2
    refine ⟨(hmult r (hsub hr)).1, ?_⟩
    have hmiss := (first_missing_norm_le left (first r.1) (hfg r (hsub hr)).1 (hfg r (hsub hr)).2.1).1
    have hle : (Ideal.span {childMultiplier left u₀ unit (pre r)}).absNorm ≤
        (Ideal.span {childMultiplier left u₀ unit (pre r)} * firstSourceMissing left (first r.1)).absNorm := by
      rw [map_mul]
      exact Nat.le_mul_of_pos_right _ hmiss
    exact le_trans (by exact_mod_cast hle) h
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    have hf := hfg r (hsub hr)
    have hs := hsg r (hsub hr)
    exact ⟨hf.1, hf.2.1.1, hs.1, hs.2.1.1⟩
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    exact ⟨(hfg r (hsub hr)).2.2.1, (hsg r (hsub hr)).2.2.1⟩
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    exact (hmult r (hsub hr)).2
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    exact ⟨(hfg r (hsub hr)).2.2.2.1, (hfg r (hsub hr)).2.2.2.2, (hsg r (hsub hr)).2.2.2.1,
      (hsg r (hsub hr)).2.2.2.2⟩
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    have hmiss := (first_missing_norm_le left (first r.1) (hfg r (hsub hr)).1 (hfg r (hsub hr)).2.1).1
    have hposR : (0 : ℝ) < ((firstSourceMissing left (first r.1)).absNorm : ℝ) := by exact_mod_cast hmiss
    exact (Real.logb_le_iff_le_rpow (by linarith) hposR).mp (hcap r hr)

end
end OAI.SevenEighths.Cycle63InitialMass
