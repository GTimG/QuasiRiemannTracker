/- The returned HIGH parts of many rows, each paid pointwise against one target, summed by binning the classes in the
row norm, the missing radicals of both levels and the zero parameter and counting each bin jointly over the rows and
the second-level labels. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.DepthTwoHighCount
import Candidate.Cycle63.Physical.InitialMass.DepthTwoBins

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment IdealMobiusDivisorSum LocalMoment ProbePhysical
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- On `[0, 3/4]` the unmarked density decreases, lies in `[0, 1]`, and drops by at most twice the increase of its
argument. -/
theorem unmarkedDensity_lipschitz {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁₂ : δ₁ ≤ δ₂) (h₂ : δ₂ ≤ 3/4) :
    unmarkedDensity δ₂ ≤ unmarkedDensity δ₁ ∧ unmarkedDensity δ₁ - unmarkedDensity δ₂ ≤ 2*(δ₂ - δ₁) ∧
      0 ≤ unmarkedDensity δ₂ ∧ unmarkedDensity δ₁ ≤ 1 := by
  have ha : 0 < 3*(5 - 2*δ₁) := by linarith
  have hb : 0 < 3*(5 - 2*δ₂) := by linarith
  have key : 10*δ₂/(3*(5 - 2*δ₂)) - 10*δ₁/(3*(5 - 2*δ₁)) =
      (10*δ₂*(3*(5 - 2*δ₁)) - 3*(5 - 2*δ₂)*(10*δ₁))/(3*(5 - 2*δ₂)*(3*(5 - 2*δ₁))) :=
    div_sub_div _ _ hb.ne' ha.ne'
  have hnum : 10*δ₂*(3*(5 - 2*δ₁)) - 3*(5 - 2*δ₂)*(10*δ₁) = 150*(δ₂ - δ₁) := by ring
  have hden : 0 < 3*(5 - 2*δ₂)*(3*(5 - 2*δ₁)) := mul_pos hb ha
  have hdiff : 0 ≤ δ₂ - δ₁ := sub_nonneg.mpr h₁₂
  have hprod : 150 ≤ 2*(3*(5 - 2*δ₂)*(3*(5 - 2*δ₁))) := by nlinarith
  have hupper : 150*(δ₂ - δ₁)/(3*(5 - 2*δ₂)*(3*(5 - 2*δ₁))) ≤ 2*(δ₂ - δ₁) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hlower : 0 ≤ 150*(δ₂ - δ₁)/(3*(5 - 2*δ₂)*(3*(5 - 2*δ₁))) := div_nonneg (by linarith) hden.le
  have hρ₂ := unmarkedDensity_ge_two_sevenths h₂
  have hfrac : 0 ≤ 10*δ₁/(3*(5 - 2*δ₁)) := div_nonneg (by linarith) ha.le
  rw [hnum] at key
  unfold unmarkedDensity at hρ₂ ⊢
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The missing radical of a first-source label is a nonzero ideal: it divides the common radical. -/
theorem firstSourceMissing_ne_zero (left : Bool) (l : FirstSourceLabel) : firstSourceMissing left l ≠ 0 := by
  intro h0
  apply CenteredMomentRankinRadical.commonRadical_ne_zero l.1.1 l.1.2
  rw [actual_first_radical_partition l.1.1 l.1.2 l.2.val l.2.property left]
  change _*firstSourceMissing left l = 0
  rw [h0, mul_zero]

section Clip
variable {M H hH}
variable {Base : Type} {base : Base → Character} {η₀ : Character} {Z B T : ℝ} {left : Bool} {v₁ : O}
  {unit : FirstSourceLabel → O}

/-- The row of a label and its missing radical each have norm at most `Z^B`. -/
theorem _root_.OAI.SevenEighths.Cycle63Moment.SecondStepHighCount.caps
    (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) (σ : R.Class)
    (ℓ : NonzeroJointSourceLabel left v₁ unit) (hℓ : ℓ ∈ R.labels σ) :
    rawFrequencyNorm (nonzeroJointSourceRow ℓ) ≤ Z^B ∧
      ((firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^B := by
  have hcap := R.row_cap σ ℓ hℓ
  rw [map_mul, Nat.cast_mul] at hcap
  have hrow : (1 : ℝ) ≤ ((Ideal.span {jointSourceRow left v₁ unit ℓ.val}).absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr ℓ.property))
  have hmiss : (1 : ℝ) ≤ ((firstSourceMissing left ℓ.val.1).absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (firstSourceMissing_ne_zero left ℓ.val.1))
  constructor
  · change ((Ideal.span {jointSourceRow left v₁ unit ℓ.val}).absNorm : ℝ) ≤ Z^B
    nlinarith
  · nlinarith

/-- A class with a label has nonnegative row-norm and missing-radical parameters. -/
theorem _root_.OAI.SevenEighths.Cycle63Moment.SecondStepHighCount.exponents_nonneg
    (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit)
    (hZ : 1 < Z) (σ : R.Class) (hσ : (R.labels σ).Nonempty) : 0 ≤ R.rowExp σ ∧ 0 ≤ R.missExp σ := by
  obtain ⟨ℓ, hℓ⟩ := hσ
  have hrow : (1 : ℝ) ≤ rawFrequencyNorm (nonzeroJointSourceRow ℓ) := by
    change (1 : ℝ) ≤ ((Ideal.span {jointSourceRow left v₁ unit ℓ.val}).absNorm : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr ℓ.property))
  have hmiss : (1 : ℝ) ≤ ((firstSourceMissing left ℓ.val.1).absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (firstSourceMissing_ne_zero left ℓ.val.1))
  constructor
  · by_contra hneg
    push Not at hneg
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg hZ hneg
    linarith [R.row_le σ ℓ hℓ]
  · by_contra hneg
    push Not at hneg
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg hZ hneg
    linarith [R.missing_le σ ℓ hℓ]

/-- The HIGH part with its row-norm and missing-radical parameters clipped to `[0, B]`. -/
def _root_.OAI.SevenEighths.Cycle63Moment.SecondStepHighCount.clip
    (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) (hZ : 1 ≤ Z)
    (hB : 0 ≤ B) : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit where
  Class := R.Class
  labels := R.labels
  exponent := R.exponent
  rowExp := fun σ => max 0 (min (R.rowExp σ) B)
  missExp := fun σ => max 0 (min (R.missExp σ) B)
  zeroBin := R.zeroBin
  witness := R.witness
  zero_le := R.zero_le
  row_le := by
    intro σ ℓ hℓ
    rcases le_total (R.rowExp σ) B with h | h
    · rw [min_eq_left h]
      exact (R.row_le σ ℓ hℓ).trans (Real.rpow_le_rpow_of_exponent_le hZ (le_max_right _ _))
    · rw [min_eq_right h, max_eq_right hB]
      exact (R.caps σ ℓ hℓ).1
  supported := R.supported
  same_support := R.same_support
  row_cap := R.row_cap
  ideal_cap := R.ideal_cap
  missing_le := by
    intro σ ℓ hℓ
    rcases le_total (R.missExp σ) B with h | h
    · rw [min_eq_left h]
      exact (R.missing_le σ ℓ hℓ).trans (Real.rpow_le_rpow_of_exponent_le hZ (le_max_right _ _))
    · rw [min_eq_right h, max_eq_right hB]
      exact (R.caps σ ℓ hℓ).2

end Clip

/-- The weight of a class in a bin. From the pointwise payment of the class and the edges of its bin (row norm and
missing radical clipped to `[0, B]`, zero parameter above `4/5` and at most one width above the bin's), the row weight
times `Z` to the class exponent is at most `Z` to the target plus the bin loss `width (3 + 4B)` minus the bin's count
exponent. -/
theorem bin_weight_bound {Z W e m q a u Etarget width B qk mk ak uk q' m' : ℝ} (hZ : 1 < Z) (hwidth : 0 < width)
    (hp : W*Z^(e + m + unmarkedDensity (2*a - 1)*q + u) ≤ Z^Etarget)
    (hqk : qk ≤ q' + width) (hq'q : q' ≤ q) (hq'0 : 0 ≤ q') (hq'B : q' ≤ B)
    (hmk : mk ≤ m' + width) (hm'm : m' ≤ m) (huk : uk ≤ u + width)
    (hak : ak ≤ a) (hakl : a - width ≤ ak) (ha45 : 4/5 ≤ ak) (ha78 : a ≤ 7/8) :
    W*Z^e ≤ Z^(Etarget + width*(3 + 4*B) - (mk + qk*unmarkedDensity (2*ak - 1) + uk)) := by
  have hZ0 : 0 < Z := by linarith
  have hlip := unmarkedDensity_lipschitz (δ₁ := 2*ak - 1) (δ₂ := 2*a - 1) (by linarith) (by linarith) (by linarith)
  set ρk := unmarkedDensity (2*ak - 1) with hρkdef
  set ρσ := unmarkedDensity (2*a - 1) with hρσdef
  have hρσ0 : 0 ≤ ρσ := hlip.2.2.1
  have hρk1 : ρk ≤ 1 := hlip.2.2.2
  have hρk0 : 0 ≤ ρk := hρσ0.trans hlip.1
  have hρk : ρk ≤ ρσ + 4*width := by linarith only [hlip.2.1, hakl]
  have e₁ := mul_le_mul_of_nonneg_right hqk hρk0
  have e₂ := mul_le_mul_of_nonneg_left hρk hq'0
  have e₃ := mul_le_mul_of_nonneg_left hρk1 hwidth.le
  have e₄ := mul_le_mul_of_nonneg_right hq'B (by linarith : (0 : ℝ) ≤ 4*width)
  have e₅ := mul_le_mul_of_nonneg_left hq'q hρσ0
  have hX : mk + qk*ρk + uk ≤ m + ρσ*q + u + width*(3 + 4*B) := by
    linarith only [e₁, e₂, e₃, e₄, e₅, hmk, hm'm, huk]
  have hsplit : W*Z^e = W*Z^(e + m + ρσ*q + u)*Z^(-(m + ρσ*q + u)) := by
    rw [mul_assoc, ← Real.rpow_add hZ0, show e + m + ρσ*q + u + -(m + ρσ*q + u) = e by ring]
  rw [hsplit]
  calc W*Z^(e + m + ρσ*q + u)*Z^(-(m + ρσ*q + u))
      ≤ Z^Etarget*Z^(-(m + ρσ*q + u)) := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hZ0.le _)
    _ = Z^(Etarget - (m + ρσ*q + u)) := by rw [← Real.rpow_add hZ0, sub_eq_add_neg]
    _ ≤ Z^(Etarget + width*(3 + 4*B) - (mk + qk*ρk + uk)) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hX])

/-- The returned HIGH parts of the rows of a finite set, one per orientation of the second level and row, with
row weights `W r` and first-level missing radicals `miss r ∈ [0, B]`. Premises: the rows over one ideal of their
multipliers with first-level missing radical at most `Z^m₁` number at most `Apre Z^m₁`; a row has at most `K` classes;
the zero parameters lie in `[4/5, 7/8]`; and every class is paid pointwise: the row weight times `Z` to the class
exponent, the missing radical, the density times the row norm and the first-level missing radical is at most
`Z^Etarget`. Then the weighted sum of the count forms is at most `C (1+T)^J Apre K Z^(Etarget + loss)` up to the bin
loss `width (3 + 4B)`. The height degree precedes the dictionary and the character, and the constants precede the
rows, their multipliers, units and HIGH parts and both heights. -/
theorem depth_two_returned_sum {Base : Type} [Fintype Base]
    (B loss width : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) (hwidth : 0 < width) :
    ∃ J : ℕ, ∀ (base : Base → Character) (η₀ : Character), ∃ C : ℝ, 0 < C ∧
      ∀ {P : Type*} (v : P → O) (unit : Bool → P → FirstSourceLabel → O) (Z T : ℝ), 2 ≤ Z → 0 ≤ T →
      ∀ R : ∀ b p, SecondStepHighCount M H hH base η₀ Z B T b (v p) (unit b p),
      ∀ (rows : Finset P) (W miss : P → ℝ) (Apre K Etarget : ℝ),
      (∀ r ∈ rows, 0 ≤ W r) → (∀ r ∈ rows, 0 ≤ miss r ∧ miss r ≤ B) → 0 ≤ Apre → 0 ≤ K →
      (∀ m₁ : ℝ, ∀ D : Ideal O,
        (((rows.filter (fun r => miss r ≤ m₁)).filter (fun r => Ideal.span {v r} = D)).card : ℝ) ≤ Apre*Z^m₁) →
      (∀ b, ∀ r ∈ rows, (Fintype.card (R b r).Class : ℝ) ≤ K) →
      (∀ b, ∀ r ∈ rows, ∀ σ, 4/5 ≤ (R b r).zeroBin σ ∧ (R b r).zeroBin σ ≤ 7/8) →
      (∀ b, ∀ r ∈ rows, ∀ σ, W r*Z^((R b r).exponent σ + (R b r).missExp σ +
        unmarkedDensity (2*(R b r).zeroBin σ - 1)*(R b r).rowExp σ + miss r) ≤ Z^Etarget) →
        ∑ r ∈ rows, W r*∑ b, (R b r).value ≤ C*(1+T)^J*Apre*K*Z^(Etarget + width*(3 + 4*B) + loss) := by
  obtain ⟨J, hJ⟩ := second_step_high_selection_count (Base := Base) M H hH B loss hB hloss
  let NB : ℕ := (Finset.Icc (⌊-(B + 1)/width⌋ : ℤ) ⌊(B + 1)/width⌋).card^4
  have hNB : (0 : ℝ) ≤ NB := Nat.cast_nonneg _
  refine ⟨J, fun base η₀ => ?_⟩
  obtain ⟨C, hC, hcount⟩ := hJ base η₀
  refine ⟨2*((NB : ℝ) + 1)*C, by positivity, ?_⟩
  intro P v unit Z T hZ hT R rows W miss Apre K Etarget hW hmiss hApre hK hpre hcard hzero hpay
  have hZ1 : 1 < Z := by linarith
  have hZ0 : 0 < Z := by linarith
  let loss' := width*(3 + 4*B)
  let E := C*(1+T)^J*Apre*K*Z^(Etarget + loss' + loss)
  have hE : 0 ≤ E := by
    have hT1 : 0 ≤ 1 + T := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le (pow_nonneg hT1 _)) hApre) hK)
      (Real.rpow_nonneg hZ0.le _)
  have horient : ∀ b : Bool, ∑ r ∈ rows, W r*(R b r).value ≤ NB*E := by
    intro b
    let Rc : ∀ p, SecondStepHighCount M H hH base η₀ Z B T b (v p) (unit b p) :=
      fun p => (R b p).clip hZ1.le hB
    let full : Finset (Σ p, (R b p).Class) := rows.sigma (fun p => (Finset.univ : Finset (R b p).Class))
    let S := full.filter (fun x => ((R b x.1).labels x.2).Nonempty)
    let f : (Σ p, (R b p).Class) → ℝ := fun x => W x.1*(Z^((R b x.1).exponent x.2)*((R b x.1).labels x.2).card)
    let coord : (Σ p, (R b p).Class) → Fin 4 → ℝ := fun x =>
      ![(Rc x.1).rowExp x.2, (Rc x.1).missExp x.2, (R b x.1).zeroBin x.2, miss x.1]
    have hsum : ∑ r ∈ rows, W r*(R b r).value = ∑ x ∈ S, f x := by
      have h1 : ∑ r ∈ rows, W r*(R b r).value = ∑ x ∈ full, f x := by
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        unfold SecondStepHighCount.value
        rw [Finset.mul_sum]
      rw [h1]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hxfull hx
      have hempty : (R b x.1).labels x.2 = ∅ := by
        by_contra hne
        exact hx (Finset.mem_filter.mpr ⟨hxfull, Finset.nonempty_iff_ne_empty.mpr hne⟩)
      simp only [f, hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
    have hbox : ∀ x ∈ S, ∀ i, -(B + 1) ≤ coord x i ∧ coord x i ≤ B + 1 := by
      intro x hx i
      have hx' := Finset.mem_sigma.mp (Finset.mem_filter.mp hx).1
      have hz := hzero b x.1 hx'.1 x.2
      have hm := hmiss x.1 hx'.1
      have hq0 : 0 ≤ max 0 (min ((R b x.1).rowExp x.2) B) := le_max_left _ _
      have hq1 : max 0 (min ((R b x.1).rowExp x.2) B) ≤ B := max_le hB (min_le_right _ _)
      have hm0 : 0 ≤ max 0 (min ((R b x.1).missExp x.2) B) := le_max_left _ _
      have hm1 : max 0 (min ((R b x.1).missExp x.2) B) ≤ B := max_le hB (min_le_right _ _)
      have c0 : -(B + 1) ≤ coord x 0 ∧ coord x 0 ≤ B + 1 := by
        change -(B + 1) ≤ max 0 (min ((R b x.1).rowExp x.2) B) ∧ max 0 (min ((R b x.1).rowExp x.2) B) ≤ B + 1
        constructor <;> linarith
      have c1 : -(B + 1) ≤ coord x 1 ∧ coord x 1 ≤ B + 1 := by
        change -(B + 1) ≤ max 0 (min ((R b x.1).missExp x.2) B) ∧ max 0 (min ((R b x.1).missExp x.2) B) ≤ B + 1
        constructor <;> linarith
      have c2 : -(B + 1) ≤ coord x 2 ∧ coord x 2 ≤ B + 1 := by
        change -(B + 1) ≤ (R b x.1).zeroBin x.2 ∧ (R b x.1).zeroBin x.2 ≤ B + 1
        constructor <;> linarith
      have c3 : -(B + 1) ≤ coord x 3 ∧ coord x 3 ≤ B + 1 := by
        change -(B + 1) ≤ miss x.1 ∧ miss x.1 ≤ B + 1
        constructor <;> linarith
      fin_cases i
      exacts [c0, c1, c2, c3]
    rw [hsum]
    refine binned_sum_le S coord f width (B + 1) E hwidth hE hbox ?_
    intro key hkey
    let qk := min (exponentBinUpper width key 0) B
    let mk := exponentBinUpper width key 1
    let ak := max (4/5) (exponentBinLower width key 2)
    let uk := exponentBinUpper width key 3
    let ρk := unmarkedDensity (2*ak - 1)
    let Sk := S.filter (fun x => exponentBin width (coord x) = key)
    have hedges : ∀ x ∈ Sk, ∀ i, exponentBinLower width key i ≤ coord x i ∧
        coord x i ≤ exponentBinUpper width key i ∧
        exponentBinUpper width key i = exponentBinLower width key i + width := by
      intro x hx i
      have hk := (Finset.mem_filter.mp hx).2
      have h := exponent_bin_edges width hwidth (coord x) i
      rw [hk] at h
      exact h
    have hmemS : ∀ x ∈ Sk, x.1 ∈ rows ∧ ((R b x.1).labels x.2).Nonempty := by
      intro x hx
      have hxS := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
      exact ⟨(Finset.mem_sigma.mp hxS.1).1, hxS.2⟩
    have hclass : ∀ x ∈ Sk, (Rc x.1).rowExp x.2 ≤ qk ∧ (Rc x.1).missExp x.2 ≤ mk ∧
        ak ≤ (Rc x.1).zeroBin x.2 := by
      intro x hx
      have h0 := hedges x hx 0
      have h1 := hedges x hx 1
      have h2 := hedges x hx 2
      have hz := hzero b x.1 (hmemS x hx).1 x.2
      have hq1 : max 0 (min ((R b x.1).rowExp x.2) B) ≤ B := max_le hB (min_le_right _ _)
      exact ⟨le_min h0.2.1 hq1, h1.2.1, max_le hz.1 h2.1⟩
    obtain ⟨x₀, hx₀, hkx₀⟩ := Finset.mem_image.mp hkey
    have hx₀k : x₀ ∈ Sk := Finset.mem_filter.mpr ⟨hx₀, hkx₀⟩
    have hak : 4/5 ≤ ak := le_max_left _ _
    have hak' : ak ≤ 7/8 := (hclass x₀ hx₀k).2.2.trans (hzero b x₀.1 (hmemS x₀ hx₀k).1 x₀.2).2
    have hpre' : ∀ D : Ideal O, ((Sk.filter (fun x => Ideal.span {v x.1} = D)).card : ℝ) ≤ Apre*Z^uk*K := by
      intro D
      have hS : ∀ x ∈ Sk, x.1 ∈ rows.filter (fun r => miss r ≤ uk) :=
        fun x hx => Finset.mem_filter.mpr ⟨(hmemS x hx).1, (hedges x hx 3).2.1⟩
      have hKp : ∀ p ∈ rows.filter (fun r => miss r ≤ uk), ((Sk.filter (fun x => x.1 = p)).card : ℝ) ≤ K := by
        intro p hp
        have hsub : Sk.filter (fun x => x.1 = p) ⊆
            (Finset.univ : Finset (R b p).Class).image (fun σ => (⟨p, σ⟩ : Σ p, (R b p).Class)) := by
          intro x hx
          have hp' := (Finset.mem_filter.mp hx).2
          obtain ⟨y₁, y₂⟩ := x
          simp only at hp'
          subst hp'
          exact Finset.mem_image.mpr ⟨y₂, Finset.mem_univ _, rfl⟩
        have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
        rw [Finset.card_univ] at hc
        exact (Nat.cast_le.mpr hc).trans (hcard b p (Finset.mem_filter.mp hp).1)
      have hsel := selected_classes_over_ideal v (rows.filter (fun r => miss r ≤ uk)) Sk K hS hKp D
      exact hsel.trans (mul_le_mul_of_nonneg_right (hpre uk D) hK)
    have hcountk : (∑ x ∈ Sk, (((R b x.1).labels x.2).card : ℝ)) ≤
        C*(1+T)^J*Z^(mk + qk*ρk + loss)*(Apre*Z^uk*K) :=
      hcount v b (unit b) Z T hZ hT Rc Sk qk mk ak (Apre*Z^uk*K) (min_le_right _ _) hak hak' hpre' hclass
    -- the pointwise bound of a weight in the bin
    have hweight : ∀ x ∈ Sk, W x.1*Z^((R b x.1).exponent x.2) ≤ Z^(Etarget + loss' - (mk + qk*ρk + uk)) := by
      intro x hx
      have hr := (hmemS x hx).1
      have hne := (R b x.1).exponents_nonneg hZ1 x.2 (hmemS x hx).2
      have hz := hzero b x.1 hr x.2
      have h0 := hedges x hx 0
      have h1 := hedges x hx 1
      have h2 := hedges x hx 2
      have h3 := hedges x hx 3
      have hlo0 : exponentBinLower width key 0 ≤ max 0 (min ((R b x.1).rowExp x.2) B) := h0.1
      have hup0 : max 0 (min ((R b x.1).rowExp x.2) B) ≤ exponentBinUpper width key 0 := h0.2.1
      have hlo1 : exponentBinLower width key 1 ≤ max 0 (min ((R b x.1).missExp x.2) B) := h1.1
      have hlo2 : exponentBinLower width key 2 ≤ (R b x.1).zeroBin x.2 := h2.1
      have hup2 : (R b x.1).zeroBin x.2 ≤ exponentBinUpper width key 2 := h2.2.1
      have hlo3 : exponentBinLower width key 3 ≤ miss x.1 := h3.1
      have hqk : qk ≤ max 0 (min ((R b x.1).rowExp x.2) B) + width := by
        have := min_le_left (exponentBinUpper width key 0) B
        linarith only [this, h0.2.2, hlo0]
      have hakl : (R b x.1).zeroBin x.2 - width ≤ ak := by
        have := le_max_right (4/5 : ℝ) (exponentBinLower width key 2)
        linarith only [this, h2.2.2, hup2]
      exact bin_weight_bound hZ1 hwidth (hpay b x.1 hr x.2) hqk (max_le hne.1 (min_le_left _ _)) (le_max_left _ _)
        (max_le hB (min_le_right _ _)) (by linarith only [h1.2.2, hlo1]) (max_le hne.2 (min_le_left _ _))
        (by linarith only [h3.2.2, hlo3]) (hclass x hx).2.2 hakl (le_max_left _ _) hz.2
    have hsplit : ∑ x ∈ Sk, f x = ∑ x ∈ Sk, (W x.1*Z^((R b x.1).exponent x.2))*((R b x.1).labels x.2).card := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [f]
      ring
    rw [hsplit]
    have hwc := weighted_count_le Sk (fun x => W x.1*Z^((R b x.1).exponent x.2))
      (fun x => (((R b x.1).labels x.2).card : ℝ)) (Z^(Etarget + loss' - (mk + qk*ρk + uk)))
      (fun x _ => Nat.cast_nonneg _) hweight
    have hexp : Z^(Etarget + loss' - (mk + qk*ρk + uk))*Z^(mk + qk*ρk + loss)*Z^uk = Z^(Etarget + loss' + loss) := by
      rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
      congr 1
      ring
    calc ∑ x ∈ Sk, (W x.1*Z^((R b x.1).exponent x.2))*((R b x.1).labels x.2).card
        ≤ Z^(Etarget + loss' - (mk + qk*ρk + uk))*∑ x ∈ Sk, (((R b x.1).labels x.2).card : ℝ) := hwc
      _ ≤ Z^(Etarget + loss' - (mk + qk*ρk + uk))*(C*(1+T)^J*Z^(mk + qk*ρk + loss)*(Apre*Z^uk*K)) :=
          mul_le_mul_of_nonneg_left hcountk (Real.rpow_nonneg hZ0.le _)
      _ = C*(1+T)^J*Apre*K*(Z^(Etarget + loss' - (mk + qk*ρk + uk))*Z^(mk + qk*ρk + loss)*Z^uk) := by ring
      _ = E := by rw [hexp]
  have hswap : ∑ r ∈ rows, W r*∑ b, (R b r).value = ∑ b, ∑ r ∈ rows, W r*(R b r).value := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.mul_sum]
  rw [hswap, Fintype.sum_bool]
  have ht := horient true
  have hf := horient false
  have hNE : (NB : ℝ)*E ≤ ((NB : ℝ) + 1)*E := mul_le_mul_of_nonneg_right (by linarith) hE
  calc ∑ r ∈ rows, W r*(R true r).value + ∑ r ∈ rows, W r*(R false r).value
      ≤ ((NB : ℝ) + 1)*E + ((NB : ℝ) + 1)*E := by linarith
    _ = 2*((NB : ℝ) + 1)*C*(1+T)^J*Apre*K*Z^(Etarget + width*(3 + 4*B) + loss) := by
        dsimp only [E, loss']
        ring

end
end OAI.SevenEighths.Cycle63InitialMass
