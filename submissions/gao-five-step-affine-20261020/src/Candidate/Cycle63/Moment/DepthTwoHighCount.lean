/- The second step's HIGH part for one child prefix in count form: finitely many classes of second-level joint labels,
each label with the witness of the joint count, and the count of the labels of the classes selected over many prefixes.
Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.DepthTwoHighRows

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily HeckeDetectorZeros LocalMoment ProbePhysical CanonicalQuadraticSieve IdealMobiusDivisorSum
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A HIGH witness at the nonzero row `w`: a natural state of any scale whose fixed modulus lies below `M` and below the
modulus of `η₀`, a kept row of the state with a natural row of its character, and a member of the dictionary `base`
with nonzero holes, such that the state's masked row character is the member's natural row at `w` masked by the
holes. -/
structure DepthTwoHighWitness {Base : Type} (base : Base → Character) (η₀ : Character) (w : NonzeroFrequency) where
  scale : ℝ
  maskBound : ℝ
  profileEdge : ℝ
  state : NaturalState scale maskBound profileEdge
  fixed_le_ray : state.fixedModulus ≤ M
  fixed_le_base : state.fixedModulus ≤ η₀.modulus
  row : O
  keep : state.radial.keep row
  natural : NaturalRow state.character row
  index : Base
  holes : Ideal O
  holes_ne : holes ≠ 0
  mask : ∀ I : Ideal O, idealCoeff (excluded natural.character state.puncture) I =
    idealCoeff (excluded (naturalRow (base index) w.val w.property).character holes) I

/-- The largest real part of a zero up to height `T` of the whole source family of the witness's masked character. -/
def DepthTwoHighWitness.zeroMax {Base : Type} {base : Base → Character} {η₀ : Character} {w : NonzeroFrequency}
    (W : DepthTwoHighWitness M base η₀ w) (T : ℝ) : ℝ :=
  zeroMaximum (wholeSourceFamily M H hH η₀ (excluded W.natural.character W.state.puncture))
    (whole_source_family_nonprincipal M H hH W.state η₀ W.fixed_le_ray W.fixed_le_base W.row W.keep W.natural) T

/-- The second step's HIGH part for one child prefix, in count form. The child multiplier `v₁` is the fixed row of the
second step, `left` its orientation and `unit` its units. A class `σ` has a finite set `labels σ` of second-level joint
labels, the exponent `exponent σ` of its count form, and the row-norm, missing-radical and zero parameters of its
labels. Each label of the class has a HIGH witness at its row whose whole source family has a zero of real part at
least `zeroBin σ` up to height `T`; its row has norm at most `Z^(rowExp σ)`; its common ideals are supported with equal
prime supports and norms at most `Z^B`; its row times its missing radical has norm at most `Z^B`; and its missing
radical has norm at most `Z^(missExp σ)`. -/
structure SecondStepHighCount {Base : Type} (base : Base → Character) (η₀ : Character) (Z B T : ℝ) (left : Bool)
    (v₁ : O) (unit : FirstSourceLabel → O) where
  Class : Type
  [classFintype : Fintype Class]
  labels : Class → Finset (NonzeroJointSourceLabel left v₁ unit)
  exponent : Class → ℝ
  rowExp : Class → ℝ
  missExp : Class → ℝ
  zeroBin : Class → ℝ
  witness : ∀ σ, ∀ ℓ ∈ labels σ, DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow ℓ)
  zero_le : ∀ σ ℓ (h : ℓ ∈ labels σ), zeroBin σ ≤ (witness σ ℓ h).zeroMax M H hH T
  row_le : ∀ σ, ∀ ℓ ∈ labels σ, rawFrequencyNorm (nonzeroJointSourceRow ℓ) ≤ Z^(rowExp σ)
  supported : ∀ σ, ∀ ℓ ∈ labels σ, Supported ℓ.val.1.1.1 ∧ ℓ.val.1.1.2 ≠ 0 ∧
    Supported ℓ.val.2.1.1 ∧ ℓ.val.2.1.2 ≠ 0
  same_support : ∀ σ, ∀ ℓ ∈ labels σ, primeSupport ℓ.val.1.1.1 = primeSupport ℓ.val.1.1.2 ∧
    primeSupport ℓ.val.2.1.1 = primeSupport ℓ.val.2.1.2
  row_cap : ∀ σ, ∀ ℓ ∈ labels σ,
    ((Ideal.span {jointSourceRow left v₁ unit ℓ.val}*firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^B
  ideal_cap : ∀ σ, ∀ ℓ ∈ labels σ, (ℓ.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (ℓ.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
    (ℓ.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (ℓ.val.2.1.2.absNorm : ℝ) ≤ Z^B
  missing_le : ∀ σ, ∀ ℓ ∈ labels σ, ((firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^(missExp σ)

attribute [instance] SecondStepHighCount.classFintype

/-- The HIGH part with no class. -/
def SecondStepHighCount.empty {Base : Type} (base : Base → Character) (η₀ : Character) (Z B T : ℝ) (left : Bool)
    (v₁ : O) (unit : FirstSourceLabel → O) : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit where
  Class := Empty
  labels := fun σ => σ.elim
  exponent := fun σ => σ.elim
  rowExp := fun σ => σ.elim
  missExp := fun σ => σ.elim
  zeroBin := fun σ => σ.elim
  witness := fun σ => σ.elim
  zero_le := fun σ => σ.elim
  row_le := fun σ => σ.elim
  supported := fun σ => σ.elim
  same_support := fun σ => σ.elim
  row_cap := fun σ => σ.elim
  ideal_cap := fun σ => σ.elim
  missing_le := fun σ => σ.elim

section Value
variable {M H hH}
variable {Base : Type} {base : Base → Character} {η₀ : Character} {Z B T : ℝ} {left : Bool} {v₁ : O}
  {unit : FirstSourceLabel → O}

/-- The count form of the HIGH part: over its classes, `Z` to the class exponent times the number of labels. -/
def SecondStepHighCount.value (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) : ℝ :=
  ∑ σ, Z^(R.exponent σ)*((R.labels σ).card : ℝ)

/-- The count form of a HIGH part is nonnegative. -/
theorem SecondStepHighCount.value_nonneg (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit)
    (hZ : 0 ≤ Z) : 0 ≤ R.value :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Real.rpow_nonneg hZ _) (Nat.cast_nonneg _))

/-- The HIGH part with no class has count form zero. -/
theorem SecondStepHighCount.empty_value :
    (SecondStepHighCount.empty M H hH base η₀ Z B T left v₁ unit).value = 0 := by
  unfold SecondStepHighCount.value
  exact Finset.sum_eq_zero (fun σ _ => Empty.elim σ)

/-- Every class pays the HIGH reserve of the parent of the second step. With `δ = 2 zeroBin σ - 1` in `[lo, 3/4]` and
`ρ` the unmarked density at `δ`, the class exponent relative to the energy scale `scale`, plus the missing radical and
`ρ` times the excess of the row norm over the norm of `v₁`, is at most `loss` minus the reserve
`scale (1 - ρ) - δ length - amp (5 - 6ρ)`. -/
def SecondStepHighCount.Pays (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit)
    (lo scale length amp loss : ℝ) : Prop :=
  ∀ σ, lo ≤ 2*R.zeroBin σ - 1 ∧ 2*R.zeroBin σ - 1 ≤ 3/4 ∧
    R.exponent σ - scale + R.missExp σ +
        unmarkedDensity (2*R.zeroBin σ - 1)*(R.rowExp σ - Real.logb Z ((Ideal.span {v₁}).absNorm : ℝ)) ≤
      loss - (scale*(1 - unmarkedDensity (2*R.zeroBin σ - 1)) - (2*R.zeroBin σ - 1)*length -
        amp*(5 - 6*unmarkedDensity (2*R.zeroBin σ - 1)))

end Value

/-- The joint row at the fixed row `v` is `v` times the joint row at the fixed row `1`. -/
theorem jointSourceRow_eq_mul (left : Bool) (v : O) (unit : FirstSourceLabel → O) (ℓ : JointSourceLabel) :
    jointSourceRow left v unit ℓ = v*jointSourceRow left 1 unit ℓ := by
  unfold jointSourceRow effectiveRow
  ring

/-- A mask identity at `v` times the joint row at the fixed row `1` is the mask identity at the row of the label with
the fixed row `v`. -/
theorem mask_at_multiplier_row (χ : Character) (left : Bool) (v : O) (unit : FirstSourceLabel → O)
    (ℓ : NonzeroJointSourceLabel left v unit) (hw : v*jointSourceRow left 1 unit ℓ.val ≠ 0) (holes I : Ideal O) :
    idealCoeff (excluded (naturalRow χ (v*jointSourceRow left 1 unit ℓ.val) hw).character holes) I =
      idealCoeff (excluded (naturalRow χ (nonzeroJointSourceRow ℓ).val
        (nonzeroJointSourceRow ℓ).property).character holes) I := by
  have h : v*jointSourceRow left 1 unit ℓ.val = (nonzeroJointSourceRow ℓ).val :=
    (jointSourceRow_eq_mul left v unit ℓ.val).symm
  have key : ∀ (w : O) (hw' : w ≠ 0), w = (nonzeroJointSourceRow ℓ).val →
      idealCoeff (excluded (naturalRow χ w hw').character holes) I =
        idealCoeff (excluded (naturalRow χ (nonzeroJointSourceRow ℓ).val
          (nonzeroJointSourceRow ℓ).property).character holes) I := by
    intro w hw' hww
    subst hww
    rfl
  exact key _ hw h

/-- The pairs with HIGH witnesses at their rows, of norm at most `Z^q` and with a zero of real part at least `a` up to
height `T`: at most the density bound of their rows times the prefixes over one ideal. A witness is asked only of the
pairs counted, and its state may have any scale. The height degree precedes the dictionary and the character, and the
constants precede the prefixes, their multipliers and units, the witnesses and both heights. -/
theorem depth_two_witness_high_count {Base : Type} [Fintype Base] (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∀ (base : Base → Character) (η₀ : Character), ∃ C : ℝ, 0 < C ∧
      ∀ {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O),
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m A a T : ℝ, q ≤ B → 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ prefixes : Finset P, ∀ pairs : Finset (NonzeroDepthTwoPair v left unit),
      ∀ W : ∀ x ∈ pairs, DepthTwoHighWitness M base η₀ (nonzeroDepthTwoRow x),
      (∀ x ∈ pairs, x.val.1 ∈ prefixes) →
      (∀ D : Ideal O, ((prefixes.filter (fun p => Ideal.span {v p} = D)).card : ℝ) ≤ A) →
      (∀ x (hx : x ∈ pairs), rawFrequencyNorm (nonzeroDepthTwoRow x) ≤ Z^q ∧
        a ≤ (W x hx).zeroMax M H hH T) →
      (∀ x ∈ pairs, Supported x.val.2.1.1.1 ∧ x.val.2.1.1.2 ≠ 0 ∧ Supported x.val.2.2.1.1 ∧ x.val.2.2.1.2 ≠ 0) →
      (∀ x ∈ pairs, primeSupport x.val.2.1.1.1 = primeSupport x.val.2.1.1.2 ∧
        primeSupport x.val.2.2.1.1 = primeSupport x.val.2.2.1.2) →
      (∀ x ∈ pairs, ((Ideal.span {depthTwoRow v left unit x.val}*firstSourceMissing left x.val.2.1).absNorm : ℝ) ≤
        Z^B) →
      (∀ x ∈ pairs, (x.val.2.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.val.2.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (x.val.2.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.val.2.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ x ∈ pairs, ((firstSourceMissing left x.val.2.1).absNorm : ℝ) ≤ Z^m) →
        (pairs.card : ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss)*A := by
  obtain ⟨J, hJ⟩ := actual_depth_two_buffered_high_row_count (Dict := Base × WholeSourceIndex M H) B B loss hB hB
    le_rfl hloss
  refine ⟨J, fun base η₀ => ?_⟩
  let bases : Base × WholeSourceIndex M H → Character := fun j => wholeSourceBase M H hH η₀ (base j.1) j.2
  obtain ⟨C, hC, hcount⟩ := hJ bases
  refine ⟨C, hC, ?_⟩
  intro P v left unit Z hZ q m A a T hq ha ha' hT prefixes pairs W hpre hprefix hzero hnonzero heq hcap hnorm
    hmissing
  rcases pairs.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · have hA : 0 ≤ A := (Nat.cast_nonneg _).trans (hprefix ⊥)
    have hZ0 : 0 < Z := by linarith
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  · let χ : NonzeroDepthTwoPair v left unit → Character := fun x =>
      if hx : x ∈ pairs then excluded (W x hx).natural.character (W x hx).state.puncture
      else excluded (W x₀ hx₀).natural.character (W x₀ hx₀).state.puncture
    let index : NonzeroDepthTwoPair v left unit → Base := fun x =>
      if hx : x ∈ pairs then (W x hx).index else (W x₀ hx₀).index
    let holes : NonzeroDepthTwoPair v left unit → Ideal O := fun x =>
      if hx : x ∈ pairs then (W x hx).holes else (W x₀ hx₀).holes
    have hχ : ∀ x (hx : x ∈ pairs), χ x = excluded (W x hx).natural.character (W x hx).state.puncture :=
      fun x hx => dite_eq_left hx
    have hindex : ∀ x (hx : x ∈ pairs), index x = (W x hx).index := fun x hx => dite_eq_left hx
    have hholes : ∀ x (hx : x ∈ pairs), holes x = (W x hx).holes := fun x hx => dite_eq_left hx
    have hn : ∀ x, ∀ j : WholeSourceIndex M H,
        (wholeOrientation (wholeSourceFamily M H hH η₀ (χ x) j) false).residue ≠ 1 := by
      intro x j
      simp only [wholeOrientation]
      by_cases hx : x ∈ pairs
      · rw [hχ x hx]
        exact whole_source_family_nonprincipal M H hH (W x hx).state η₀ (W x hx).fixed_le_ray
          (W x hx).fixed_le_base (W x hx).row (W x hx).keep (W x hx).natural j
      · have hχ₀ : χ x = excluded (W x₀ hx₀).natural.character (W x₀ hx₀).state.puncture := dite_eq_right hx
        rw [hχ₀]
        exact whole_source_family_nonprincipal M H hH (W x₀ hx₀).state η₀ (W x₀ hx₀).fixed_le_ray
          (W x₀ hx₀).fixed_le_base (W x₀ hx₀).row (W x₀ hx₀).keep (W x₀ hx₀).natural j
    refine hcount v left unit Z hZ q m A a T hq ha ha' hT prefixes pairs
      (fun x j => wholeSourceFamily M H hH η₀ (χ x) j) (fun x j => (index x, j)) (fun x _ => holes x)
      (fun _ _ => false) hn hpre hprefix ?_ ?_ hnonzero heq hcap hnorm hmissing
    · intro x hx j I
      show idealCoeff (wholeSourceFamily M H hH η₀ (χ x) j) I =
        idealCoeff (excluded (naturalRow (bases (index x, j)) (nonzeroDepthTwoRow x).val
          (nonzeroDepthTwoRow x).property).character (holes x)) I
      rw [hindex x hx, hholes x hx]
      exact whole_source_family_mask M H hH η₀ (base (W x hx).index) (χ x) (nonzeroDepthTwoRow x).val
        (nonzeroDepthTwoRow x).property
        (naturalRow (base (W x hx).index) _ (nonzeroDepthTwoRow x).property) (W x hx).holes (W x hx).holes_ne
        (fun I => by rw [hχ x hx]; exact (W x hx).mask I)
        (fun j => naturalRow (wholeSourceBase M H hH η₀ (base (W x hx).index) j)
          (nonzeroDepthTwoRow x).val (nonzeroDepthTwoRow x).property) j I
    · intro x hx
      refine ⟨(hzero x hx).1, (hzero x hx).2.trans ?_⟩
      exact LowBranch.zeroMaximum_subfamily
        (wholeSourceFamily M H hH η₀ (excluded (W x hx).natural.character (W x hx).state.puncture))
        (fun j => wholeOrientation (wholeSourceFamily M H hH η₀ (χ x) j) false)
        (whole_source_family_nonprincipal M H hH (W x hx).state η₀ (W x hx).fixed_le_ray (W x hx).fixed_le_base
          (W x hx).row (W x hx).keep (W x hx).natural)
        (hn x) id (fun j => by simp only [id, wholeOrientation, Bool.false_eq_true, ↓reduceIte, hχ x hx]) T

/-- The selected classes over one ideal of the prefix multipliers number at most the prefixes over that ideal times a
bound on the selected classes of one prefix. -/
theorem selected_classes_over_ideal {P : Type*} {Class : P → Type} (v : P → O) (prefixes : Finset P)
    (S : Finset (Σ p, Class p)) (K : ℝ) (hS : ∀ x ∈ S, x.1 ∈ prefixes)
    (hK : ∀ p ∈ prefixes, ((S.filter (fun x => x.1 = p)).card : ℝ) ≤ K) (D : Ideal O) :
    ((S.filter (fun x => Ideal.span {v x.1} = D)).card : ℝ) ≤
      ((prefixes.filter (fun p => Ideal.span {v p} = D)).card : ℝ)*K := by
  have hmaps : ∀ x ∈ S.filter (fun x => Ideal.span {v x.1} = D),
      x.1 ∈ prefixes.filter (fun p => Ideal.span {v p} = D) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hS x hx.1, hx.2⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  have hle : ∀ p ∈ prefixes.filter (fun p => Ideal.span {v p} = D),
      ((((S.filter (fun x => Ideal.span {v x.1} = D)).filter (fun x => x.1 = p)).card : ℕ) : ℝ) ≤ K := by
    intro p hp
    have hsub : (S.filter (fun x => Ideal.span {v x.1} = D)).filter (fun x => x.1 = p) ⊆
        S.filter (fun x => x.1 = p) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      exact Finset.mem_filter.mpr ⟨hx.1.1, hx.2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hK p (Finset.mem_filter.mp hp).1)
  calc ((S.filter (fun x => Ideal.span {v x.1} = D)).card : ℝ)
      = ∑ p ∈ prefixes.filter (fun p => Ideal.span {v p} = D),
          ((((S.filter (fun x => Ideal.span {v x.1} = D)).filter (fun x => x.1 = p)).card : ℕ) : ℝ) := by
        rw [hfiber, Nat.cast_sum]
    _ ≤ ∑ _p ∈ prefixes.filter (fun p => Ideal.span {v p} = D), K := Finset.sum_le_sum hle
    _ = ((prefixes.filter (fun p => Ideal.span {v p} = D)).card : ℝ)*K := by
        rw [Finset.sum_const, nsmul_eq_mul]

section Selection
variable {M H hH}
variable {Base : Type} {base : Base → Character} {η₀ : Character} {Z B T : ℝ} {left : Bool}
variable {P : Type*} {v : P → O} {unit : P → FirstSourceLabel → O}

/-- The pair of a class of the HIGH part of a prefix and one of its labels: the class is the prefix of the pair. -/
def selectedPair (R : ∀ p, SecondStepHighCount M H hH base η₀ Z B T left (v p) (unit p))
    (y : Σ x : (Σ p, (R p).Class), NonzeroJointSourceLabel left (v x.1) (unit x.1)) :
    NonzeroDepthTwoPair (fun x : (Σ p, (R p).Class) => v x.1) left (fun x => unit x.1) :=
  ⟨(y.1, y.2.val), y.2.property⟩

/-- Distinct classes or labels give distinct pairs. -/
theorem selectedPair_injective (R : ∀ p, SecondStepHighCount M H hH base η₀ Z B T left (v p) (unit p)) :
    Function.Injective (selectedPair R) := by
  rintro ⟨x, ℓ⟩ ⟨x', ℓ'⟩ h
  have h' : (x, ℓ.val) = (x', ℓ'.val) := congrArg Subtype.val h
  rw [Prod.mk.injEq] at h'
  obtain ⟨rfl, hl⟩ := h'
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hl))

/-- The pairs of the labels of the selected classes. -/
def selectedPairs (R : ∀ p, SecondStepHighCount M H hH base η₀ Z B T left (v p) (unit p))
    (S : Finset (Σ p, (R p).Class)) :
    Finset (NonzeroDepthTwoPair (fun x : (Σ p, (R p).Class) => v x.1) left (fun x => unit x.1)) :=
  (S.sigma (fun x => (R x.1).labels x.2)).map ⟨selectedPair R, selectedPair_injective R⟩

/-- The label of a pair whose prefix is a class, at the multiplier and units of the class's prefix. -/
def pairLabel (R : ∀ p, SecondStepHighCount M H hH base η₀ Z B T left (v p) (unit p))
    (y : NonzeroDepthTwoPair (fun x : (Σ p, (R p).Class) => v x.1) left (fun x => unit x.1)) :
    NonzeroJointSourceLabel left (v y.val.1.1) (unit y.val.1.1) :=
  ⟨y.val.2, y.property⟩

/-- The row of the label of a pair is the row of the pair. -/
theorem pairLabel_row (R : ∀ p, SecondStepHighCount M H hH base η₀ Z B T left (v p) (unit p))
    (y : NonzeroDepthTwoPair (fun x : (Σ p, (R p).Class) => v x.1) left (fun x => unit x.1)) :
    nonzeroJointSourceRow (pairLabel R y) = nonzeroDepthTwoRow y := rfl

/-- A selected pair has a selected class as prefix and a label of that class. -/
theorem mem_selectedPairs (R : ∀ p, SecondStepHighCount M H hH base η₀ Z B T left (v p) (unit p))
    (S : Finset (Σ p, (R p).Class))
    (y : NonzeroDepthTwoPair (fun x : (Σ p, (R p).Class) => v x.1) left (fun x => unit x.1))
    (hy : y ∈ selectedPairs R S) : y.val.1 ∈ S ∧ pairLabel R y ∈ (R y.val.1.1).labels y.val.1.2 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
  exact Finset.mem_sigma.mp hz

/-- The selected pairs number the labels of the selected classes. -/
theorem card_selectedPairs (R : ∀ p, SecondStepHighCount M H hH base η₀ Z B T left (v p) (unit p))
    (S : Finset (Σ p, (R p).Class)) :
    ((selectedPairs R S).card : ℝ) = ∑ x ∈ S, (((R x.1).labels x.2).card : ℝ) := by
  unfold selectedPairs
  rw [Finset.card_map, Finset.card_sigma, Nat.cast_sum]

end Selection

/-- The labels of the classes selected from the HIGH parts of many prefixes, with row norms at most `Z^q`, missing
radicals at most `Z^m` and zero parameters at least `a`: at most the density bound of the rows times the selected
classes over one ideal of the prefix multipliers. The selected classes are the prefixes of the count, so a label of
several selected classes of one prefix is counted once for each. The constants precede the prefixes, their
multipliers, units and HIGH parts and both heights. The height degree precedes the dictionary and the character. -/
theorem second_step_high_selection_count {Base : Type} [Fintype Base] (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∀ (base : Base → Character) (η₀ : Character), ∃ C : ℝ, 0 < C ∧
      ∀ {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O) (Z T : ℝ), 2 ≤ Z → 0 ≤ T →
      ∀ R : ∀ p, SecondStepHighCount M H hH base η₀ Z B T left (v p) (unit p),
      ∀ S : Finset (Σ p, (R p).Class), ∀ q m a A : ℝ, q ≤ B → 4/5 ≤ a → a ≤ 7/8 →
      (∀ D : Ideal O, ((S.filter (fun x => Ideal.span {v x.1} = D)).card : ℝ) ≤ A) →
      (∀ x ∈ S, (R x.1).rowExp x.2 ≤ q ∧ (R x.1).missExp x.2 ≤ m ∧ a ≤ (R x.1).zeroBin x.2) →
        (∑ x ∈ S, (((R x.1).labels x.2).card : ℝ)) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss)*A := by
  obtain ⟨J, hJ⟩ := depth_two_witness_high_count (Base := Base) M H hH B loss hB hloss
  refine ⟨J, fun base η₀ => ?_⟩
  obtain ⟨C, hC, hcount⟩ := hJ base η₀
  refine ⟨C, hC, ?_⟩
  intro P v left unit Z T hZ hT R S q m a A hq ha ha' hprefix hclass
  have hZ1 : 1 ≤ Z := by linarith
  rw [← card_selectedPairs R S]
  refine hcount (fun x : (Σ p, (R p).Class) => v x.1) left (fun x => unit x.1) Z hZ q m A a T hq ha ha' hT S
    (selectedPairs R S)
    (fun y hy => (R y.val.1.1).witness y.val.1.2 (pairLabel R y) (mem_selectedPairs R S y hy).2)
    (fun y hy => (mem_selectedPairs R S y hy).1) hprefix ?_ ?_ ?_ ?_ ?_ ?_
  · intro y hy
    have hm := mem_selectedPairs R S y hy
    exact ⟨((R y.val.1.1).row_le y.val.1.2 (pairLabel R y) hm.2).trans
        (Real.rpow_le_rpow_of_exponent_le hZ1 (hclass _ hm.1).1),
      (hclass _ hm.1).2.2.trans ((R y.val.1.1).zero_le y.val.1.2 (pairLabel R y) hm.2)⟩
  · intro y hy
    exact (R y.val.1.1).supported y.val.1.2 (pairLabel R y) (mem_selectedPairs R S y hy).2
  · intro y hy
    exact (R y.val.1.1).same_support y.val.1.2 (pairLabel R y) (mem_selectedPairs R S y hy).2
  · intro y hy
    exact (R y.val.1.1).row_cap y.val.1.2 (pairLabel R y) (mem_selectedPairs R S y hy).2
  · intro y hy
    exact (R y.val.1.1).ideal_cap y.val.1.2 (pairLabel R y) (mem_selectedPairs R S y hy).2
  · intro y hy
    have hm := mem_selectedPairs R S y hy
    exact ((R y.val.1.1).missing_le y.val.1.2 (pairLabel R y) hm.2).trans
      (Real.rpow_le_rpow_of_exponent_le hZ1 (hclass _ hm.1).2.1)

end
end OAI.SevenEighths.Cycle63Moment
