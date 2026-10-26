import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoHighCountOps
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The HIGH part of one class given on rows: an injective map from rows to second-level labels at the child multiplier,
a witness at the label of each row and the class conditions on each row; the labels of the class are the image of the
rows. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily HeckeDetectorZeros LocalMoment ProbePhysical CanonicalQuadraticSieve IdealMobiusDivisorSum
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
variable {M : Ideal O} [NeZero M]
variable {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {Base : Type} {base : Base → Character} {η₀ : Character} {Z B T : ℝ} {left : Bool} {v₁ : O}
  {unit : FirstSourceLabel → O}

/-- A joint label at the fixed row `1` as a label at the fixed row `v`, for `v ≠ 0`: the same label, whose row is `v`
times the row at `1`. -/
def multiplierLabel (left : Bool) (unit : FirstSourceLabel → O) {v : O} (hv : v ≠ 0)
    (key : NonzeroJointSourceLabel left 1 unit) : NonzeroJointSourceLabel left v unit :=
  ⟨key.val, by rw [jointSourceRow_eq_mul]; exact mul_ne_zero hv key.property⟩

/-- Labels at the fixed row `1` with the same image at the fixed row `v` are equal. -/
theorem multiplierLabel_injective (left : Bool) (unit : FirstSourceLabel → O) {v : O} (hv : v ≠ 0) :
    Function.Injective (multiplierLabel left unit hv) := by
  intro k k' h
  have h' : (multiplierLabel left unit hv k).val = (multiplierLabel left unit hv k').val := congrArg Subtype.val h
  exact Subtype.ext h'

/-- The row of a label at the fixed row `v` is `v` times the row of the label at the fixed row `1`. -/
theorem multiplierLabel_row (left : Bool) (unit : FirstSourceLabel → O) {v : O} (hv : v ≠ 0)
    (key : NonzeroJointSourceLabel left 1 unit) :
    (nonzeroJointSourceRow (multiplierLabel left unit hv key)).val = v*(nonzeroJointSourceRow key).val :=
  jointSourceRow_eq_mul left v unit key.val

/-- A witness transported along an equality of labels keeps its zero maximum. -/
theorem DepthTwoHighWitness.zeroMax_cast {ℓ ℓ' : NonzeroJointSourceLabel left v₁ unit} (h : ℓ = ℓ')
    (W : DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow ℓ)) (T' : ℝ) :
    (h ▸ W : DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow ℓ')).zeroMax M H hH T' = W.zeroMax M H hH T' := by
  subst h
  rfl

section Rows
variable {κ : Type*} (rows : Finset κ) (lab : κ → NonzeroJointSourceLabel left v₁ unit)
  (W : ∀ r, DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow (lab r)))

/-- The row of the rows over a label of the image. -/
def rowOver (ℓ : NonzeroJointSourceLabel left v₁ unit) (h : ℓ ∈ rows.image lab) : κ :=
  Classical.choose (Finset.mem_image.mp h)

theorem rowOver_mem (ℓ : NonzeroJointSourceLabel left v₁ unit) (h : ℓ ∈ rows.image lab) :
    rowOver rows lab ℓ h ∈ rows := (Classical.choose_spec (Finset.mem_image.mp h)).1

theorem lab_rowOver (ℓ : NonzeroJointSourceLabel left v₁ unit) (h : ℓ ∈ rows.image lab) :
    lab (rowOver rows lab ℓ h) = ℓ := (Classical.choose_spec (Finset.mem_image.mp h)).2

/-- The witness at a label of the image: the witness of its row, transported to the label. -/
def imageWitness (ℓ : NonzeroJointSourceLabel left v₁ unit) (h : ℓ ∈ rows.image lab) :
    DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow ℓ) :=
  lab_rowOver rows lab ℓ h ▸ W (rowOver rows lab ℓ h)

/-- The HIGH part of one class given on rows. Its labels are the image of the rows, its witnesses those of the rows,
and the class conditions hold at every row: a zero of real part at least `a` up to height `T`, row norm at most
`Z^q`, supported common ideals with equal prime supports, norm caps `Z^B` and missing radical at most `Z^m`. -/
def SecondStepHighCount.ofRows (e q m a : ℝ)
    (hzero : ∀ r ∈ rows, a ≤ (W r).zeroMax M H hH T)
    (hrow : ∀ r ∈ rows, rawFrequencyNorm (nonzeroJointSourceRow (lab r)) ≤ Z^q)
    (hsupp : ∀ r ∈ rows, Supported (lab r).val.1.1.1 ∧ (lab r).val.1.1.2 ≠ 0 ∧
      Supported (lab r).val.2.1.1 ∧ (lab r).val.2.1.2 ≠ 0)
    (hsame : ∀ r ∈ rows, primeSupport (lab r).val.1.1.1 = primeSupport (lab r).val.1.1.2 ∧
      primeSupport (lab r).val.2.1.1 = primeSupport (lab r).val.2.1.2)
    (hcap : ∀ r ∈ rows,
      ((Ideal.span {jointSourceRow left v₁ unit (lab r).val}*firstSourceMissing left (lab r).val.1).absNorm : ℝ) ≤
        Z^B)
    (hideal : ∀ r ∈ rows, ((lab r).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ ((lab r).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
      ((lab r).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((lab r).val.2.1.2.absNorm : ℝ) ≤ Z^B)
    (hmiss : ∀ r ∈ rows, ((firstSourceMissing left (lab r).val.1).absNorm : ℝ) ≤ Z^m) :
    SecondStepHighCount M H hH base η₀ Z B T left v₁ unit :=
  SecondStepHighCount.single (rows.image lab) e q m a (imageWitness rows lab W)
    (fun ℓ h => by
      unfold imageWitness
      rw [DepthTwoHighWitness.zeroMax_cast]
      exact hzero _ (rowOver_mem rows lab ℓ h))
    (fun ℓ h => by
      have hr := hrow _ (rowOver_mem rows lab ℓ h)
      rw [lab_rowOver rows lab ℓ h] at hr
      exact hr)
    (fun ℓ h => by
      have hr := hsupp _ (rowOver_mem rows lab ℓ h)
      rw [lab_rowOver rows lab ℓ h] at hr
      exact hr)
    (fun ℓ h => by
      have hr := hsame _ (rowOver_mem rows lab ℓ h)
      rw [lab_rowOver rows lab ℓ h] at hr
      exact hr)
    (fun ℓ h => by
      have hr := hcap _ (rowOver_mem rows lab ℓ h)
      rw [lab_rowOver rows lab ℓ h] at hr
      exact hr)
    (fun ℓ h => by
      have hr := hideal _ (rowOver_mem rows lab ℓ h)
      rw [lab_rowOver rows lab ℓ h] at hr
      exact hr)
    (fun ℓ h => by
      have hr := hmiss _ (rowOver_mem rows lab ℓ h)
      rw [lab_rowOver rows lab ℓ h] at hr
      exact hr)

/-- The count form of one class given on injectively labelled rows is `Z^e` times the number of rows. -/
theorem SecondStepHighCount.ofRows_value (hlab : Function.Injective lab) (e q m a : ℝ)
    (hzero : ∀ r ∈ rows, a ≤ (W r).zeroMax M H hH T)
    (hrow : ∀ r ∈ rows, rawFrequencyNorm (nonzeroJointSourceRow (lab r)) ≤ Z^q)
    (hsupp : ∀ r ∈ rows, Supported (lab r).val.1.1.1 ∧ (lab r).val.1.1.2 ≠ 0 ∧
      Supported (lab r).val.2.1.1 ∧ (lab r).val.2.1.2 ≠ 0)
    (hsame : ∀ r ∈ rows, primeSupport (lab r).val.1.1.1 = primeSupport (lab r).val.1.1.2 ∧
      primeSupport (lab r).val.2.1.1 = primeSupport (lab r).val.2.1.2)
    (hcap : ∀ r ∈ rows,
      ((Ideal.span {jointSourceRow left v₁ unit (lab r).val}*firstSourceMissing left (lab r).val.1).absNorm : ℝ) ≤
        Z^B)
    (hideal : ∀ r ∈ rows, ((lab r).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ ((lab r).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
      ((lab r).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((lab r).val.2.1.2.absNorm : ℝ) ≤ Z^B)
    (hmiss : ∀ r ∈ rows, ((firstSourceMissing left (lab r).val.1).absNorm : ℝ) ≤ Z^m) :
    (SecondStepHighCount.ofRows (M := M) (H := H) (hH := hH) (B := B) (T := T) rows lab W e q m a hzero hrow
      hsupp hsame hcap hideal hmiss).value = Z^e*rows.card := by
  unfold SecondStepHighCount.ofRows
  rw [SecondStepHighCount.single_value, Finset.card_image_of_injective rows hlab]

end Rows

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
