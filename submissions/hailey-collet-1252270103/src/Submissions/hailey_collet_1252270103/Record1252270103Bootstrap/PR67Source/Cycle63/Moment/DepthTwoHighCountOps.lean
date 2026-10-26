import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoHighCount
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Operations on the count form of the second step's HIGH part: the union of finitely many parts, a common shift of
the class exponents, the part of one class, and a larger zero height. Released under Apache 2.0. -/
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

/-- The union of the HIGH parts of a finite family: a class is an index together with a class of that index's part. -/
def SecondStepHighCount.sigma {ι : Type} [Fintype ι] (R : ι → SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) :
    SecondStepHighCount M H hH base η₀ Z B T left v₁ unit where
  Class := Σ i, (R i).Class
  labels := fun x => (R x.1).labels x.2
  exponent := fun x => (R x.1).exponent x.2
  rowExp := fun x => (R x.1).rowExp x.2
  missExp := fun x => (R x.1).missExp x.2
  zeroBin := fun x => (R x.1).zeroBin x.2
  witness := fun x => (R x.1).witness x.2
  zero_le := fun x => (R x.1).zero_le x.2
  row_le := fun x => (R x.1).row_le x.2
  supported := fun x => (R x.1).supported x.2
  same_support := fun x => (R x.1).same_support x.2
  row_cap := fun x => (R x.1).row_cap x.2
  ideal_cap := fun x => (R x.1).ideal_cap x.2
  missing_le := fun x => (R x.1).missing_le x.2

/-- The count form of a union is the sum of the count forms. -/
theorem SecondStepHighCount.sigma_value {ι : Type} [Fintype ι]
    (R : ι → SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) :
    (SecondStepHighCount.sigma R).value = ∑ i, (R i).value := by
  unfold SecondStepHighCount.value SecondStepHighCount.sigma
  exact Fintype.sum_sigma _

/-- The HIGH part with every class exponent raised by `c`. -/
def SecondStepHighCount.shift (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) (c : ℝ) :
    SecondStepHighCount M H hH base η₀ Z B T left v₁ unit where
  Class := R.Class
  labels := R.labels
  exponent := fun σ => R.exponent σ + c
  rowExp := R.rowExp
  missExp := R.missExp
  zeroBin := R.zeroBin
  witness := R.witness
  zero_le := R.zero_le
  row_le := R.row_le
  supported := R.supported
  same_support := R.same_support
  row_cap := R.row_cap
  ideal_cap := R.ideal_cap
  missing_le := R.missing_le

/-- Raising every class exponent by `c` multiplies the count form by `Z^c`. -/
theorem SecondStepHighCount.shift_value (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) (c : ℝ)
    (hZ : 0 < Z) : (R.shift c).value = Z^c*R.value := by
  unfold SecondStepHighCount.value SecondStepHighCount.shift
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Real.rpow_add hZ]
  ring

/-- The HIGH part of one class: a finite set of labels with witnesses, the class exponent and the row-norm,
missing-radical and zero parameters of its labels. -/
def SecondStepHighCount.single (labels : Finset (NonzeroJointSourceLabel left v₁ unit)) (e q m a : ℝ)
    (witness : ∀ ℓ ∈ labels, DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow ℓ))
    (zero_le : ∀ ℓ (h : ℓ ∈ labels), a ≤ (witness ℓ h).zeroMax M H hH T)
    (row_le : ∀ ℓ ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow ℓ) ≤ Z^q)
    (supported : ∀ ℓ ∈ labels, Supported ℓ.val.1.1.1 ∧ ℓ.val.1.1.2 ≠ 0 ∧
      Supported ℓ.val.2.1.1 ∧ ℓ.val.2.1.2 ≠ 0)
    (same_support : ∀ ℓ ∈ labels, primeSupport ℓ.val.1.1.1 = primeSupport ℓ.val.1.1.2 ∧
      primeSupport ℓ.val.2.1.1 = primeSupport ℓ.val.2.1.2)
    (row_cap : ∀ ℓ ∈ labels,
      ((Ideal.span {jointSourceRow left v₁ unit ℓ.val}*firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^B)
    (ideal_cap : ∀ ℓ ∈ labels, (ℓ.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (ℓ.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
      (ℓ.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (ℓ.val.2.1.2.absNorm : ℝ) ≤ Z^B)
    (missing_le : ∀ ℓ ∈ labels, ((firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^m) :
    SecondStepHighCount M H hH base η₀ Z B T left v₁ unit where
  Class := Unit
  labels := fun _ => labels
  exponent := fun _ => e
  rowExp := fun _ => q
  missExp := fun _ => m
  zeroBin := fun _ => a
  witness := fun _ => witness
  zero_le := fun _ => zero_le
  row_le := fun _ => row_le
  supported := fun _ => supported
  same_support := fun _ => same_support
  row_cap := fun _ => row_cap
  ideal_cap := fun _ => ideal_cap
  missing_le := fun _ => missing_le

/-- The count form of one class is `Z^e` times its number of labels. -/
theorem SecondStepHighCount.single_value (labels : Finset (NonzeroJointSourceLabel left v₁ unit)) (e q m a : ℝ)
    (witness : ∀ ℓ ∈ labels, DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow ℓ))
    (zero_le : ∀ ℓ (h : ℓ ∈ labels), a ≤ (witness ℓ h).zeroMax M H hH T)
    (row_le : ∀ ℓ ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow ℓ) ≤ Z^q)
    (supported : ∀ ℓ ∈ labels, Supported ℓ.val.1.1.1 ∧ ℓ.val.1.1.2 ≠ 0 ∧
      Supported ℓ.val.2.1.1 ∧ ℓ.val.2.1.2 ≠ 0)
    (same_support : ∀ ℓ ∈ labels, primeSupport ℓ.val.1.1.1 = primeSupport ℓ.val.1.1.2 ∧
      primeSupport ℓ.val.2.1.1 = primeSupport ℓ.val.2.1.2)
    (row_cap : ∀ ℓ ∈ labels,
      ((Ideal.span {jointSourceRow left v₁ unit ℓ.val}*firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^B)
    (ideal_cap : ∀ ℓ ∈ labels, (ℓ.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (ℓ.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
      (ℓ.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (ℓ.val.2.1.2.absNorm : ℝ) ≤ Z^B)
    (missing_le : ∀ ℓ ∈ labels, ((firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^m) :
    (SecondStepHighCount.single (M := M) (H := H) (hH := hH) (T := T) labels e q m a witness zero_le row_le
      supported same_support row_cap ideal_cap missing_le).value = Z^e*labels.card := by
  unfold SecondStepHighCount.value SecondStepHighCount.single
  simp only [Finset.univ_unique, Finset.sum_singleton]

/-- The HIGH part with the zero height raised from `T` to `T'`: a zero up to height `T` is one up to height `T'`. -/
def SecondStepHighCount.raise (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) {T' : ℝ} (hT : T ≤ T') :
    SecondStepHighCount M H hH base η₀ Z B T' left v₁ unit where
  Class := R.Class
  labels := R.labels
  exponent := R.exponent
  rowExp := R.rowExp
  missExp := R.missExp
  zeroBin := R.zeroBin
  witness := R.witness
  zero_le := fun σ ℓ h => (R.zero_le σ ℓ h).trans (zeroMaximum_mono _ _ hT)
  row_le := R.row_le
  supported := R.supported
  same_support := R.same_support
  row_cap := R.row_cap
  ideal_cap := R.ideal_cap
  missing_le := R.missing_le

/-- Raising the zero height keeps the count form. -/
theorem SecondStepHighCount.raise_value (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) {T' : ℝ}
    (hT : T ≤ T') : (R.raise hT).value = R.value := rfl

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
