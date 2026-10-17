import Candidate.Cycle63.Moment.PhysicalHighRows
import Candidate.Cycle63.Moment.JointHighDensity
import Candidate.Cycle63.Moment.SecondNaturalMask
import Candidate.Target830.High.JointHighDensity
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily LocalMoment ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily Cycle63Moment
open CenteredMomentCanonicalFirst ActualEisensteinCubic
open HeckeDetectorZeros ConcreteTraceCRT Target830MarkedDensity
local notation "O" => HeckeFamily.O
theorem actual_joint_fixed_physical_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ character : NonzeroJointSourceLabel left u₀ unit → Character,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Dict,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Ideal O,
      ∀ reverse : NonzeroJointSourceLabel left u₀ unit → Bool,
      (∀ label ∈ labels, ∀ I : Ideal O, idealCoeff (character label) I =
        idealCoeff (excluded (naturalRow (base (dictionary label))
          (nonzeroJointSourceRow label).val (nonzeroJointSourceRow label).property).character
            (puncture label)) I) →
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        ∃ s : ℂ, LFunction (wholeOrientation (character label) (reverse label)) s = 0 ∧
          (s ≠ 1 ∨ (wholeOrientation (character label) (reverse label)).residue ≠ 1) ∧
          a ≤ s.re ∧ |s.im| ≤ T) →
      (∀ label ∈ labels, Supported label.val.1.1.1 ∧ label.val.1.1.2 ≠ 0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.val.1.1.1 = primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1 = primeSupport label.val.2.1.2) →
      (∀ label ∈ labels,
        ((Ideal.span {jointSourceRow left u₀ unit label.val}*
          firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (label.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (label.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^m) →
        (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_natural_high_row_count
    (orientedFixedBase base) B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels character dictionary
    puncture reverse hcoeff hzero hnonzero heq hsupportnorm hnorm hmissing
  exact hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels Prod.snd
    (fun label hl => ⟨(hzero label hl).1,
      physical_zero_to_fixed_dictionary base (character label) (dictionary label)
        (nonzeroJointSourceRow label) (puncture label) (reverse label)
        (hcoeff label hl) a T (by linarith) (hzero label hl).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

/-- High-bin cardinality from the actual finite whole-family zero maximum,
with constants chosen before every live masked family and height. -/

theorem actual_joint_buffered_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ {Family : Type*} [Fintype Family],
      ∀ character : NonzeroJointSourceLabel left u₀ unit → Family → Character,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Family → Dict,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Family → Ideal O,
      ∀ reverse : NonzeroJointSourceLabel left u₀ unit → Family → Bool,
      ∀ hchar : ∀ label, ∀ j,
        (wholeOrientation (character label j) (reverse label j)).residue ≠ 1,
      (∀ label ∈ labels, ∀ j, ∀ I : Ideal O, idealCoeff (character label j) I =
        idealCoeff (excluded (naturalRow (base (dictionary label j))
          (nonzeroJointSourceRow label).val (nonzeroJointSourceRow label).property).character
            (puncture label j)) I) →
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (fun j => wholeOrientation (character label j) (reverse label j)) (hchar label) T) →
      (∀ label ∈ labels, Supported label.val.1.1.1 ∧ label.val.1.1.2 ≠ 0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.val.1.1.1 = primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1 = primeSupport label.val.2.1.2) →
      (∀ label ∈ labels,
        ((Ideal.span {jointSourceRow left u₀ unit label.val}*
          firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (label.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (label.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^m) →
        (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_natural_high_row_count
    (orientedFixedBase base) B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels Family _ character dictionary
    puncture reverse hchar hcoeff hzero hnonzero heq hsupportnorm hnorm hmissing
  exact hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels Prod.snd
    (fun label hl => ⟨(hzero label hl).1,
      physical_family_maximum_to_fixed_dictionary base (character label) (reverse label)
        (hchar label) (dictionary label) (puncture label) (nonzeroJointSourceRow label)
        (hcoeff label hl) a T (by linarith) (hzero label hl).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_joint_fixed_physical_high_row_count
#print axioms OAI.SevenEighths.TargetHigh830.actual_joint_buffered_high_row_count
