import Candidate.Cycle63.Moment.WholeSourceFamily
import Candidate.Cycle63.Moment.HighSourceEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion
import Candidate.Target830.High.PhysicalHighRows
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily LocalMoment ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily Cycle63Moment
open CenteredMomentCanonicalFirst ActualEisensteinCubic
open CenteredMomentEnergyState CenteredMomentCommonRadialData
open HeckeDetectorZeros ConcreteTraceCRT Target830MarkedDensity
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
theorem actual_whole_joint_high_row_count {Base : Type*} [Fintype Base]
    (base : Base → Character) (η₀ : Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (Z : ℝ), 2 ≤ Z → ∀ q m a T Bmask bΦ : ℝ,
      q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z Bmask bΦ,
      ∀ hQM : ∀ l, (st l).fixedModulus ≤ M,
      ∀ hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus,
      ∀ z : NonzeroJointSourceLabel left u₀ unit → O,
      ∀ hz : ∀ l, (st l).radial.keep (z l),
      ∀ F : ∀ l, NaturalRow (st l).character (z l),
      ∀ index : NonzeroJointSourceLabel left u₀ unit → Base,
      ∀ holes : NonzeroJointSourceLabel left u₀ unit → Ideal O,
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (F l).character (st l).puncture) I =
          idealCoeff (excluded (naturalRow (base (index l))
            (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
            (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded (F l).character (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l)
            (z l) (hz l) (F l)) T) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^m) →
      (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  let bases : Base×WholeSourceIndex M H → Character :=
    fun j => wholeSourceBase M H hH η₀ (base j.1) j.2
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_buffered_high_row_count bases B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T Bmask bΦ hq ha ha' hT labels st hQM hQη z hz F
    index holes hholes hmask hzero hnonzero heq hsupport hnorm hmissing
  let characters := fun l => wholeSourceFamily M H hH η₀
    (excluded (F l).character (st l).puncture)
  have hn := fun l => whole_source_family_nonprincipal M H hH (st l) η₀
    (hQM l) (hQη l) (z l) (hz l) (F l)
  apply hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels characters
    (fun l j => (index l,j)) (fun l _ => holes l) (fun _ _ => false) hn
    ?_ hzero hnonzero heq hsupport hnorm hmissing
  intro l hl j I
  exact whole_source_family_mask M H hH η₀ (base (index l))
    (excluded (F l).character (st l).puncture) (nonzeroJointSourceRow l).val
    (nonzeroJointSourceRow l).property
    (naturalRow (base (index l)) _ (nonzeroJointSourceRow l).property)
    (holes l) (hholes l hl) (hmask l hl)
    (fun j => naturalRow (wholeSourceBase M H hH η₀ (base (index l)) j)
      (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property) j I

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_whole_joint_high_row_count
