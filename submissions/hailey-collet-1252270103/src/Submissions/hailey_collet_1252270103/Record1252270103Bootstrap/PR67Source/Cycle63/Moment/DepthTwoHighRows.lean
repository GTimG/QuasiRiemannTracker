import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.WholeSourceFamily
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The count of the pairs of a child prefix and a second-level label whose rows carry a zero of the physical
family, first for a family masked to the fixed dictionary and then for the whole source family of a natural state.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily HeckeDetectorZeros LocalMoment ProbePhysical CanonicalQuadraticSieve IdealMobiusDivisorSum
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The pairs whose rows have norm at most `Z^q` and whose physical families, each member an Euler-masked character
of the fixed dictionary at the pair's row, have a zero maximum at least `a` up to height `T`: at most the density
bound of the rows times the pairs over one row. The height degree precedes the dictionary, and the constants precede
the prefixes, their multipliers and units, every masked family and both heights. -/
theorem actual_depth_two_buffered_high_row_count {Dict : Type*} [Fintype Dict]
    (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∀ base : Dict → Character, ∃ C : ℝ, 0 < C ∧
      ∀ {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O),
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m A a T : ℝ, q ≤ Q → 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ prefixes : Finset P, ∀ pairs : Finset (NonzeroDepthTwoPair v left unit),
      ∀ {Family : Type*} [Fintype Family],
      ∀ character : NonzeroDepthTwoPair v left unit → Family → Character,
      ∀ dictionary : NonzeroDepthTwoPair v left unit → Family → Dict,
      ∀ puncture : NonzeroDepthTwoPair v left unit → Family → Ideal O,
      ∀ reverse : NonzeroDepthTwoPair v left unit → Family → Bool,
      ∀ hchar : ∀ x, ∀ j, (wholeOrientation (character x j) (reverse x j)).residue ≠ 1,
      (∀ x ∈ pairs, x.val.1 ∈ prefixes) →
      (∀ D : Ideal O, ((prefixes.filter (fun p => Ideal.span {v p} = D)).card : ℝ) ≤ A) →
      (∀ x ∈ pairs, ∀ j, ∀ I : Ideal O, idealCoeff (character x j) I =
        idealCoeff (excluded (naturalRow (base (dictionary x j))
          (nonzeroDepthTwoRow x).val (nonzeroDepthTwoRow x).property).character (puncture x j)) I) →
      (∀ x ∈ pairs, rawFrequencyNorm (nonzeroDepthTwoRow x) ≤ Z^q ∧
        a ≤ zeroMaximum (fun j => wholeOrientation (character x j) (reverse x j)) (hchar x) T) →
      (∀ x ∈ pairs, Supported x.val.2.1.1.1 ∧ x.val.2.1.1.2 ≠ 0 ∧ Supported x.val.2.2.1.1 ∧ x.val.2.2.1.2 ≠ 0) →
      (∀ x ∈ pairs, primeSupport x.val.2.1.1.1 = primeSupport x.val.2.1.1.2 ∧
        primeSupport x.val.2.2.1.1 = primeSupport x.val.2.2.1.2) →
      (∀ x ∈ pairs, ((Ideal.span {depthTwoRow v left unit x.val}*firstSourceMissing left x.val.2.1).absNorm : ℝ) ≤
        Z^B) →
      (∀ x ∈ pairs, (x.val.2.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.val.2.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (x.val.2.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.val.2.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ x ∈ pairs, ((firstSourceMissing left x.val.2.1).absNorm : ℝ) ≤ Z^m) →
        (pairs.card : ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss)*A := by
  obtain ⟨J, hJ⟩ := depth_two_high_row_count (Dict := Dict × Bool) B Q loss hB hQ hQB hloss
  refine ⟨J, fun base => ?_⟩
  obtain ⟨C, hC, hcount⟩ := hJ (orientedFixedBase base)
  refine ⟨C, hC, ?_⟩
  intro P v left unit Z hZ q m A a T hq ha ha' hT prefixes pairs Family _ character dictionary puncture reverse
    hchar hpre hprefix hcoeff hzero hnonzero heq hsupportnorm hnorm hmissing
  exact hcount v left unit Z hZ q m A a T hq ha ha' hT Prod.snd prefixes pairs hpre hprefix
    (fun x hx => ⟨(hzero x hx).1,
      physical_family_maximum_to_fixed_dictionary base (character x) (reverse x) (hchar x) (dictionary x)
        (puncture x) (nonzeroDepthTwoRow x) (hcoeff x hx) a T (by linarith) (hzero x hx).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

/-- The pairs whose rows have norm at most `Z^q` and whose natural states have a zero of the whole source family with
real part at least `a` and height at most `T`, the state's masked character being a masked member of the fixed
dictionary at the pair's row: at most the density bound of the rows times the pairs over one row. The constants
precede the prefixes, their multipliers and units, the states, the punctures and both heights. -/
theorem actual_whole_depth_two_high_row_count {Base : Type*} [Fintype Base]
    (base : Base → Character) (η₀ : Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O),
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m A a T Bmask bΦ : ℝ, q ≤ Q → 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ prefixes : Finset P, ∀ pairs : Finset (NonzeroDepthTwoPair v left unit),
      ∀ st : NonzeroDepthTwoPair v left unit → NaturalState Z Bmask bΦ,
      ∀ hQM : ∀ x, (st x).fixedModulus ≤ M,
      ∀ hQη : ∀ x, (st x).fixedModulus ≤ η₀.modulus,
      ∀ z : NonzeroDepthTwoPair v left unit → O,
      ∀ hz : ∀ x, (st x).radial.keep (z x),
      ∀ F : ∀ x, NaturalRow (st x).character (z x),
      ∀ index : NonzeroDepthTwoPair v left unit → Base,
      ∀ holes : NonzeroDepthTwoPair v left unit → Ideal O,
      (∀ x ∈ pairs, x.val.1 ∈ prefixes) →
      (∀ D : Ideal O, ((prefixes.filter (fun p => Ideal.span {v p} = D)).card : ℝ) ≤ A) →
      (∀ x ∈ pairs, holes x ≠ 0) →
      (∀ x ∈ pairs, ∀ I : Ideal O,
        idealCoeff (excluded (F x).character (st x).puncture) I =
          idealCoeff (excluded (naturalRow (base (index x))
            (nonzeroDepthTwoRow x).val (nonzeroDepthTwoRow x).property).character (holes x)) I) →
      (∀ x ∈ pairs, rawFrequencyNorm (nonzeroDepthTwoRow x) ≤ Z^q ∧
        a ≤ zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded (F x).character (st x).puncture))
          (whole_source_family_nonprincipal M H hH (st x) η₀ (hQM x) (hQη x) (z x) (hz x) (F x)) T) →
      (∀ x ∈ pairs, Supported x.val.2.1.1.1 ∧ x.val.2.1.1.2 ≠ 0 ∧ Supported x.val.2.2.1.1 ∧ x.val.2.2.1.2 ≠ 0) →
      (∀ x ∈ pairs, primeSupport x.val.2.1.1.1 = primeSupport x.val.2.1.1.2 ∧
        primeSupport x.val.2.2.1.1 = primeSupport x.val.2.2.1.2) →
      (∀ x ∈ pairs, ((Ideal.span {depthTwoRow v left unit x.val}*firstSourceMissing left x.val.2.1).absNorm : ℝ) ≤
        Z^B) →
      (∀ x ∈ pairs, (x.val.2.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.val.2.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (x.val.2.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.val.2.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ x ∈ pairs, ((firstSourceMissing left x.val.2.1).absNorm : ℝ) ≤ Z^m) →
        (pairs.card : ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss)*A := by
  let bases : Base × WholeSourceIndex M H → Character := fun j => wholeSourceBase M H hH η₀ (base j.1) j.2
  obtain ⟨J, hJ⟩ := actual_depth_two_buffered_high_row_count (Dict := Base × WholeSourceIndex M H) B Q loss hB hQ
    hQB hloss
  obtain ⟨C, hC, hcount⟩ := hJ bases
  refine ⟨J, C, hC, ?_⟩
  intro P v left unit Z hZ q m A a T Bmask bΦ hq ha ha' hT prefixes pairs st hQM hQη z hz F index holes
    hpre hprefix hholes hmask hzero hnonzero heq hsupportnorm hnorm hmissing
  let characters := fun x => wholeSourceFamily M H hH η₀ (excluded (F x).character (st x).puncture)
  have hn := fun x => whole_source_family_nonprincipal M H hH (st x) η₀ (hQM x) (hQη x) (z x) (hz x) (F x)
  apply hcount v left unit Z hZ q m A a T hq ha ha' hT prefixes pairs characters
    (fun x j => (index x, j)) (fun x _ => holes x) (fun _ _ => false) hn hpre hprefix ?_ hzero hnonzero heq
    hsupportnorm hnorm hmissing
  intro x hx j I
  exact whole_source_family_mask M H hH η₀ (base (index x))
    (excluded (F x).character (st x).puncture) (nonzeroDepthTwoRow x).val (nonzeroDepthTwoRow x).property
    (naturalRow (base (index x)) _ (nonzeroDepthTwoRow x).property)
    (holes x) (hholes x hx) (hmask x hx)
    (fun j => naturalRow (wholeSourceBase M H hH η₀ (base (index x)) j)
      (nonzeroDepthTwoRow x).val (nonzeroDepthTwoRow x).property) j I

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
