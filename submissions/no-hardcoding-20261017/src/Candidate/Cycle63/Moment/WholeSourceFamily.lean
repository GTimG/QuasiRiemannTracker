import Candidate.Cycle63.Moment.HighSourceEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open Filter Set HeckeFamily HeckePrimeRay HeckeDetectorZeros ConcreteTraceCRT LocalMoment
open ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open HeckeDetectorFamilyInclusion LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

abbrev WholeSourceIndex := Unit ⊕
  (RayQuotient.Characters M H × RayQuotient.Characters M H)

def wholeSourceFamily (η₀ χ : Character) : WholeSourceIndex M H → Character :=
  Sum.elim (fun _ => χ) (fun j => twistedFamily M H hH
    (χ.product (relativeCharacter M H hH η₀ j.1).inverse.inverse) j.2)

def wholeSourceBase (η₀ η : Character) : WholeSourceIndex M H → Character :=
  Sum.elim (fun _ => η) (fun j =>
    (η.product (relativeCharacter M H hH η₀ j.1).inverse.inverse).product
      (HeckeRayQuotient.character M H hH j.2))

/-- Every plain and further relative ray is a member of the same fixed
natural dictionary, with the actual moving Euler puncture retained. -/
theorem whole_source_family_mask (η₀ η χ : Character) (w : O) (hw : w ≠ 0)
    (F : NaturalRow η w) (R : Ideal O) (hR : R ≠ 0)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff (excluded F.character R) I)
    (G : ∀ j : WholeSourceIndex M H, NaturalRow (wholeSourceBase M H hH η₀ η j) w)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceFamily M H hH η₀ χ j) I =
      idealCoeff (excluded (G j).character R) I := by
  cases j with
  | inl j =>
    have he : ∀ I : Ideal O, idealCoeff F.character I = idealCoeff (G (.inl j)).character I := by
      intro I
      rw [F.ideal I,(G (.inl j)).ideal I]
      rfl
    rw [wholeSourceFamily,Sum.elim_inl,hcoeff I,
      excluded_ideal _ _ hR,
      excluded_ideal _ _ hR,he I]
  | inr j =>
    let ν := (relativeCharacter M H hH η₀ j.1).inverse.inverse
    let F₁ := naturalRow (η.product ν) w hw
    have h₁ := actual_fixed_product_natural_mask η χ ν w F F₁ R hR hcoeff
    exact actual_fixed_product_natural_mask (η.product ν) (χ.product ν)
      (HeckeRayQuotient.character M H hH j.2) w F₁ (G (.inr j)) R hR h₁ I

/-- Nonexceptionality is tested at the actual state's fixed ideal. It
excludes principal plains and every further relative ray. -/
theorem whole_source_family_nonprincipal {Z Bmask bΦ : ℝ}
    (s : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : s.radial.keep z) (F : NaturalRow s.character z) :
    ∀ j : WholeSourceIndex M H,
      (wholeSourceFamily M H hH η₀ (excluded F.character s.puncture) j).residue ≠ 1 := by
  intro j
  cases j with
  | inl j =>
    change (excluded F.character s.puncture).residue ≠ 1
    intro hp
    exact F.nonprincipal (s.row_ne_zero z hz) s.fixedModulus s.puncture
      s.puncture_ne_zero (s.nonexceptional z hz)
      ((HeckeFiniteDeletion.principal_iff_of_mask _ _
        (excludePrimes_mask F.character
          _ (support_prime s.puncture))).mp hp)
  | inr j =>
    exact whole_nonprincipal M H hH s (relativeCharacter M H hH η₀ j.1).inverse hQM
      (relativeCharacter_fixedQ M H hH η₀ j.1 _ hQM hQη) z hz F j.2

/-- One whole-family upper bin supplies all actual relative-slot gates,
including the radial support restriction required by the conductor bound. -/
theorem whole_source_upper_actual_low {Z Bmask bΦ : ℝ}
    (s : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : s.radial.keep z) (a e T : ℝ)
    (hs : s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0)
    (hupper : zeroMaximum
      (wholeSourceFamily M H hH η₀
        (excluded (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture))
      (whole_source_family_nonprincipal M H hH s η₀ hQM hQη z hz
        (naturalRow s.character z (s.row_ne_zero z hz))) T < a+2*e) :
    ActualLow M H hH s η₀ hQM hQη a e T z := by
  refine ⟨hs,?_⟩
  intro hz' θ
  have hχ := whole_nonprincipal M H hH s (relativeCharacter M H hH η₀ θ).inverse hQM
    (relativeCharacter_fixedQ M H hH η₀ θ _ hQM hQη) z hz'
    (naturalRow s.character z (s.row_ne_zero z hz'))
  have hh := zeroMaximum_subfamily
    (twistedFamily M H hH
      ((excluded (naturalRow s.character z (s.row_ne_zero z hz')).character s.puncture).product
        (relativeCharacter M H hH η₀ θ).inverse.inverse))
    (wholeSourceFamily M H hH η₀
      (excluded (naturalRow s.character z (s.row_ne_zero z hz')).character s.puncture)) hχ
    (whole_source_family_nonprincipal M H hH s η₀ hQM hQη z hz'
      (naturalRow s.character z (s.row_ne_zero z hz')))
    (fun θ' => Sum.inr (θ,θ')) (fun _ => rfl) T
  exact hh.trans_lt hupper

/-- Whole inversion leaves the family maximum unchanged, so both physical
orientations use this single partition. -/
theorem whole_source_maximum_inverse (η₀ χ : Character)
    (hn : ∀ j : WholeSourceIndex M H,
      (wholeSourceFamily M H hH η₀ χ j).residue ≠ 1) (T : ℝ) :
    zeroMaximum (fun j => (wholeSourceFamily M H hH η₀ χ j).inverse)
      (fun j => inverse_nonprincipal _ (hn j)) T =
      zeroMaximum (wholeSourceFamily M H hH η₀ χ) hn T :=
  maximum_inverse _ hn T

/-- The actual supported nonexceptional source supplies the whole high
family. No selected zero or principal-character hypothesis is assumed. -/
theorem actual_whole_joint_high_row_count {Base : Type*} [Fintype Base]
    (base : Base → Character) (η₀ : Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (Z : ℝ), 2 ≤ Z → ∀ q m a T Bmask bΦ : ℝ,
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
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

#print axioms actual_whole_joint_high_row_count
#print axioms whole_source_family_mask
#print axioms whole_source_family_nonprincipal
#print axioms whole_source_upper_actual_low
#print axioms whole_source_maximum_inverse
end
end OAI.SevenEighths.Cycle63Moment
