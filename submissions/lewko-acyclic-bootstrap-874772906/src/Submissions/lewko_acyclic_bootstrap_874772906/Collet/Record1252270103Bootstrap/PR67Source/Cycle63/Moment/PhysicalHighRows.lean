import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.SecondNaturalMask
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical
open HeckeFamily LocalMoment ProbePhysical CenteredMomentNaturalRowSource
open CanonicalQuadraticSieve IdealMobiusDivisorSum
open RayFourExpansion
local notation "O" => HeckeFamily.O

def wholeOrientation (χ : Character) (reverse : Bool) : Character :=
  if reverse then χ.inverse else χ

theorem whole_orientation_coefficients (χ ψ : Character)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I) (reverse : Bool) :
    ∀ I : Ideal O, idealCoeff (wholeOrientation χ reverse) I =
      idealCoeff (wholeOrientation ψ reverse) I := by
  intro I
  cases reverse
  · exact hcoeff I
  · change idealCoeff χ.inverse I = idealCoeff ψ.inverse I
    rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj, hcoeff I]

def orientedFixedBase {Dict : Type*} (base : Dict → Character) (j : Dict × Bool) : Character :=
  base j.1

/-- This transfers zeros of the literal second character, rather than zeros
of a Fourier summand. The Euler deletion and whole orientation are retained. -/
theorem physical_zero_to_fixed_dictionary {Dict : Type*} (base : Dict → Character)
    (χ : Character) (j : Dict) (w : NonzeroFrequency)
    (R : Ideal O) (reverse : Bool)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I =
      idealCoeff (excluded (naturalRow (base j) w.val w.property).character R) I)
    (a T : ℝ) (ha : 0 < a)
    (hz : ∃ s : ℂ, LFunction (wholeOrientation χ reverse) s = 0 ∧
      (s ≠ 1 ∨ (wholeOrientation χ reverse).residue ≠ 1) ∧
      a ≤ s.re ∧ |s.im| ≤ T) :
    naturalActualZeroRow (orientedFixedBase base) Prod.snd a T w := by
  obtain ⟨s,hzero,hpole,hs,ht⟩ := hz
  let F := (naturalRow (base j) w.val w.property).character
  let ψ := excluded F R
  have he := positive_zeros_eq_of_coefficients (wholeOrientation χ reverse)
    (wholeOrientation ψ reverse)
    (whole_orientation_coefficients χ ψ hcoeff reverse) (ha.trans_le hs) hpole
  have hm : ∀ I : Ideal O, idealCoeff (wholeOrientation ψ reverse) I =
      if IsCoprime I (wholeOrientation ψ reverse).modulus then
        idealCoeff (wholeOrientation F reverse) I else 0 := by
    have hb : ∀ I : Ideal O, idealCoeff ψ I =
        if IsCoprime I ψ.modulus then idealCoeff F I else 0 :=
      fun I => excludePrimes_mask F _ (support_prime R) I
    cases reverse
    · exact hb
    · exact inverse_coefficient_mask ψ F hb
  have hp := positive_zeros_eq_of_mask_nonpole
    (wholeOrientation ψ reverse) (wholeOrientation F reverse) hm
    (ha.trans_le hs) he.2
  refine ⟨(j,reverse),s,?_,?_,hs,ht⟩
  · exact hp.1.mp (he.1.mp hzero)
  · exact hp.2

/-- A genuine high-bin maximum supplies a positive nonpole zero of the
fixed natural dictionary. The live whole-character family and all moving
Euler holes remain literal through maximum attainment and zero transfer. -/
theorem physical_family_maximum_to_fixed_dictionary
    {Dict Family : Type*} [Fintype Family] (base : Dict → Character)
    (character : Family → Character) (reverse : Family → Bool)
    (hchar : ∀ j, (wholeOrientation (character j) (reverse j)).residue ≠ 1)
    (dictionary : Family → Dict) (puncture : Family → Ideal O)
    (w : NonzeroFrequency)
    (hcoeff : ∀ j, ∀ I : Ideal O, idealCoeff (character j) I =
      idealCoeff (excluded (naturalRow (base (dictionary j)) w.val w.property).character
        (puncture j)) I)
    (a T : ℝ) (ha : 51/100 < a)
    (hmax : a ≤ HeckeDetectorZeros.zeroMaximum
      (fun j => wholeOrientation (character j) (reverse j)) hchar T) :
    naturalActualZeroRow (orientedFixedBase base) Prod.snd a T w := by
  obtain ⟨j,s,hzero,hheight,hre⟩ := HeckeDetectorZeros.maximum_attained
    (fun j => wholeOrientation (character j) (reverse j)) hchar T (ha.trans_le hmax)
  exact physical_zero_to_fixed_dictionary base (character j) (dictionary j) w
    (puncture j) (reverse j) (hcoeff j) a T (by linarith)
    ⟨s,hzero,Or.inr (hchar j),by rw [hre]; exact hmax,hheight⟩

/-- High-bin cardinality from the actual finite whole-family zero maximum,
with constants chosen before every live masked family and height. -/
theorem actual_joint_buffered_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
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
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
