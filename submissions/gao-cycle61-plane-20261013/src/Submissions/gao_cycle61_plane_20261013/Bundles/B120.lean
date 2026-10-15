/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B103
import Submissions.gao_cycle61_plane_20261013.Bundles.B110
import Submissions.gao_cycle61_plane_20261013.Bundles.B114
import Submissions.gao_cycle61_plane_20261013.Bundles.B119
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily

/- BEGIN ORIGINAL Cycle61.Moment.FixedPairMasks; sha256 67ec0c8b7318cf7244a1f301289dd8da259d45de6c4735e72019f44b43b39b80 -/
section
                                        
                                                                         

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open ActualEisensteinCubic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentHeckeColumnWindow CenteredMomentFirstIdealFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentNaturalRowSource CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O

variable {η : Character} {C D : Ideal O} {hC : Supported C}
  {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter}

/-- Recover the primary-element presentation from the height identity of
the exact fixed pair used by the physical source. -/
theorem fixed_pair_left_element (F : FixedPair η C D hC E ξ₁ ξ₂)
    (n : O) (hn : Supported (Ideal.span {n})) (hp : goodLambda^2∣n-1) :
    elementCoeff F.left n=elementCoeff η n*coprimalityMask fixedBadMask n*
      leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)
        (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*
      rayCharacter ξ₁ n := by
  have hn0 : n≠0 := Ideal.span_singleton_eq_bot.not.mp hn.1
  have hh := F.left_height (Ideal.span {n}) hn 0
  rw [rowWeight_one_primary η fixedBadMask 0 _ hn] at hh
  simp only [heightCoeff,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,
    idealCoeff_span _ hn0,CompletedGauss.primaryGenerator_span n hn0 hp] at hh
  exact hh.trans (by ring)

theorem fixed_pair_right_element (F : FixedPair η C D hC E ξ₁ ξ₂)
    (n : O) (hn : Supported (Ideal.span {n})) (hp : goodLambda^2∣n-1) :
    elementCoeff F.right n=elementCoeff η n*coprimalityMask fixedBadMask n*
      rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)
        (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*
      rayCharacter ξ₂ n := by
  have hn0 : n≠0 := Ideal.span_singleton_eq_bot.not.mp hn.1
  have hh := F.right_height (Ideal.span {n}) hn 0
  rw [rowWeight_one_primary η fixedBadMask 0 _ hn] at hh
  simp only [heightCoeff,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,
    idealCoeff_span _ hn0,CompletedGauss.primaryGenerator_span n hn0 hp] at hh
  exact hh.trans (by ring)

/-- The actual physical pair, rather than a separately chosen pair, has
the fixed-parent natural-row masks needed by the joint dictionary. -/
theorem fixed_pair_left_natural_mask (η₀ : Character) (u₀ : O)
    (F₀ : NaturalRow η₀ u₀) (R : Ideal O)
    (F : FixedPair (excluded F₀.character R) C D hC E ξ₁ ξ₂) :
    ∃u : Oˣ,∀G : NaturalRow (childCharacter η₀
      (firstPhaseCharacter C D hC (activeExponent C D)*ξ₁))
      (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*
        firstLeftUncancelled C D),
      ∀I : Ideal O,idealCoeff F.left I=
        if IsCoprime I F.left.modulus then idealCoeff G.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_left_natural_parent_source_mask η₀ u₀ F₀ R fixedBadMask C D hC E ξ₁
  exact ⟨u,hu F.left F.left_modulus (fixed_pair_left_element F)⟩

theorem fixed_pair_right_natural_mask (η₀ : Character) (u₀ : O)
    (F₀ : NaturalRow η₀ u₀) (R : Ideal O)
    (F : FixedPair (excluded F₀.character R) C D hC E ξ₁ ξ₂) :
    ∃u : Oˣ,∀G : NaturalRow (childCharacter η₀
      (firstPhaseCharacter C D hC (fun P=>6-activeExponent C D P)*ξ₂))
      (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*
        firstRightUncancelled C D),
      ∀I : Ideal O,idealCoeff F.right I=
        if IsCoprime I F.right.modulus then idealCoeff G.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_right_natural_parent_source_mask η₀ u₀ F₀ R fixedBadMask C D hC E ξ₂
  exact ⟨u,hu F.right F.right_modulus (fixed_pair_right_element F)⟩

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.fixed_pair_left_element
#print axioms OAI.SevenEighths.Cycle61Moment.fixed_pair_right_element
#print axioms OAI.SevenEighths.Cycle61Moment.fixed_pair_left_natural_mask
#print axioms OAI.SevenEighths.Cycle61Moment.fixed_pair_right_natural_mask

end
/- END ORIGINAL Cycle61.Moment.FixedPairMasks -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.FirstUniformDictionary; sha256 8de2f0e46561498995e653b40a561ebf731f8262f8bb714145a09bbc3b1cdd78 -/
section
                                    
                                        

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentChildRows CenteredMomentNaturalRowSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonSupport RayFourExpansion
open Cycle61Moment
open CenteredMomentFirstPhysicalSource
local notation "O" => HeckeFamily.O

theorem uniform_first_left_single_dictionary (η : Character) (C D : Ideal O)
    (hC : Supported C) :
    ∃ u : Oˣ, ∀ (ξ : RayCharacter) (u₀ e n : O), Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      (elementCoeff η n * idealRowHom u₀ (Ideal.span {n})) *
        leftCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
        rayCharacter ξ n =
      elementCoeff (childCharacter η
        (firstPhaseCharacter C D hC (activeExponent C D)*ξ)) n *
        (∏ P ∈ firstLeftCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom (u₀*(u:O)*e*firstLeftUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_left_signed C D hC
  refine ⟨u,?_⟩
  intro ξ u₀ e n hn hnp
  rw [hu e n hn hnp, ← actual_first_phase_character C D hC (activeExponent C D) n hn,
    idealRowHom_argument_mul, actual_first_left_holes C D n hn,
    childCharacter_primary η _ n hn hnp]
  simp only [rayCharacter, MulChar.mul_apply, idealRowHom_argument_mul]
  ring

theorem uniform_first_right_single_dictionary (η : Character) (C D : Ideal O)
    (hC : Supported C) :
    ∃ u : Oˣ, ∀ (ξ : RayCharacter) (u₀ e n : O), Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      (elementCoeff η n * idealRowHom u₀ (Ideal.span {n})) *
        rightCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
        rayCharacter ξ n =
      elementCoeff (childCharacter η
        (firstPhaseCharacter C D hC (fun P => 6-activeExponent C D P)*ξ)) n *
        (∏ P ∈ firstRightCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom (u₀*(u:O)*e*firstRightUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_right_signed C D hC
  refine ⟨u,?_⟩
  intro ξ u₀ e n hn hnp
  rw [hu e n hn hnp,
    ← actual_first_phase_character C D hC (fun P => 6-activeExponent C D P) n hn,
    idealRowHom_argument_mul, actual_first_right_holes C D n hn,
    childCharacter_primary η _ n hn hnp]
  simp only [rayCharacter, MulChar.mul_apply, idealRowHom_argument_mul]
  ring

theorem uniform_first_left_natural_parent_mask (η : Character) (u₀ : O)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    :
    ∃ u : Oˣ, ∀ (ξ : RayCharacter) (χ : Character),
      χ.modulus = (excluded F₀.character R).modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff (excluded F₀.character R) n * coprimalityMask m n *
          leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (activeExponent C D)*ξ))
        (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstLeftUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := uniform_first_left_single_dictionary η C D hC
  refine ⟨u,?_⟩
  intro ξ χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstLeftCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  have hparent : χ.modulus ≤ (excluded F₀.character R).modulus := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_left
  have hpc := hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hparent)
  rw [hcoeff n hn hp, natural_parent_supported_element η u₀ n F₀ R hn hpc,
    show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu ξ u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem uniform_first_right_natural_parent_mask (η : Character) (u₀ : O)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    :
    ∃ u : Oˣ, ∀ (ξ : RayCharacter) (χ : Character),
      χ.modulus = (excluded F₀.character R).modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff (excluded F₀.character R) n * coprimalityMask m n *
          rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (fun P => 6-activeExponent C D P)*ξ))
        (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstRightUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := uniform_first_right_single_dictionary η C D hC
  refine ⟨u,?_⟩
  intro ξ χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstRightCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  have hparent : χ.modulus ≤ (excluded F₀.character R).modulus := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_left
  have hpc := hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hparent)
  rw [hcoeff n hn hp, natural_parent_supported_element η u₀ n F₀ R hn hpc,
    show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu ξ u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_first_left_single_dictionary
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_first_left_natural_parent_mask
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_first_right_single_dictionary
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_first_right_natural_parent_mask

end
/- END ORIGINAL Cycle61.Physical.InitialMass.FirstUniformDictionary -/

/- BEGIN ORIGINAL Cycle61.Moment.ReflectedJointRow; sha256 c72db40b4cb8da20812c83d68ec21435ac80d55dbc1041ba389fb1d451084475 -/
section
                                           

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondLedger CenteredMomentPartition
local notation "O" => HeckeFamily.O

/-- Negating the residual Fourier row preserves the canonical partition. -/
theorem canonical_partition_neg (C D : Ideal O) (U : Finset (CommonIndex C D)) (z : O) :
    canonicalPartition C D U (-z) ↔ canonicalPartition C D U z := by
  simp only [canonicalPartition,actualUnitSet,dividedFrequency,mul_neg,dvd_neg]
  rfl

def reflectedJointLabel (l : JointSourceLabel) : JointSourceLabel :=
  ⟨l.1,l.2.1,⟨(l.2.2.val.1,-l.2.2.val.2),by
    rw [mul_neg]
    exact (canonical_partition_neg _ _ _ _).mpr l.2.2.property⟩⟩

theorem reflected_joint_row (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (l : JointSourceLabel) :
    jointSourceRow left u₀ unit (reflectedJointLabel l) = -jointSourceRow left u₀ unit l := by
  simp only [jointSourceRow,reflectedJointLabel,effectiveRow]
  ring

theorem reflected_joint_involutive : Function.Involutive reflectedJointLabel := by
  rintro ⟨f,cd,⟨⟨u,z⟩,hp⟩⟩
  simp only [reflectedJointLabel,neg_neg]
  rfl

def reflectedNonzeroJointLabel {left : Bool} {u₀ : O} {unit : FirstSourceLabel→ O}
    (l : NonzeroJointSourceLabel left u₀ unit) : NonzeroJointSourceLabel left u₀ unit :=
  ⟨reflectedJointLabel l.val,by rw [reflected_joint_row];exact neg_ne_zero.mpr l.property⟩

theorem reflected_joint_first_frequency (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (l : JointSourceLabel) :
    jointFirstFrequency left u₀ unit (reflectedJointLabel l)=jointFirstFrequency left u₀ unit l := rfl

theorem reflected_joint_norm {left : Bool} {u₀ : O} {unit : FirstSourceLabel→ O}
    (l : NonzeroJointSourceLabel left u₀ unit) :
    LocalMoment.rawFrequencyNorm (nonzeroJointSourceRow (reflectedNonzeroJointLabel l))=
      LocalMoment.rawFrequencyNorm (nonzeroJointSourceRow l) := by
  simp only [LocalMoment.rawFrequencyNorm,nonzeroJointSourceRow,reflectedNonzeroJointLabel,
    reflected_joint_row,Ideal.span_singleton_neg]

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.canonical_partition_neg
#print axioms OAI.SevenEighths.Cycle61Moment.reflected_joint_row
#print axioms OAI.SevenEighths.Cycle61Moment.reflected_joint_involutive
#print axioms OAI.SevenEighths.Cycle61Moment.reflected_joint_first_frequency

#print axioms OAI.SevenEighths.Cycle61Moment.reflected_joint_norm

end
/- END ORIGINAL Cycle61.Moment.ReflectedJointRow -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondEncodedGates; sha256 b096b3e376ab99d3657c971b8dd78c49cd8eb03028a0c7e897d0d19437797d9d -/
section
                                                  
                                        
                                       

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
local notation "O" => HeckeFamily.O

/-- The signed first numerator cannot vanish on a supported first pair. -/
theorem first_source_numerator_ne_zero (left : Bool)(l : FirstSourceLabel)
    (hC : Supported l.1.1) : firstSourceNumerator left l≠0 := by
  have hn : 0<(Ideal.span {firstSourceNumerator left l}).absNorm := by
    cases left <;> exact powered_numerator_norm_pos _ _ _
      (fun P _=>firstSignedPrime_supported _ _ hC P)
  intro he
  simp only [he,Ideal.span_singleton_zero,Ideal.absNorm_bot] at hn
  omega

/-- Nonzero fixed factor and unit choices make every literal first
frequency nonzero; this is independent of subsequent block cancellation. -/
theorem actual_joint_first_frequency_ne_zero (left : Bool)(u₀ : O)
    (unit : FirstSourceLabel→ O)(l : JointSourceLabel)
    (hu₀ : u₀≠0)(hunit : unit l.1≠0)(hC : Supported l.1.1.1) :
    jointFirstFrequency left u₀ unit l≠0 := by
  unfold jointFirstFrequency
  apply mul_ne_zero _ (first_source_numerator_ne_zero left l.1 hC)
  apply mul_ne_zero (mul_ne_zero hu₀ hunit)
  exact Ideal.span_singleton_eq_bot.not.mp
    (subsetGenerator_supported _ _ hC l.1.2.val).1

/-- Actual live second blocks supply both common-ideal support gates. -/
theorem actual_second_encoded_support {Label : Type*}[Fintype Label]
    (s : Label→ SecondBlockSource)(first : Label→ FirstSourceLabel)
    (hfirst : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2 ∧
      CompletedGauss.primeSupport (first l).1.1=CompletedGauss.primeSupport (first l).1.2)
    (r : secondLiveRows s) :
    let l := secondEncodedRow s first r
    (Supported l.1.1.1 ∧ l.1.1.2≠0 ∧ Supported l.2.1.1 ∧ l.2.1.2≠0) ∧
      (CompletedGauss.primeSupport l.1.1.1=CompletedGauss.primeSupport l.1.1.2 ∧
       CompletedGauss.primeSupport l.2.1.1=CompletedGauss.primeSupport l.2.1.2) := by
  exact ⟨⟨(hfirst r.val.1).1,(hfirst r.val.1).2.1.1,
    (s r.val.1).hC,(s r.val.1).hD.1⟩,⟨(hfirst r.val.1).2.2,(s r.val.1).sameSupport⟩⟩

/-- Reflection keeps distinct encoded rows distinct, so the right column
uses the same joint-count selection without a new multiplicity factor. -/
theorem reflected_nonzero_joint_injective {left : Bool}{u₀ : O}{unit : FirstSourceLabel→ O} :
    Function.Injective (@reflectedNonzeroJointLabel left u₀ unit) := by
  intro l k he
  apply Subtype.ext
  exact reflected_joint_involutive.injective (congrArg Subtype.val he)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_source_numerator_ne_zero
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_first_frequency_ne_zero
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_encoded_support
#print axioms OAI.SevenEighths.Cycle61InitialMass.reflected_nonzero_joint_injective

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondEncodedGates -/
