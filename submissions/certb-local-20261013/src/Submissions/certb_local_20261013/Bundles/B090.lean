/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B028
import Submissions.certb_local_20261013.Bundles.B033
import Submissions.certb_local_20261013.Bundles.B040
import Submissions.certb_local_20261013.Bundles.B055
import Submissions.certb_local_20261013.Bundles.B060
import Submissions.certb_local_20261013.Bundles.B071
import Submissions.certb_local_20261013.Bundles.B083
import Submissions.certb_local_20261013.Bundles.B086
import Submissions.certb_local_20261013.Bundles.B087
import Submissions.certb_local_20261013.Bundles.B088
import Submissions.certb_local_20261013.Bundles.B089
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralTuple
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

/- BEGIN ORIGINAL MODULE Analytic.JointLowValueEnergy ; sha256 3e4f30cee7e4e598a9926cac1b1f06132840a79a0c5321689b06c987e7a3068f -/
section




/-! The actual second children are controlled by the cumulative-common
low source energy, before the Fourier windows are restored. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst
open CenteredMomentActiveSource CenteredMomentSecondRetainedAggregate
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly RayFourExpansion
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentSecondMaskedWindow CenteredMomentSecondSectorEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonRadialSource
open CenteredMomentCommonHeightEnvelope CenteredMomentRadialEligibleEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentExceptionalAmplitudePair
open CenteredMomentCompleteCommon CenteredMomentSecondBlockAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
local notation "O" => HeckeFamily.O
local instance lowValueDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def lowActiveLeftSupported {S : Finset (Ideal O)} {β : Ideal O → ℂ}
    (p : ActiveLabel S β) : Supported p.val.1 :=
  (commonLabels_supported (activeSource S β) _ _ p.property).1

def lowActiveRightSupported {S : Finset (Ideal O)} {β : Ideal O → ℂ}
    (p : ActiveLabel S β) : Supported p.val.2 :=
  (commonLabels_supported (activeSource S β) _ _ p.property).2

lemma secondChildValue_eq_sector_row (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O) (H : ℝ) :
    secondChildValue η t S β C hC A L χ z H =
      (Real.sqrt H : ℂ)⁻¹ * rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I => β (C*I)*heightCoeff η t I)) χ) z := by
  simp only [secondChildValue,rowPolynomial,secondBlockChildCoefficient,sectorElement_span]

/-- This is an exact source inequality, with the actual cumulative common
ideal, original coefficient array, and dyadic normalization. -/
theorem secondChildValue_l2_source
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C L : Ideal O) (hC : Supported C)
    (η ψ : Character) (χ : RayCharacter) (A : O)
    (hψ : ∀ I : Ideal O, Supported I → IsCoprime C I → ∀ t : ℝ,
      heightCoeff ψ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (CompletedGauss.primaryGenerator I))
    (v H : ℝ) (hH : 0 < H) (r : Radial) (rows : Finset O)
    (hkeep : ∀ z ∈ rows,r.keep z)
    (hmajor : ∀ z ∈ rows,1 ≤ (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re) :
    (∑ z ∈ rows,‖secondChildValue η v (original src R seed).columns (original src R seed).beta
      C hC A L χ z H‖^2) ≤
      (volume src.toData/H)*sourceEnergy (withHeight src ψ v) r C hC R seed L := by
  let S := (original src R seed).columns
  let β := (original src R seed).beta
  let coeff := divisorCoefficient L (sectorElement C hC.1 S)
    (movingCoefficient A (sectorElement C hC.1 S)
      (fun I => β (C*I)*heightCoeff η v I)) χ
  have he := finite_energy_le_restricted r.keep Finset.univ (sectorElement C hC.1 S)
    (sectorElement_supported C hC.1 S) coeff r.profile r.scale r.scale_pos rows hkeep r.nonneg hmajor
  have hn (z : O) : ‖secondChildValue η v S β C hC A L χ z H‖^2 =
      H⁻¹*‖rowPolynomial Finset.univ (sectorElement C hC.1 S) coeff z‖^2 := by
    rw [secondChildValue_eq_sector_row,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg H),mul_pow,inv_pow,Real.sq_sqrt hH.le]
  calc
    _ = H⁻¹*∑ z ∈ rows,‖rowPolynomial Finset.univ (sectorElement C hC.1 S) coeff z‖^2 := by
      change (∑ z ∈ rows,‖secondChildValue η v S β C hC A L χ z H‖^2) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => hn z)
    _ ≤ H⁻¹*restrictedEnergy r.keep Finset.univ (sectorElement C hC.1 S) coeff r.profile r.scale :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hH.le)
    _ = H⁻¹*rawCommonSourceEnergy (withHeight src ψ v) r C hC R seed L := by
      rw [masked_child_energy η ψ χ A C hC hψ S β L v r.keep r.profile r.scale]
      rfl
    _ = _ := by rw [rawCommonSourceEnergy_eq]; change H⁻¹*(volume src.toData*_)=_;ring

/-- The first projector and first-common coprimality are discharged by the
actual active second-common label. No absolute coefficient replacement is made. -/
theorem actual_common_second_left_l2
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
    (family : RayCharacter → Character)
    (hfamily : Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family)
    (χ : RayCharacter) (v H : ℝ) (hH : 0 < H) (L : Ideal O) (r : Radial) (rows : Finset O)
    (hkeep : ∀ z ∈ rows,r.keep z)
    (hmajor : ∀ z ∈ rows,1 ≤ (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re) :
    (∑ z ∈ rows,‖secondChildValue η v
      (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 (lowActiveLeftSupported p)
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
      L χ z H‖^2) ≤
      (volume src.toData/H)*sourceEnergy (withHeight src (family χ) v) r (C₁*p.val.1)
        ((supported_mul_iff _ _).mpr ⟨hC₁,(lowActiveLeftSupported p)⟩) R seed L := by
  have hg := actual_second_common_first_projector (original src R seed) C₁ L₁ hC₁ p
  have he (z : O) := common_second_child_eq_complete_source (original src R seed)
    C₁ p.val.1 L₁ hC₁ (lowActiveLeftSupported p) hg.2.2.1 hg.1 η
    (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) z v L χ
  simp only [secondChildValue] at ⊢
  simp_rw [he]
  apply secondChildValue_l2_source src R seed (C₁*p.val.1) L
    ((supported_mul_iff _ _).mpr ⟨hC₁,(lowActiveLeftSupported p)⟩) η (family χ) χ _ _ v H hH r rows hkeep hmajor
  intro I hI hcop t
  exact hfamily.height_eq χ I hI (Or.inl hcop.of_mul_left_right) t

theorem actual_common_second_right_l2
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
    (family : RayCharacter → Character)
    (hfamily : Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family)
    (χ : RayCharacter) (v H : ℝ) (hH : 0 < H) (L : Ideal O) (r : Radial) (rows : Finset O)
    (hkeep : ∀ z ∈ rows,r.keep z)
    (hmajor : ∀ z ∈ rows,1 ≤ (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re) :
    (∑ z ∈ rows,‖secondChildValue η v
      (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.2 (lowActiveRightSupported p)
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
      L χ z H‖^2) ≤
      (volume src.toData/H)*sourceEnergy (withHeight src (family χ) v) r (C₁*p.val.2)
        ((supported_mul_iff _ _).mpr ⟨hC₁,(lowActiveRightSupported p)⟩) R seed L := by
  have hg := actual_second_common_first_projector (original src R seed) C₁ L₁ hC₁ p
  have he (z : O) := common_second_child_eq_complete_source (original src R seed)
    C₁ p.val.2 L₁ hC₁ (lowActiveRightSupported p) hg.2.2.2 hg.2.1 η
    (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) z v L χ
  simp only [secondChildValue] at ⊢
  simp_rw [he]
  apply secondChildValue_l2_source src R seed (C₁*p.val.2) L
    ((supported_mul_iff _ _).mpr ⟨hC₁,(lowActiveRightSupported p)⟩) η (family χ) χ _ _ v H hH r rows hkeep hmajor
  intro I hI hcop t
  exact hfamily.height_eq χ I hI (Or.inr hcop.of_mul_left_right) t

#print axioms secondChildValue_l2_source
#print axioms actual_common_second_left_l2
#print axioms actual_common_second_right_l2
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowValueEnergy -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceInducing ; sha256 bd0b27259b2892a51991b508743a1de9be60f88b9995d362d315d689ebe2ea50 -/
section




/-! The exceptional predicate of the literal physical source is exactly
the predicate on its canonical reconstructed row. Finite Euler deletions
and the two ray choices do not create separate classifications. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeRowClosure HeckeInverseAmplification CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredExceptionalProfile CenteredMomentFixedRowMask
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFixedRay CenteredMomentChildRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
local notation "O" => HeckeFamily.O

lemma fixedInducing_of_row_identity (source parent : Character)
    (m A j w : O) (hw : w ≠ 0) (R : Ideal O) (hR : R ≠ 0)
    (heq : ∀ I : Ideal O, rowWeight source m A j 0 I =
      rowWeight parent (fixedBadMask*idealGenerator R) 1 w 0 I)
    (Q : Ideal O) :
    FixedInducingRow source Q m A j ↔ FixedInducingRow parent Q fixedBadMask 1 w := by
  have ht (n : O) : rowTwist (elementHom source) m 1 (A*j) n =
      rowTwist (elementHom parent) (fixedBadMask*idealGenerator R) 1 w n := by
    rw [←rowWeight_zero_span,←rowWeight_zero_span]
    simpa only [rowWeight,one_mul] using heq (Ideal.span {n})
  have hi : FixedInducingRow source Q m A j ↔
      FixedInducingRow parent Q (fixedBadMask*idealGenerator R) 1 w := by
    constructor
    · rintro ⟨χ, ψ, hp, hi, hQ, hc⟩
      exact ⟨χ, ψ, hp, hi, hQ, fun n => by simpa only [one_mul] using (hc n).trans (ht n)⟩
    · rintro ⟨χ, ψ, hp, hi, hQ, hc⟩
      refine ⟨χ, ψ, hp, hi, hQ, ?_⟩
      intro n
      have hh : elementCoeff χ n = rowTwist (elementHom parent)
          (fixedBadMask*idealGenerator R) 1 w n := by simpa only [one_mul] using hc n
      exact hh.trans (ht n).symm
  exact hi.trans (fixedInducingRow_mul_mask_iff parent Q fixedBadMask (idealGenerator R) 1 w
    fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hw
    (dvd_mul_right _ _) (dvd_mul_left _ _))

theorem PhysicalNaturalPair.inducing_iff {Slot : Type*} [Fintype Slot]
    {η : Character} {w : NonzeroElement} {s : CommonSecondKernelLabel Slot}
    {z : O} {TL TR : Ideal O} (P : PhysicalNaturalPair η w s z TL TR)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) :
    (FixedInducingRow (childCharacter s.parent s.leftRay) Q
      (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.1)))
      s.toKernelLabel.frequency z ↔ FixedInducingRow η Q fixedBadMask 1 w.val) ∧
    (FixedInducingRow (childCharacter s.parent (s.rightRay⁻¹)) Q
      (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.2)))
      s.toKernelLabel.frequency (-z) ↔ FixedInducingRow η Q fixedBadMask 1 w.val) := by
  exact ⟨(fixedInducing_of_row_identity _ _ _ _ _ _ w.property TL P.punctureL_ne
      (P.left_eq 0) Q).trans (jointParentDictionary_inducing_iff η P.parentL Q hQ72 w.val w.property),
    (fixedInducing_of_row_identity _ _ _ _ _ _ w.property TR P.punctureR_ne
      (P.right_eq 0) Q).trans (jointParentDictionary_inducing_iff η P.parentR Q hQ72 w.val w.property)⟩

lemma fixedInducing_of_masked_row_identity (source parent : Character)
    (j w : O) (hj : j ≠ 0) (hw : w ≠ 0)
    (T R : Ideal O) (hT : T ≠ 0) (hR : R ≠ 0)
    (heq : ∀ I : Ideal O,
      rowWeight source (fixedBadMask*idealGenerator T) 1 j 0 I =
      rowWeight parent (fixedBadMask*idealGenerator R) 1 w 0 I)
    (Q : Ideal O) :
    FixedInducingRow source Q fixedBadMask 1 j ↔
      FixedInducingRow parent Q fixedBadMask 1 w := by
  have ht (n : O) :
      rowTwist (elementHom source) (fixedBadMask*idealGenerator T) 1 j n =
      rowTwist (elementHom parent) (fixedBadMask*idealGenerator R) 1 w n := by
    simpa only [rowWeight_zero_span] using heq (Ideal.span {n})
  have hi : FixedInducingRow source Q (fixedBadMask*idealGenerator T) 1 j ↔
      FixedInducingRow parent Q (fixedBadMask*idealGenerator R) 1 w := by
    constructor
    · rintro ⟨χ, ψ, hp, hi, hQ, hc⟩
      refine ⟨χ, ψ, hp, hi, hQ, ?_⟩
      intro n
      simpa only [one_mul] using (hc n).trans (by simpa only [one_mul] using ht n)
    · rintro ⟨χ, ψ, hp, hi, hQ, hc⟩
      refine ⟨χ, ψ, hp, hi, hQ, ?_⟩
      intro n
      simpa only [one_mul] using (hc n).trans (by simpa only [one_mul] using (ht n).symm)
  exact (fixedInducingRow_mul_mask_iff source Q fixedBadMask (idealGenerator T) 1 j
    fixedBadMask_ne_zero (idealGenerator_ne_zero T hT) one_ne_zero hj
    (dvd_mul_right _ _) (dvd_mul_left _ _)).symm.trans
      (hi.trans (fixedInducingRow_mul_mask_iff parent Q fixedBadMask (idealGenerator R) 1 w
        fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hw
        (dvd_mul_right _ _) (dvd_mul_left _ _)))

theorem actual_second_side_inducing_iff
    (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂)
    (left : Bool) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (χ : RayCharacter) (z : O) (hz : z ≠ 0)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) :
    let w := secondReconstructedRow C₁ D₁ hC₁ E₁
      (firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F) C₂ D₂ hC₂ U left z hz
    FixedInducingRow (childCharacter (firstSideCharacter F left) χ) Q m
      (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) z ↔
      FixedInducingRow η Q fixedBadMask 1 w.val := by
  intro w
  obtain ⟨family,hfamily⟩ := exists_exceptional_family (firstSideCharacter F left)
    C₂ D₂ hC₂ hD₂ hCD U
  obtain ⟨parent,N,hh⟩ := actual_second_side_family_row η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F left
    C₂ D₂ hC₂ hD₂ hCD U family hfamily C₂ hC₂.1 (Or.inl dvd_rfl) χ z hz
  have hcancel : firstSideCanceled C₁ D₁ left ≠ 0 := canceledIdeal_ne_zero C₁ D₁ hC₁ _
  exact (hfamily.inducing_iff χ Q m z hm hz hmLam hm2).trans
    ((fixedInducing_of_masked_row_identity (family χ) parent.val z w.val hz w.property
      C₂ (C₂*firstSideCanceled C₁ D₁ left) hC₂.1 (mul_ne_zero hC₂.1 hcancel)
      (hh 0) Q).trans (jointParentDictionary_inducing_iff η parent Q hQ72 w.val w.property))

namespace FirstSidePresentation
variable {η : Character} {Slot : Type*} [Fintype Slot]

theorem inducing_iff (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (χ : RayCharacter) (z : O) (hz : z ≠ 0)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) :
    FixedInducingRow (childCharacter s.parent χ) Q m s.toKernelLabel.frequency z ↔
      FixedInducingRow η Q fixedBadMask 1 (F.row s z hz).val := by
  simpa only [hs, sourceParent, row, SecondKernelLabel.frequency,
    CommonSecondKernelLabel.toKernelLabel] using
    actual_second_side_inducing_iff η F.C F.D F.supported F.active F.leftRay F.rightRay
      F.pair F.side s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD
      s.toKernelLabel.hCD s.partition χ z hz Q hQ72 m hm hmLam hm2

end FirstSidePresentation

#print axioms actual_second_side_inducing_iff
#print axioms FirstSidePresentation.inducing_iff
#print axioms PhysicalNaturalPair.inducing_iff
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceInducing -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceReindex ; sha256 95bc709a4b1bec8ab8aee67081b04ab21a45053785abb683a2213e2c58e89d7e -/
section



/-! The actual dependent first/second common indices inject into one joint
arithmetic label. Rays and dyadic sectors stay fixed outside this map. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationChildInput
open CenteredMomentCanonicalFirst CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentFixedRay RayFourExpansion
local notation "O" => HeckeFamily.O

variable {Slot : Type*} [Fintype Slot]

def sourceFirstCommon (side : Bool) (p : Ideal O × Ideal O) : Ideal O :=
  if side then p.1 else p.2

theorem sourceFirstCommon_supported (s : OriginalData Slot) (side : Bool)
    (p : ActiveLabel s.columns s.beta) : Supported (sourceFirstCommon side p.val) := by
  have h := commonLabels_supported (activeSource s.columns s.beta) _ _ p.property
  cases side
  · exact h.2
  · exact h.1

/-- Literal active common pairs, first projector, second partition and residual
frequency. The second projector and every ray/dyadic choice remain external. -/
abbrev ActualJointSourceRow (s : OriginalData Slot) (side : Bool) :=
  (first : ActiveLabel s.columns s.beta) ×
    (E : Finset (CommonIndex first.val.1 first.val.2)) ×
    (L : Ideal O) ×
    (second : ActiveLabel
      (commonSecondColumns s (sourceFirstCommon side first.val)
        (sourceFirstCommon_supported s side first))
      (commonSecondBeta s (sourceFirstCommon side first.val) L)) ×
    (U : Finset (CommonIndex second.val.1 second.val.2)) × O

namespace ActualJointSourceRow
variable {s : OriginalData Slot} {side : Bool}

abbrev first (q : ActualJointSourceRow s side) := q.1
abbrev E (q : ActualJointSourceRow s side) := q.2.1
abbrev L (q : ActualJointSourceRow s side) := q.2.2.1
abbrev second (q : ActualJointSourceRow s side) := q.2.2.2.1
abbrev U (q : ActualJointSourceRow s side) := q.2.2.2.2.1
abbrev z (q : ActualJointSourceRow s side) := q.2.2.2.2.2

def baseLabel (q : ActualJointSourceRow s side) : JointReconstructionLabel where
  C₁ := q.first.val.1
  D₁ := q.first.val.2
  C₂ := q.second.val.1
  D₂ := q.second.val.2
  E := q.E
  U := q.U
  L := q.L
  h := q.z

def label (q : ActualJointSourceRow s side) : JointReconstructionLabel :=
  if side then q.baseLabel else q.baseLabel.swapFirst

theorem baseLabel_injective : Function.Injective (baseLabel (s := s) (side := side)) := by
  intro q q' he
  rcases q with ⟨p,E,L,r,U,z⟩
  rcases q' with ⟨p',E',L',r',U',z'⟩
  have hp : p = p' := Subtype.ext (Prod.ext
    (congrArg JointReconstructionLabel.C₁ he) (congrArg JointReconstructionLabel.D₁ he))
  subst p'
  have hL : L = L' := congrArg JointReconstructionLabel.L he
  subst L'
  have hr : r = r' := Subtype.ext (Prod.ext
    (congrArg JointReconstructionLabel.C₂ he) (congrArg JointReconstructionLabel.D₂ he))
  subst r'
  have hE : E = E' := by
    have h := congrArg (fun v : JointReconstructionLabel => v.E.image Subtype.val) he
    exact Finset.image_injective Subtype.val_injective h
  have hU : U = U' := by
    have h := congrArg (fun v : JointReconstructionLabel => v.U.image Subtype.val) he
    exact Finset.image_injective Subtype.val_injective h
  have hz : z = z' := congrArg JointReconstructionLabel.h he
  subst E'; subst U'; subst z'
  rfl

theorem label_injective : Function.Injective (label (s := s) (side := side)) := by
  intro q q' h
  apply baseLabel_injective
  cases side
  · exact JointReconstructionLabel.swapFirst_injective h
  · exact h

def labelEmbedding : ActualJointSourceRow s side ↪ JointReconstructionLabel :=
  ⟨label,label_injective⟩

theorem label_supported (q : ActualJointSourceRow s side) :
    Supported q.label.C₁ ∧ Supported q.label.D₁ ∧
      Supported q.label.C₂ ∧ Supported q.label.D₂ := by
  have h₁ := commonLabels_supported (activeSource s.columns s.beta) _ _ q.first.property
  have h₂ := commonLabels_supported (activeSource _ _) _ _ q.second.property
  cases side <;> simp only [label,Bool.false_eq_true,ite_false,ite_true,baseLabel,
    JointReconstructionLabel.swapFirst]
  · exact ⟨h₁.2,h₁.1,h₂.1,h₂.2⟩
  · exact ⟨h₁.1,h₁.2,h₂.1,h₂.2⟩

theorem label_equal_support (q : ActualJointSourceRow s side) :
    primeSupport q.label.C₁ = primeSupport q.label.D₁ ∧
      primeSupport q.label.C₂ = primeSupport q.label.D₂ := by
  have h₁ := (commonLabels_data _ _ _ _ q.first.property).2.2
  have h₂ := (commonLabels_data _ _ _ _ q.second.property).2.2
  cases side <;> simp only [label,Bool.false_eq_true,ite_false,ite_true,baseLabel,
    JointReconstructionLabel.swapFirst]
  · exact ⟨h₁.symm,h₂⟩
  · exact ⟨h₁,h₂⟩

/-- Exact finite reindexing, with no arithmetic cardinality factor. -/
theorem sum_label_image {M : Type*} [AddCommMonoid M]
    (rows : Finset (ActualJointSourceRow s side)) (f : JointReconstructionLabel → M) :
    (∑ v ∈ rows.image label, f v) = ∑ q ∈ rows, f q.label :=
  Finset.sum_image (fun _ _ _ _ he => label_injective he)

theorem card_label_image (rows : Finset (ActualJointSourceRow s side)) :
    (rows.image label).card = rows.card := Finset.card_image_of_injective _ label_injective

end ActualJointSourceRow
#print axioms ActualJointSourceRow.label_injective
#print axioms ActualJointSourceRow.sum_label_image
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceReindex -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowCentralTuple ; sha256 d485f4bddfd5c65d5ac7702e53f6d84028c4f7cc8c75c73e5491e09809aeff5b -/
section




/-! Adapted from OpenAI/math family003, pinned original module Detector.LowCentralTuple.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical ContDiff
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_compensated_sqrt_factor (q L : ℝ) (hq : 0≤ q) (hL : 0< L) :
    Real.sqrt (3*q/L)=Real.sqrt (3*q)*L^(-(1/2:ℝ)) := by
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,Real.sqrt_eq_rpow,Real.rpow_neg hL.le]

theorem low_central_compensated_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0< X→
      Z^(1+lowSelectedLength ell J-ε/2)≤ X→X≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) X t*
          selectedSlotFactor W (fun i=> Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := lowUnselectedMass_decay K 1 a (by norm_num) ha
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0< q := calibration_elementNorm_pos _
  let C0 := Cg*Ci*Real.sqrt (3*q)*Cu
  have hC0 : 0< C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,eventually_original_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=> canonicalSlotSupport (T i)
  let Yp := fun i=> Z^(ell i)
  have hz : 0< Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n≤ max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+((Submission20261012.Global.ly/2))*ε:ℝ)
  let V := Ci*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2)
  have hGV : G*V≤ Ci*(1+‖t‖)^degree*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε+lowUnselectedLength ell J/2) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+((Submission20261012.Global.ly/2))*ε:ℝ)*Z^((lowUnselectedLength ell J+507*ε)/2)) := by ring
      _≤_ := by
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by nlinarith [Submission20261012.Global.ly_lt_half])
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε+lowUnselectedLength ell J/2))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(-(1/2:ℝ))) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤ lowGramFactor (calibrationForSet S hS) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤ V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε+lowUnselectedLength ell J/2)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _=_ := by rw [low_compensated_sqrt_factor q L hq.le hL];ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=> hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hlo : ∀i n,n∈canonicalSlotSupport (T i)→a*Z^(ell i)≤ elementNorm n := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).1
  have hm := hmass ell Z hz T hT hlo J W Yp hW
  calc
    _≤ Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε+lowUnselectedLength ell J/2))*(Cu*Z^(-lowUnselectedLength ell J/2))) := by gcongr
    _=_ := by
      have he : Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε+lowUnselectedLength ell J/2)*Z^(-lowUnselectedLength ell J/2)=Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      dsimp [C0]
      linear_combination (Cg*Ci*Real.sqrt (3*q)*Cu*(1+‖t‖)^degree)*he

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowCentralTuple -/

/- BEGIN ORIGINAL MODULE Analytic.ActualAllocatedErrors ; sha256 29a2e3fc0b5fe207cdd50b88f6bc0f07926ee2db91862a5ce6a5544e30683b5e -/
section



/-! Actual extracted error estimates with Ready discharged by source caps.
Dead extracted sources vanish exactly. Every live extracted source receives
its Ready packet from the pinned source theorem before the genuine analytic
estimate is used. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance actualAllocatedErrorsDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance actualAllocatedErrorsFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates


open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstLiveAdmission

open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentPrimeElements CenteredMomentPrimePool

theorem actual_allocated_extracted_errors
    (Wslot:ℝ→ℂ)(aslot bslot Mcap εremove lo hi εchild:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(haUpper:a≤1/4)(hbPlain:1≤ b)
    (L:ℝ)(hL:0≤ L)
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)(hMcap:0< Mcap)
    (hεchild:0<εchild)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost) (hsigma_eq : sigma=9/500)
    (Avol Dscale Pmask qmoving εgeo : ℝ) (hεgeo : 0 < εgeo)
    (hbudget : CenteredMomentFirstSecondInputGates.exponent Avol Dscale Pmask qmoving εgeo ξ ≤ Bcap)
    (εalloc : ℝ) (hεalloc : 0 < εalloc):
    ∃ Calloc : ℝ, 0 < Calloc ∧
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(τ:Character)(t:ℝ),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
    P.Nonempty →
    (∀ (B : actualAllocations src.pools C), frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      ∀ (prime : elementPool P) i, ∀ I∈(activeInput (child src C R0 B τ t)).slots i,
      IsCoprime (Ideal.span {prime.val}) I) →
    ∀ family : actualAllocations src.pools C → elementPool P → Fin 3 → RayCharacter → Character,
    (∀ B, frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      ∀ prime i χ, (family B prime i χ).modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    (∀ B, frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      ∀ prime i χ, ((family B prime i χ).modulus.absNorm:ℝ)≤
      cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (errorIndex i+1))) →
    let radius := fun (prime : elementPool P) (i : Fin 3) => errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (errorIndex i+1)
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol →
    (R0.absNorm : ℝ)≤ Z^Pmask → R0≠0 →
    (∀ prime i, (radius prime i)⁻¹≤ Z^Dscale) →
    (∀ B, frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      ∀ prime i χ, ((family B prime i χ).modulus.absNorm : ℝ)≤ Z^qmoving) →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀profile:Profiles a b,profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀ Mgeom Mvolume : ℝ, 1≤ Mgeom →
    Z^(Mgeom/4)≤ src.X₁ → Z^(Mgeom/4)≤ src.X₂ →
    Z^(Mgeom/4)≤ src.Y₁ → Z^(Mgeom/4)≤ src.Y₂ →
    Mgeom≤ Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
    Real.logb Z (volume src)≤(883/1000)*Mgeom →
    Real.logb Z (volume src)≤ Mvolume →
    Real.logb Z fixedPresentationCost≤1/1000 →
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤429/100000 →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    allocatedExtractedErrors N src C R0 seed τ t upper Z
      (Real.logb Z (D.absNorm : ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve P family/
      ((τ.modulus.absNorm : ℝ)*(volume src/(C.absNorm : ℝ)^2)*Z^(allowance C D Z)) ≤
      Calloc*(C.absNorm : ℝ)^εalloc*mass src^2*
        (56*1872*(Fintype.card RayCharacter : ℝ))*
          ∑ j : Fin 4,
            (Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
              Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm : ℝ))*
            (upper^N)^(powers εsrc j)*
            Z^(localErrorExponents paid εsrc Mvolume saving delta reserve j) := by
  obtain ⟨Calloc,hCalloc,halloc⟩ := allocated_error_reference_bound N upper εalloc hupper hεalloc
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_firstExtractedErrors_local_average (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget
  refine ⟨Calloc,hCalloc,Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E τ t hmod K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hP hslot family hrad hfamily
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
    hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
  let paid := (Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
  let budget := (56*1872*(Fintype.card RayCharacter : ℝ))*∑ j : Fin 4,
    (Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
      Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm : ℝ))*
    (upper^N)^(powers εsrc j)*Z^(localErrorExponents paid εsrc Mvolume saving delta reserve j)
  have hz := zero_lt_one.trans hZ.1
  have hbudget0 : 0 ≤ budget := by
    dsimp [budget]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hh := halloc src hcard C R0 seed hC.1 τ t Z (Real.logb Z (D.absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve (allowance C D Z) budget hz hbudget0 P family ?_
  · simpa only [budget,mul_assoc] using hh
  · intro B hB
    have hb := hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
      hP (hslot B hB) (family B) (hrad B hB) (hfamily B hB)
      hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv (hconductorCap B hB) seed hseed hseed0 hseedcap
      profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
      hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
    simpa only [budget,paid,mul_assoc] using hb

#print axioms actual_allocated_extracted_errors
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualAllocatedErrors -/

/- BEGIN ORIGINAL MODULE Analytic.JointCancellationSectors ; sha256 69c8673b91aed7c1100aff2ea362db2336e2f77fa61f8c4d89571573c4421864 -/
section




/-! The two additional first-width coordinates needed by joint population
have bounded finite sector ranges before any source labels are selected. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CanonicalRowCompletion CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

namespace ActualJointSourceRow
variable {Slot : Type*} [Fintype Slot] {s : CenteredMomentFirstAmplificationChoice.OriginalData Slot} {side : Bool}

def cancellationCoordinates (q : ActualJointSourceRow s side) (Z : ℝ) : Fin 2 → ℝ :=
  ![Real.logb Z (normValue (leftEffectiveFactor q.label.C₁ q.label.D₁)),
    Real.logb Z ((canceledIdeal q.label.C₁ q.label.D₁ 5).absNorm : ℝ)]

theorem cancellation_coordinates_bounds (q : ActualJointSourceRow s side) (Z B : ℝ)
    (hZ : 1< Z) (hB : 0≤ B) (hC : (q.label.C₁.absNorm : ℝ)≤ Z^B) :
    ∀ j,0≤ q.cancellationCoordinates Z j ∧ q.cancellationCoordinates Z j≤5*B := by
  have hc := left_cancellation_sector_caps q.label.C₁ q.label.D₁ q.label_supported.1 Z B hZ hC
  intro j
  fin_cases j
  · exact ⟨hc.2.2.1,hc.2.2.2⟩
  · exact ⟨hc.1,hc.2.1.trans (by linarith)⟩

/-- Taking upper sector edges for L and R₀ costs six mesh widths in
L≤5(R−R₀); this is charged explicitly rather than forcing exact widths. -/
theorem cancellation_upper_edge_budget (q : ActualJointSourceRow s side)
    (Z R L R₀ e : ℝ) (hZ : 1< Z)
    (hR : Real.logb Z (normValue (activeConductor q.label.C₁ q.label.D₁))≤ R)
    (hL : L≤ q.cancellationCoordinates Z 0+e)
    (hR₀ : R₀≤ q.cancellationCoordinates Z 1+e) :
    L≤5*(R-R₀)+6*e := by
  have hh := left_effective_canceled_log q.label.C₁ q.label.D₁ q.label_supported.1 Z hZ
  simp only [cancellationCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one] at hL hR₀
  linarith

end ActualJointSourceRow

theorem uniform_cancellation_sector_count (B e : ℝ) (hB : 0≤ B) (he : 0< e) :
    ∃ N : ℕ,∀ {Row Slot : Type*} [Fintype Slot]
      (s : CenteredMomentFirstAmplificationChoice.OriginalData Slot) (side : Bool)
      (labels : Finset Row) (q : Row → ActualJointSourceRow s side) (Z : ℝ),1< Z →
      (∀ x∈labels,((q x).label.C₁.absNorm : ℝ)≤ Z^B) →
      ∃ bin : (x : Row) → x∈labels → (Fin 2 → Fin (N+1)),
        ∀ x hx j,0≤(bin x hx j).val*e ∧
          (bin x hx j).val*e≤(q x).cancellationCoordinates Z j ∧
          (q x).cancellationCoordinates Z j<(bin x hx j).val*e+e := by
  obtain ⟨N,hN⟩ := exists_nat_ge (5*B/e)
  refine ⟨N,?_⟩
  intro Row Slot inst s side labels q Z hZ hcap
  have hb x (hx : x∈labels) j := (q x).cancellation_coordinates_bounds Z B hZ hB (hcap x hx) j
  let bin : (x : Row) → x∈labels → (Fin 2 → Fin (N+1)) := fun x hx j =>
    ⟨Nat.floor ((q x).cancellationCoordinates Z j/e),Nat.lt_succ_of_le
      (Nat.floor_le_of_le ((div_le_iff₀ he).mpr ((hb x hx j).2.trans ((div_le_iff₀ he).mp hN))))⟩
  refine ⟨bin,?_⟩
  intro x hx j
  have hl := Nat.floor_le (div_nonneg (hb x hx j).1 he.le)
  have hh := Nat.lt_floor_add_one ((q x).cancellationCoordinates Z j/e)
  change 0≤(Nat.floor ((q x).cancellationCoordinates Z j/e) : ℝ)*e ∧
    (Nat.floor ((q x).cancellationCoordinates Z j/e) : ℝ)*e≤_ ∧
    _<(Nat.floor ((q x).cancellationCoordinates Z j/e) : ℝ)*e+e
  refine ⟨by positivity,(le_div_iff₀ he).mp hl,?_⟩
  have hh' := (div_lt_iff₀ he).mp hh
  nlinarith

#print axioms ActualJointSourceRow.cancellation_upper_edge_budget
#print axioms uniform_cancellation_sector_count
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCancellationSectors -/
