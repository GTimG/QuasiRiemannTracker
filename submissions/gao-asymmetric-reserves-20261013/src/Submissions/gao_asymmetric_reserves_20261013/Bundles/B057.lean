/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B002
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B031
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B045
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B047
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B048
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B050
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B051
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B053
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B054
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.LowBandEmpty
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.LowBandSubtype
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PositiveLowBandSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PositiveLowSourceControlled
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.StageMonotonicity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSourceMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask

/- BEGIN ORIGINAL MODULE Analytic.JointHighProduct ; sha256 5e26907b19bbc312d611ef5e2b1bd7bee1c0d4596db2c532597c01662e8b6651 -/
section



/-! The actual paired-product payment on a jointly counted high bin.
First labels remain in the population throughout; neither parent labels
nor the second projector create another arithmetic counting factor. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma norm_pair_of_squared_bounds (Z C EL ER : ℝ) (x y : ℂ)
    (hZ : 0 < Z) (hC : 0 ≤ C)
    (hx : ‖x‖^2 ≤ C*Z^EL) (hy : ‖y‖^2 ≤ C*Z^ER) :
    ‖x‖*‖y‖ ≤ C*Z^((EL+ER)/2) := by
  have hsq : (C*Z^((EL+ER)/2))^2 = (C*Z^EL)*(C*Z^ER) := by
    simp only [pow_two]
    have he : (EL+ER)/2+(EL+ER)/2 = EL+ER := by ring
    calc
      C*Z^((EL+ER)/2)*(C*Z^((EL+ER)/2)) =
        C*C*(Z^((EL+ER)/2)*Z^((EL+ER)/2)) := by ring
      _ = C*C*Z^(EL+ER) := by rw [← Real.rpow_add hZ, he]
      _ = C*Z^EL*(C*Z^ER) := by rw [Real.rpow_add hZ]; ring
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)).mp
  rw [hsq, mul_pow]
  exact mul_le_mul hx hy (sq_nonneg _) (by positivity)

lemma squared_bound_change_base (Z d dmax δ ell cap loss C : ℝ) (x : ℂ)
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hd : d ≤ dmax) (hloss : 0 ≤ loss)
    (hcap : d*ell ≤ cap) (hC : 0 ≤ C)
    (hx : ‖x‖^2 ≤ C*(Z^d)^(δ*ell+loss)) :
    ‖x‖^2 ≤ C*Z^(δ*cap+dmax*loss) := by
  apply hx.trans
  apply mul_le_mul_of_nonneg_left _ hC
  rw [← Real.rpow_mul (by linarith : 0 ≤ Z)]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  nlinarith [mul_le_mul_of_nonneg_left hcap hδ,
    mul_le_mul_of_nonneg_right hd hloss]

section FixedData
variable {Slot : Type*} [Fintype Slot]
variable (η : Character) (η₀ : Slot → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

/-- The paired norm product over one actual joint high bin. Both factors
have the same reconstructed row, with their own fixed ray parent, literal
puncture and independent plain profiles. Their lengths are averaged only
after the source squared estimates, giving `A-c-b₂` exactly. -/
theorem actual_joint_high_product
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (Rwidth dmax τ ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ (n J : ℕ) (C : ℝ), 0 < C ∧
      ∀ (Z d P W : ℝ), 1 < Z → 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ →
      P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (DL DR : ∀ v, JointBufferedProductData η (w v) Slot n profileBound p.lower e),
      (∀ v ∈ S, (DL v).Admissible M H hH η₀ Aprofile Bprofile
        Rwidth τ ηaux σmin σmax Z d p.height) →
      (∀ v ∈ S, (DR v).Admissible M H hH η₀ Aprofile Bprofile
        Rwidth τ ηaux σmin σmax Z d p.height) →
      ∀ A c c₂ d₂ b₂ : ℝ, 2*b₂ = c₂+d₂ →
      (∀ v ∈ S, d*(DL v).length ≤ A-c-c₂) →
      (∀ v ∈ S, d*(DR v).length ≤ A-c-d₂) →
      (∑ v ∈ S, ‖(DL v).value M H η₀ V Bprofile Z d‖ *
        ‖(DR v).value M H η₀ V Bprofile Z d‖) ≤
        C*(1+|p.height|)^J *
          Z^(unmarkedDensity (2*p.lower-1)*W+P+(2*p.lower-1)*(A-c-b₂)+loss) := by
  obtain ⟨n,Cp,hCp,hpoint⟩ := joint_buffered_data_bound M H hH η η₀ Q hQ72 hQM hQη₀
    V Aprofile Bprofile hA hVs hV Rwidth dmax τ ε e κ ηaux σmin σmax productLoss
    hRw hdmax hτ hε he he' hκ hκone hη hbudget hprimebudget hproductLoss profileBound hprofile
  obtain ⟨J,K,hK,hcount⟩ := actual_joint_natural_population η
    (relativeSlotTranslate M H hH η₀) Q hQtop hQ72 hQη
    (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) hβ M H hH S₀
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
    B populationLoss hB hpopulationLoss
  refine ⟨n,J,K*Cp,mul_pos hK hCp,?_⟩
  intro Z d P W hZ hd hdmax' hbase hT hPB hWB p hp unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr DL DR hDL hDR A c c₂ d₂ b₂ hb₂ hlenL hlenR
  have hcount' : (S.card : ℝ) ≤
      K*(1+|p.height|)^J*Z^(unmarkedDensity (2*p.lower-1)*W+P+populationLoss) := by
    apply hcount Z P W hZ hPB hWB p unit S R hR hsup heq hproj _ hnorm
    · intro v hv
      simpa only [← hw v hv] using hNw v hv
    · intro v hv
      simpa only [← hw v hv] using hNr v hv
    · intro v hv
      have hrow : v.row (unit v) ≠ 0 := by rw [← hw v hv]; exact (w v).property
      refine ⟨hrow,?_⟩
      have hweq : (⟨v.row (unit v),hrow⟩ : NonzeroElement) = w v :=
        Subtype.ext (hw v hv).symm
      rw [hweq]
      exact hbin v hv
  have hploss : 0 ≤ productLoss := by
    have hcard : (0 : ℝ) ≤ (Fintype.card Slot : ℝ) := by positivity
    have hpos : 0 ≤ (2+2*(Fintype.card Slot : ℝ))*ε := mul_nonneg (by positivity) hε.le
    exact hpos.trans hproductLoss
  have hδ : 0 ≤ 2*p.lower-1 := by linarith [p.lower_bound]
  have hpair (v : JointReconstructionLabel) (hv : v ∈ S) :
      ‖(DL v).value M H η₀ V Bprofile Z d‖ * ‖(DR v).value M H η₀ V Bprofile Z d‖ ≤
      Cp*Z^((2*p.lower-1)*(A-c-b₂)+dmax*productLoss) := by
    have hleft := squared_bound_change_base Z d dmax (2*p.lower-1) (DL v).length
      (A-c-c₂) productLoss Cp _ hZ.le hδ hdmax' hploss (hlenL v hv) hCp.le
      (hpoint Z d hZ.le hd hdmax' hbase hT p hp (w v) (R v) (hR v) (hbin v hv) (DL v) (hDL v hv))
    have hright := squared_bound_change_base Z d dmax (2*p.lower-1) (DR v).length
      (A-c-d₂) productLoss Cp _ hZ.le hδ hdmax' hploss (hlenR v hv) hCp.le
      (hpoint Z d hZ.le hd hdmax' hbase hT p hp (w v) (R v) (hR v) (hbin v hv) (DR v) (hDR v hv))
    have he : ((2*p.lower-1)*(A-c-c₂)+dmax*productLoss+
        ((2*p.lower-1)*(A-c-d₂)+dmax*productLoss))/2 =
        (2*p.lower-1)*(A-c-b₂)+dmax*productLoss := by nlinarith [hb₂]
    simpa only [he] using norm_pair_of_squared_bounds Z Cp _ _ _ _
      (zero_lt_one.trans hZ) hCp.le hleft hright
  calc
    (∑ v ∈ S, ‖(DL v).value M H η₀ V Bprofile Z d‖ *
        ‖(DR v).value M H η₀ V Bprofile Z d‖) ≤
        (S.card : ℝ)*(Cp*Z^((2*p.lower-1)*(A-c-b₂)+dmax*productLoss)) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpair
    _ ≤ (K*(1+|p.height|)^J*Z^(unmarkedDensity (2*p.lower-1)*W+P+populationLoss))*
        (Cp*Z^((2*p.lower-1)*(A-c-b₂)+dmax*productLoss)) :=
      mul_le_mul_of_nonneg_right hcount' (by positivity)
    _ = (K*Cp)*(1+|p.height|)^J *
        Z^(unmarkedDensity (2*p.lower-1)*W+P+(2*p.lower-1)*(A-c-b₂)+
          (populationLoss+dmax*productLoss)) := by
      rw [show unmarkedDensity (2*p.lower-1)*W+P+(2*p.lower-1)*(A-c-b₂)+
          (populationLoss+dmax*productLoss) =
          (unmarkedDensity (2*p.lower-1)*W+P+populationLoss)+
          ((2*p.lower-1)*(A-c-b₂)+dmax*productLoss) by ring]
      simp only [Real.rpow_add (zero_lt_one.trans hZ)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity)

end FixedData
#print axioms actual_joint_high_product
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighProduct -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondAllocated ; sha256 a5d2c144253add51687799f83f26433bdd42a778d7515755d11683b94478aa1d -/
section






/-! Literal second children, common allocations, and retained rectangles.
No common-label or allocation cardinality is inserted in these identities. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentSecondSectorColumns
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentOriginalChildEnergy CenteredMomentLiveDomain CenteredMomentLiveSupport
open CenteredMomentAmplificationLiveMask CenteredMomentSourceRectangle
open CenteredMomentSourceRectangleMask CenteredMomentDivisorRowEnergy
open CenteredMomentChildAssembly CenteredMomentChildRows RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCompleteCommon CenteredMomentSecondSourceMask
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate
local notation "O" => HeckeFamily.O

theorem commonSecondBeta_nonzero {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C L I : Ideal O) (h : commonSecondBeta s C L I ≠ 0) :
    IsCoprime C I ∧ L ∣ I ∧ s.beta (C*I) ≠ 0 := by
  unfold commonSecondBeta at h
  split_ifs at h with hg
  · exact ⟨hg.1, hg.2, h⟩
  · exact (h rfl).elim

/-- Actual active second-common labels inherit both first-projector
divisibilities. This uses their genuine source witnesses, not a support
assumption imposed on arbitrary labels. -/
theorem actual_second_common_first_projector {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (p : ActiveLabel (commonSecondColumns s C₁ hC₁) (commonSecondBeta s C₁ L₁)) :
    L₁ ∣ p.val.1 ∧ L₁ ∣ p.val.2 ∧
      IsCoprime C₁ p.val.1 ∧ IsCoprime C₁ p.val.2 := by
  obtain ⟨I, hI, J, hJ, hIs, hJs, hβI, hβJ, heC, heD⟩ :=
    commonLabel_witnesses (commonSecondColumns s C₁ hC₁) (commonSecondBeta s C₁ L₁)
      p.val.1 p.val.2 p.property
  have hi := commonSecondBeta_nonzero s C₁ L₁ I hβI
  have hj := commonSecondBeta_nonzero s C₁ L₁ J hβJ
  have hh := divisor_dvd_common (commonPart I J) (commonPart J I)
    (residualPart I J) (residualPart J I) L₁
    (commonPart_ne_zero I J) (commonPart_ne_zero J I)
    (residualPart_ne_zero I J) (residualPart_ne_zero J I)
    (commonParts_equal_support I J) (commonPart_own_residual_coprime I J)
    (commonPart_residualPart_coprime I J) (residualParts_coprime I J)
    (by simpa only [← reconstruct I J hIs.1] using hi.2.1)
    (by simpa only [← reconstruct J I hJs.1] using hj.2.1)
  rw [← heC, ← heD]
  exact ⟨hh.1, hh.2,
    hi.1.of_isCoprime_of_dvd_right (commonPart_dvd I J hIs.1),
    hj.1.of_isCoprime_of_dvd_right (commonPart_dvd J I hJs.1)⟩

lemma residualPool_twice (C D : Ideal O) (hC : C ≠ 0) (hD : D ≠ 0)
    (S : Finset (Ideal O)) :
    residualPool D hD (residualPool C hC S) = residualPool (C*D) (mul_ne_zero hC hD) S := by
  ext I
  simp only [mem_residualPool, mul_assoc]

theorem commonSecondBeta_complete_mask {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C₁ C₂ L₁ I : Ideal O)
    (hCC : IsCoprime C₁ C₂) (hL : L₁ ∣ C₂) :
    (if IsCoprime C₂ I then commonSecondBeta s C₁ L₁ (C₂*I) else 0) =
      if IsCoprime (C₁*C₂) I then s.beta ((C₁*C₂)*I) else 0 := by
  have hd : L₁ ∣ C₂*I := hL.trans (dvd_mul_right _ _)
  simp only [commonSecondBeta, IsCoprime.mul_right_iff, IsCoprime.mul_left_iff,
    hCC, hd, true_and, and_true, mul_assoc]
  split_ifs <;> simp_all

lemma fixed_height_frequency_row (η : Character) (t : ℝ) (A z : O)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff η t I * idealRowHom (A*z) I = rowWeight η fixedBadMask A z t I := by
  rw [heightCoeff_eq_fixed_rowWeight η t I hI]
  simpa only [rowWeight, one_mul] using (rowWeight_split η fixedBadMask 1 (A*z) t I).symm

/-- The projected coefficient is the literal fixed-mask Hecke coefficient.
The second projector remains an external divisor condition. -/
theorem second_child_sum_eq_source (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O) :
    (∑ I : sectorPool C hC.1 S,
      secondBlockChildCoefficient η t S β C hC A L χ z I) =
    ∑ I ∈ supportedColumns (residualPool C hC.1 S),
      (if IsCoprime C I then β (C*I) else 0) *
        (if L ∣ I then 1 else 0) * rowWeight (childCharacter η χ) fixedBadMask A z t I := by
  simp_rw [secondBlockChildCoefficient_eq_ray_row, mul_assoc,
    fixed_height_frequency_row _ _ _ _ _ (sectorPool_supported C hC.1 S _)]
  rw [Finset.sum_coe_sort (sectorPool C hC.1 S)
    (fun I => (if L ∣ I then β (C*I) else 0) *
      rowWeight (childCharacter η χ) fixedBadMask A z t I)]
  rw [sectorPool, ← supported_residualPool C hC S, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

/-- Add the second projector after extracting the complete common ideal.
This is an identity of coefficients, before squaring or counting labels. -/
theorem original_projected_live_column {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (hS : ∀ i, ∀ I ∈ s.S i, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ s.S (Sum.inl i), Prime I)
    (C L I : Ideal O) (hC : C ≠ 0) (hI : I ≠ 0) (hsC : s.s ∣ C) :
    (if IsCoprime C I then s.beta (C*I) else 0) * (if L ∣ I then 1 else 0) =
      ∑ B : actualAllocations s.S C, frozenCoefficient B C s.R s.nu s.slot s.lengths *
        finiteColumnCoefficient
          (liveBox s.S B (allocation_data s.S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C s.R L s.nu s.slot s.lengths
            s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂) I := by
  have he := original_source_punctured_column s.S hS hp C s.R s.s I hC hI hsC
    s.nu s.slot s.lengths s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂
  change (if IsCoprime C I then s.beta (C*I) else 0) = _ at he
  rw [he, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro B hB
  rw [maskedLiveProfile, column_mask]
  simp only [liveProfile, mul_assoc]

/-- The comparison rectangle survives with the same extracted plain
ideals; both the source puncture and the common ideal enter its mask. -/
def commonAllocatedRectangle {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C : Ideal O) (B : actualAllocations s.S C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) : ℂ :=
  maskedRectangle η (fixedBadMask*idealGenerator (s.R*C)) A z t
    (fun i : CenteredMomentCommonProfile.liveIndices B.val =>
      residualPool (B.val (Sum.inl i.val))
        ((allocation_data s.S C B (Finset.mem_filter.mp B.property).1).1 _)
        (s.S (Sum.inl i.val)))
    (fun i I => s.nu i.val I*s.slot i.val ((I.absNorm : ℝ)/s.lengths i.val)) L
    s.W₁ s.W₂
    (s.X₁/(s.B₁*B.val (Sum.inr 0)).absNorm)
    (s.X₂/(s.B₂*B.val (Sum.inr 1)).absNorm)
    (s.Y₁/(s.B₁*B.val (Sum.inr 0)).absNorm)
    (s.Y₂/(s.B₂*B.val (Sum.inr 1)).absNorm)

theorem live_projected_polynomial_eq_rectangle {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C : Ideal O) (B : actualAllocations s.S C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O)
    (h₁ : PlainCoverage (s.S (Sum.inr 0)) s.W₁ s.B₁ s.X₁ s.Y₁)
    (h₂ : PlainCoverage (s.S (Sum.inr 1)) s.W₂ s.B₂ s.X₂ s.Y₂) :
    (∑ I ∈ finiteColumns
      (liveBox s.S B (allocation_data s.S C B (Finset.mem_filter.mp B.property).1).1),
      finiteColumnCoefficient
        (liveBox s.S B (allocation_data s.S C B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B C s.R L s.nu s.slot s.lengths
          s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂) I *
        rowWeight η fixedBadMask A z t I) = commonAllocatedRectangle s C B η A z t L := by
  rw [liveBox_eq_tuplePool]
  exact CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask A z t (dvd_mul_right _ _) (dvd_mul_left _ _) _ _ _ (s.R*C) L
    (fun i : CenteredMomentCommonProfile.liveIndices B.val => s.nu i.val)
    (fun i => s.slot i.val) (fun i => s.lengths i.val)
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ _ _
    (plainCoverage_residualPool _ _ _ _ _ _ _ h₁)
    (plainCoverage_residualPool _ _ _ _ _ _ _ h₂)

theorem live_projected_supported_sum {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (hS : ∀ i, ∀ I ∈ s.S i, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ s.S (Sum.inl i), Prime I)
    (C : Ideal O) (hC : Supported C) (B : actualAllocations s.S C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O)
    (h₁ : PlainCoverage (s.S (Sum.inr 0)) s.W₁ s.B₁ s.X₁ s.Y₁)
    (h₂ : PlainCoverage (s.S (Sum.inr 1)) s.W₂ s.B₂ s.X₂ s.Y₂) :
    (∑ I ∈ supportedColumns (residualPool C hC.1 s.columns),
      finiteColumnCoefficient
        (liveBox s.S B (allocation_data s.S C B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B C s.R L s.nu s.slot s.lengths
          s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂) I *
        rowWeight η fixedBadMask A z t I) = commonAllocatedRectangle s C B η A z t L := by
  let Q := liveBox s.S B (allocation_data s.S C B (Finset.mem_filter.mp B.property).1).1
  let γ := maskedLiveProfile B C s.R L s.nu s.slot s.lengths
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂
  change (∑ I ∈ supportedColumns (residualPool C hC.1 s.columns),
    finiteColumnCoefficient Q γ I*rowWeight η fixedBadMask A z t I) = _
  calc
    _ = ∑ I ∈ supportedColumns (finiteColumns Q),
        finiteColumnCoefficient Q γ I*rowWeight η fixedBadMask A z t I := by
      have he (I : Ideal O) : finiteColumnCoefficient Q γ I =
          finiteColumnCoefficient Q
            (liveProfile B C s.R s.nu s.slot s.lengths
              s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂) I *
              (if L ∣ I then 1 else 0) :=
        column_mask Q (s.R*C) (fun i => s.nu i.val) (fun i => s.slot i.val)
          (fun i => s.lengths i.val) s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂
          (s.B₁*B.val (Sum.inr 0)) (s.B₂*B.val (Sum.inr 1)) L I
      simp_rw [he, mul_assoc]
      exact live_column_sum s.S hS hp B _ C s.R hC
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        s.nu s.slot s.lengths s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂
        (fun I => (if L ∣ I then 1 else 0)*rowWeight η fixedBadMask A z t I)
    _ = ∑ I ∈ finiteColumns Q,
        finiteColumnCoefficient Q γ I*rowWeight η fixedBadMask A z t I := by
      apply Finset.sum_filter_of_ne
      intro I hI hn
      by_contra hs
      exact hn (by rw [rowWeight_zero_of_not_supported η fixedBadMask A z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs, mul_zero])
    _ = _ := live_projected_polynomial_eq_rectangle s C B η A z t L h₁ h₂

/-- The literal second child is the sum of all complete-common allocations.
This includes frozen coefficients, the comparison Y rectangle, the original
puncture, the extracted plain ideals, and the external second projector. -/
theorem original_second_child_eq_rectangles {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (hS : ∀ i, ∀ I ∈ s.S i, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ s.S (Sum.inl i), Prime I)
    (C : Ideal O) (hC : Supported C) (hsC : s.s ∣ C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) (χ : RayCharacter)
    (h₁ : PlainCoverage (s.S (Sum.inr 0)) s.W₁ s.B₁ s.X₁ s.Y₁)
    (h₂ : PlainCoverage (s.S (Sum.inr 1)) s.W₂ s.B₂ s.X₂ s.Y₂) :
    (∑ I : sectorPool C hC.1 s.columns,
      secondBlockChildCoefficient η t s.columns s.beta C hC A L χ z I) =
    ∑ B : actualAllocations s.S C, frozenCoefficient B C s.R s.nu s.slot s.lengths *
      commonAllocatedRectangle s C B (childCharacter η χ) A z t L := by
  rw [second_child_sum_eq_source]
  calc
    _ = ∑ I ∈ supportedColumns (residualPool C hC.1 s.columns),
        ∑ B : actualAllocations s.S C, frozenCoefficient B C s.R s.nu s.slot s.lengths *
          finiteColumnCoefficient
            (liveBox s.S B (allocation_data s.S C B (Finset.mem_filter.mp B.property).1).1)
            (maskedLiveProfile B C s.R L s.nu s.slot s.lengths
              s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂) I *
            rowWeight (childCharacter η χ) fixedBadMask A z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [original_projected_live_column s hS hp C L I hC.1
        (Finset.mem_filter.mp hI).2.1 hsC, Finset.sum_mul]
    _ = ∑ B : actualAllocations s.S C, frozenCoefficient B C s.R s.nu s.slot s.lengths *
        ∑ I ∈ supportedColumns (residualPool C hC.1 s.columns),
          finiteColumnCoefficient
            (liveBox s.S B (allocation_data s.S C B (Finset.mem_filter.mp B.property).1).1)
            (maskedLiveProfile B C s.R L s.nu s.slot s.lengths
              s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.B₁ s.B₂) I *
            rowWeight (childCharacter η χ) fixedBadMask A z t I := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum, mul_assoc]
    _ = _ := Finset.sum_congr rfl (fun B _ => congrArg
      (fun v => frozenCoefficient B C s.R s.nu s.slot s.lengths*v)
      (live_projected_supported_sum s hS hp C hC B (childCharacter η χ) A z t L h₁ h₂))

/-- The first and second common extractions combine exactly. The first
projector has already been extracted into the second common ideal. -/
theorem common_second_child_eq_complete_source {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C₁ C₂ L₁ : Ideal O)
    (hC₁ : Supported C₁) (hC₂ : Supported C₂)
    (hCC : IsCoprime C₁ C₂) (hL : L₁ ∣ C₂)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) (χ : RayCharacter) :
    (∑ I : sectorPool C₂ hC₂.1 (commonSecondColumns s C₁ hC₁),
      secondBlockChildCoefficient η t (commonSecondColumns s C₁ hC₁)
        (commonSecondBeta s C₁ L₁) C₂ hC₂ A L χ z I) =
    ∑ I : sectorPool (C₁*C₂) (mul_ne_zero hC₁.1 hC₂.1) s.columns,
      secondBlockChildCoefficient η t s.columns s.beta (C₁*C₂)
        ((supported_mul_iff _ _).mpr ⟨hC₁, hC₂⟩) A L χ z I := by
  rw [second_child_sum_eq_source, second_child_sum_eq_source]
  unfold commonSecondColumns
  rw [residualPool_twice]
  apply Finset.sum_congr rfl
  intro I hI
  rw [commonSecondBeta_complete_mask s C₁ C₂ L₁ I hCC hL]

/-- This is the literal bridge for the active second Poisson labels of
the first common source. First-projector divisibility and coprimality are
derived from the label, and all common allocation labels remain summed. -/
theorem actual_common_second_child_eq_rectangles {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (hS : ∀ i, ∀ I ∈ s.S i, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ s.S (Sum.inl i), Prime I)
    (C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hsC₁ : s.s ∣ C₁)
    (p : ActiveLabel (commonSecondColumns s C₁ hC₁) (commonSecondBeta s C₁ L₁))
    (hC₂ : Supported p.val.1)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) (χ : RayCharacter)
    (h₁ : PlainCoverage (s.S (Sum.inr 0)) s.W₁ s.B₁ s.X₁ s.Y₁)
    (h₂ : PlainCoverage (s.S (Sum.inr 1)) s.W₂ s.B₂ s.X₂ s.Y₂) :
    (∑ I : sectorPool p.val.1 hC₂.1 (commonSecondColumns s C₁ hC₁),
      secondBlockChildCoefficient η t (commonSecondColumns s C₁ hC₁)
        (commonSecondBeta s C₁ L₁) p.val.1 hC₂ A L χ z I) =
    ∑ B : actualAllocations s.S (C₁*p.val.1),
      frozenCoefficient B (C₁*p.val.1) s.R s.nu s.slot s.lengths *
        commonAllocatedRectangle s (C₁*p.val.1) B (childCharacter η χ) A z t L := by
  have hh := actual_second_common_first_projector s C₁ L₁ hC₁ p
  rw [common_second_child_eq_complete_source s C₁ p.val.1 L₁ hC₁ hC₂ hh.2.2.1 hh.1]
  exact original_second_child_eq_rectangles s hS hp _ ((supported_mul_iff _ _).mpr ⟨hC₁, hC₂⟩)
    (hsC₁.trans (dvd_mul_right _ _)) η A z t L χ h₁ h₂

theorem actual_common_second_right_child_eq_rectangles {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (hS : ∀ i, ∀ I ∈ s.S i, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ s.S (Sum.inl i), Prime I)
    (C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hsC₁ : s.s ∣ C₁)
    (p : ActiveLabel (commonSecondColumns s C₁ hC₁) (commonSecondBeta s C₁ L₁))
    (hD₂ : Supported p.val.2)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) (ξ : RayCharacter)
    (h₁ : PlainCoverage (s.S (Sum.inr 0)) s.W₁ s.B₁ s.X₁ s.Y₁)
    (h₂ : PlainCoverage (s.S (Sum.inr 1)) s.W₂ s.B₂ s.X₂ s.Y₂) :
    (∑ I : sectorPool p.val.2 hD₂.1 (commonSecondColumns s C₁ hC₁),
      secondBlockChildCoefficient η t (commonSecondColumns s C₁ hC₁)
        (commonSecondBeta s C₁ L₁) p.val.2 hD₂ A L (ξ⁻¹) (-z) I) =
    ∑ B : actualAllocations s.S (C₁*p.val.2),
      frozenCoefficient B (C₁*p.val.2) s.R s.nu s.slot s.lengths *
        commonAllocatedRectangle s (C₁*p.val.2) B (childCharacter η (ξ⁻¹)) A (-z) t L := by
  have hh := actual_second_common_first_projector s C₁ L₁ hC₁ p
  rw [common_second_child_eq_complete_source s C₁ p.val.2 L₁ hC₁ hD₂ hh.2.2.2 hh.2.1]
  exact original_second_child_eq_rectangles s hS hp _ ((supported_mul_iff _ _).mpr ⟨hC₁, hD₂⟩)
    (hsC₁.trans (dvd_mul_right _ _)) η A (-z) t L (ξ⁻¹) h₁ h₂

/-- The actual surviving source data after common extraction. Its prime
pools are inherited, not supplied by a coefficient equality premise. -/
def secondCommonData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (η : Character) (A : O) (t : ℝ) : Data (CenteredMomentCommonProfile.liveIndices B.val) :=
  { commonData s C R B with η := η, A := A, t := t }

def secondCommonVolume {ι : Type*} [Fintype ι]
    (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) : ℝ :=
  (s.X₁/(B.val (Sum.inr 0)).absNorm)*(s.X₂/(B.val (Sum.inr 1)).absNorm)*
    ∏ i : CenteredMomentCommonProfile.liveIndices B.val, s.P i.val

theorem secondCommonVolume_pos {ι : Type*} [Fintype ι]
    (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    0 < secondCommonVolume s C B :=
  mul_pos (mul_pos (div_pos s.X₁_pos (alloc_norm_pos s C B _))
    (div_pos s.X₂_pos (alloc_norm_pos s C B _)))
      (Finset.prod_pos (fun i _ => s.P_pos i.val))

theorem common_rectangle_eq_source {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) :
    commonAllocatedRectangle (original s R seed) C B η A z t L =
      let c := secondCommonData s C R B η A t
      maskedRectangle c.η c.m c.A z c.t c.slots c.coefficient L
        c.W₁ c.W₂ c.X₁ c.X₂ c.Y₁ c.Y₂ := by
  simp only [commonAllocatedRectangle, original, secondCommonData, commonData,
    one_mul, live_slot_one, residual_one, Input.pools, Sum.elim_inl]
  simp only [maskedRectangle, CenteredMomentEligibleEnergy.Data.coefficient]
  congr 1
  ext v
  simp

theorem common_rectangle_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) :
    (Real.sqrt (secondCommonVolume s C B) : ℂ)⁻¹ *
      commonAllocatedRectangle (original s R seed) C B η A z t L =
      secondMaskedValue (secondCommonData s C R B η A t).toSource L z := by
  rw [common_rectangle_eq_source]
  rfl

theorem common_rectangle_unnormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) :
    commonAllocatedRectangle (original s R seed) C B η A z t L =
      (Real.sqrt (secondCommonVolume s C B) : ℂ) *
        secondMaskedValue (secondCommonData s C R B η A t).toSource L z := by
  rw [← common_rectangle_normalized s C R seed B η A z t L]
  have hn : (Real.sqrt (secondCommonVolume s C B) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (secondCommonVolume_pos s C B)).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

def secondCommonWeight {ι : Type*} [Fintype ι]
    (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C) : ℂ :=
  frozenCoefficient B C R s.ν s.W s.P *
    ((Real.sqrt (secondCommonVolume s C B)/Real.sqrt (volume s) : ℝ) : ℂ)

/-- The denominator can be the actual physical column normalization.
It is not replaced by a fresh source-volume upper bound. -/
def secondCommonWeightAt {ι : Type*} [Fintype ι]
    (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C) (V : ℝ) : ℂ :=
  frozenCoefficient B C R s.ν s.W s.P *
    ((Real.sqrt (secondCommonVolume s C B)/Real.sqrt V : ℝ) : ℂ)

theorem original_second_child_normalized_at {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R seed : Ideal O) (hC : Supported C) (hsC : seed ∣ C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) (χ : RayCharacter) (V : ℝ) :
    (Real.sqrt V : ℂ)⁻¹ *
      (∑ I : sectorPool C hC.1 (original s R seed).columns,
        secondBlockChildCoefficient η t (original s R seed).columns
          (original s R seed).beta C hC A L χ z I) =
      ∑ B : actualAllocations s.pools C, secondCommonWeightAt s C R B V *
        secondMaskedValue (secondCommonData s C R B (childCharacter η χ) A t).toSource L z := by
  rw [original_second_child_eq_rectangles (original s R seed) s.pools_ne s.prime
    C hC hsC η A z t L χ s.coverage₁ s.coverage₂, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  change ↥(actualAllocations s.pools C) at B
  rw [common_rectangle_unnormalized s C R seed B (childCharacter η χ) A z t L]
  simp only [secondCommonWeightAt, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  change _ * (frozenCoefficient B C R s.ν s.W s.P * (_ * _)) = _
  ring

/-- Direct normalized bridge from the actual first common source and its
active second label to the literal surviving source Data. -/
theorem actual_common_second_child_normalized_at {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hsC₁ : seed ∣ C₁)
    (p : ActiveLabel (commonSecondColumns (original s R seed) C₁ hC₁)
      (commonSecondBeta (original s R seed) C₁ L₁)) (hC₂ : Supported p.val.1)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) (χ : RayCharacter) (V : ℝ) :
    (Real.sqrt V : ℂ)⁻¹ *
      (∑ I : sectorPool p.val.1 hC₂.1 (commonSecondColumns (original s R seed) C₁ hC₁),
        secondBlockChildCoefficient η t (commonSecondColumns (original s R seed) C₁ hC₁)
          (commonSecondBeta (original s R seed) C₁ L₁) p.val.1 hC₂ A L χ z I) =
      ∑ B : actualAllocations s.pools (C₁*p.val.1),
        secondCommonWeightAt s (C₁*p.val.1) R B V *
          secondMaskedValue (secondCommonData s (C₁*p.val.1) R B
            (childCharacter η χ) A t).toSource L z := by
  have hh := actual_second_common_first_projector (original s R seed) C₁ L₁ hC₁ p
  rw [common_second_child_eq_complete_source (original s R seed) C₁ p.val.1 L₁
    hC₁ hC₂ hh.2.2.1 hh.1]
  exact original_second_child_normalized_at s _ R seed ((supported_mul_iff _ _).mpr ⟨hC₁, hC₂⟩)
    (hsC₁.trans (dvd_mul_right _ _)) η A z t L χ V

/-- Exact parent-volume normalization. Common allocations are retained
with their individual square-root volume ratios. -/
theorem original_second_child_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R seed : Ideal O) (hC : Supported C) (hsC : seed ∣ C)
    (η : Character) (A z : O) (t : ℝ) (L : Ideal O) (χ : RayCharacter) :
    (Real.sqrt (volume s) : ℂ)⁻¹ *
      (∑ I : sectorPool C hC.1 (original s R seed).columns,
        secondBlockChildCoefficient η t (original s R seed).columns
          (original s R seed).beta C hC A L χ z I) =
      ∑ B : actualAllocations s.pools C, secondCommonWeight s C R B *
        secondMaskedValue (secondCommonData s C R B (childCharacter η χ) A t).toSource L z := by
  rw [original_second_child_eq_rectangles (original s R seed) s.pools_ne s.prime
    C hC hsC η A z t L χ s.coverage₁ s.coverage₂, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  change ↥(actualAllocations s.pools C) at B
  rw [common_rectangle_unnormalized s C R seed B (childCharacter η χ) A z t L]
  simp only [secondCommonWeight, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  change _ * (frozenCoefficient B C R s.ν s.W s.P * (_ * _)) = _
  ring

/-- The paired retained expression with the exact allocation reductions
and the two actual positive rows (X and Y) on each side. -/
def secondRetainedPairBound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : Data ι) (v : Data κ)
    (L : Ideal O) (z w : O) : ℝ :=
  ∑ a ∈ s.toSource.active L, ∑ b ∈ v.toSource.active L,
    (1 / Real.sqrt (formalReductionFactor L a s.P * formalReductionFactor L b v.P)) *
      (Real.sqrt (secondExtractionNumerator s.M s.b₁ s.b₂ L a *
        secondRetainedEnergy s.toSource L a z) *
       Real.sqrt (secondExtractionNumerator v.M v.b₁ v.b₂ L b *
        secondRetainedEnergy v.toSource L b w))

theorem second_source_masked_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : Data ι) (v : Data κ)
    (L : Ideal O) (hL : Squarefree L) (z w : O) :
    ‖secondMaskedValue s.toSource L z‖ * ‖secondMaskedValue v.toSource L w‖ ≤
      secondRetainedPairBound s v L z w :=
  actual_second_masked_pair s.toSource v.toSource s.M v.M
    (fun i => zero_le_one.trans (s.M_ge_one i)) (fun i => zero_le_one.trans (v.M_ge_one i))
    s.coefficient_bound v.coefficient_bound s.b₁ s.b₂ v.b₁ v.b₂
    s.support₁ s.support₂ v.support₁ v.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos v.X₁_pos v.X₂_pos v.Y₁_pos v.Y₂_pos
    s.same_product v.same_product L hL z w

/-- The actual retained Fourier phase is a contraction on a pair of
normalized source rectangles. The right source is evaluated at -z. -/
theorem actual_second_phase_source_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : Data ι) (v : Data κ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)) (R : ℝ)
    (L : Ideal O) (hL : Squarefree L) (z : O) :
    ‖secondBlockRowPhase C D hC hD U R z * secondMaskedValue s.toSource L z *
        star (secondMaskedValue v.toSource L (-z))‖ ≤
      secondRetainedPairBound s v L z (-z) := by
  calc
    _ = ‖secondBlockRowPhase C D hC hD U R z‖ *
        (‖secondMaskedValue s.toSource L z‖ * ‖secondMaskedValue v.toSource L (-z)‖) := by
      rw [norm_mul, norm_mul, norm_star, mul_assoc]
    _ ≤ ‖secondMaskedValue s.toSource L z‖ * ‖secondMaskedValue v.toSource L (-z)‖ := by
      exact mul_le_of_le_one_left (by positivity) (secondBlockRowPhase_norm C D hC hD hCD U R z)
    _ ≤ _ := second_source_masked_pair s v L hL z (-z)

theorem actual_second_height_phase_source_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : Data ι) (v : Data κ)
    (η : Character) (t : ℝ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)) (R : ℝ)
    (L : Ideal O) (hL : Squarefree L) (z : O) :
    ‖(heightCoeff η t C*star (heightCoeff η t D))*
        (secondBlockRowPhase C D hC hD U R z * secondMaskedValue s.toSource L z *
          star (secondMaskedValue v.toSource L (-z)))‖ ≤
      secondRetainedPairBound s v L z (-z) := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t C D hC.1 hD.1)).trans
      (actual_second_phase_source_pair s v C D hC hD hCD U R L hL z)

/-- Whole first-label sums can be retained through the phase contraction;
the right hand side still contains every active second allocation. -/
theorem joint_second_phase_source_pair {α : Type*} (ι κ : α → Type*)
    [∀ ℓ, Fintype (ι ℓ)] [∀ ℓ, Fintype (κ ℓ)]
    [∀ ℓ, DecidableEq (ι ℓ)] [∀ ℓ, DecidableEq (κ ℓ)]
    (Λ : Finset α) (weight : α → ℝ) (hweight : ∀ ℓ ∈ Λ, 0 ≤ weight ℓ)
    (s : ∀ ℓ, Data (ι ℓ)) (v : ∀ ℓ, Data (κ ℓ)) (C D : α → Ideal O)
    (hC : ∀ ℓ, Supported (C ℓ)) (hD : ∀ ℓ, Supported (D ℓ))
    (hCD : ∀ ℓ, CompletedGauss.primeSupport (C ℓ) = CompletedGauss.primeSupport (D ℓ))
    (U : ∀ ℓ, Finset (CenteredMomentCanonicalFirst.CommonIndex (C ℓ) (D ℓ)))
    (R : α → ℝ) (L : α → Ideal O) (hL : ∀ ℓ, Squarefree (L ℓ)) (z : α → O) :
    (∑ ℓ ∈ Λ, weight ℓ *
      ‖secondBlockRowPhase (C ℓ) (D ℓ) (hC ℓ) (hD ℓ) (U ℓ) (R ℓ) (z ℓ) *
        secondMaskedValue (s ℓ).toSource (L ℓ) (z ℓ) *
        star (secondMaskedValue (v ℓ).toSource (L ℓ) (-(z ℓ)))‖) ≤
    ∑ ℓ ∈ Λ, weight ℓ * secondRetainedPairBound (s ℓ) (v ℓ) (L ℓ) (z ℓ) (-(z ℓ)) := by
  exact Finset.sum_le_sum (fun ℓ hℓ => mul_le_mul_of_nonneg_left
    (actual_second_phase_source_pair (s ℓ) (v ℓ) (C ℓ) (D ℓ) (hC ℓ) (hD ℓ)
      (hCD ℓ) (U ℓ) (R ℓ) (L ℓ) (hL ℓ) (z ℓ)) (hweight ℓ hℓ))

#print axioms second_child_sum_eq_source
#print axioms live_projected_polynomial_eq_rectangle
#print axioms original_second_child_eq_rectangles
#print axioms original_second_child_normalized
#print axioms second_source_masked_pair
#print axioms actual_second_common_first_projector
#print axioms actual_common_second_child_eq_rectangles
#print axioms actual_second_phase_source_pair
#print axioms actual_common_second_child_normalized_at
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondAllocated -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.NaturalLowStage ; sha256 651f1349c8d709e97b4410c15583cedadc3b8cefbe75e5ccd7e438a78133f316 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/NaturalLowStage.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/










namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyNaturalLowStage
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open Cycle25CenteredMomentEnergyPositiveHighParameters Cycle25CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins Cycle25CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open Cycle25CenteredMomentEnergyNaturalLowPhysical CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyBandMonotonicity

theorem actual_low_from_bands
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)(hΦ:2≤ bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(7/10:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uout:Finset (ℕ×ℕ),∃Jout:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi Mparent
        (physicalLoss Mglobal B ε k) κ Z η₀ Q Jout Uout (C*(C₀+C₁+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (physicalLoss Mglobal B ε k) Z Jout Uout (C*(C₀+C₁+1)) :=by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hr:0< r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hmarg:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hbΦ:0< bΦ:=by linarith
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hentry⟩:=
    CenteredMomentEnergyPositiveLowSourceControlled.actual_low_stages_from_physical (α:=α)
      M H hH W hW.continuous aslot bslot lo hi a b bΦ Mparent (r/4) (r/4)
      (2*amplification ε+1) haslot hWs hbslot ha hb hbΦ hMp (by positivity) (by positivity)
  obtain ⟨U,J,hphysical⟩:=actual_natural_low_physical (α:=α) M H hH W hW aslot bslot lo hi a b bΦ
    haslot hWs hbslot ha hb Mglobal A B Bmask Mparent Mchild Lgoal Lslot Mchild κ ε k
    hMg hA hB hBm hMp hMc hL hLs hMA hready hκ hbeta hκbeta hε hslot hdrop Ψ degree S
  let Umerge:=S∪U
  let Jmerge:=degree+J
  have hS:S⊆Umerge:=Finset.subset_union_left
  have hU:U⊆Umerge:=Finset.subset_union_right
  have hdeg:degree≤ Jmerge:=Nat.le_add_right _ _
  have hJ:J≤ Jmerge:=Nat.le_add_left _ _
  have halower:a/max 1 b≤ a:=by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
    nlinarith [le_max_left (1:ℝ) b]
  have hlen:Lgoal≤2*max Lgoal Mparent+r/4:=by
    have hh:=le_max_left Lgoal Mparent
    linarith
  refine ⟨insert (0,0) Umerge,Jmerge,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphys⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let Cout:=Cfixed*(Cp+1)+1
  have hCout:0< Cout:=by dsimp [Cout];positivity
  refine ⟨Cout,hCout,?_⟩
  filter_upwards [hentry,hphys] with Z he hp
  refine ⟨hp.1,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
  have hzsmall:=zeroAt_transport (internalQ Q η₀)
    (a/max 1 b) b bΦ Bmask _ Mchild εchild Z
    (a/max 1 b) b 2 0 _ Mchild εchild degree degree S S C₀ C₀ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₀ le_rfl hzero
  have hpsmall:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    (a/max 1 b) b 2 0 _ Mchild εchild η₀ Q degree degree S S C₁ C₁ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hpos
  have hold:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    a b bΦ Bmask Lgoal Mchild (physicalLoss Mglobal B ε k) η₀ Q
    degree Jmerge S Umerge C₁ C₁ hp.1.le halower le_rfl le_rfl le_rfl hlen le_rfl
    (hell.trans hmarg.2.1) hdeg hS hC₁ le_rfl hpos
  have hm:=hp.2 εchild C₀ C₁ hell hC₀ hC₁ hzsmall hpsmall
  have hm':PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
      a b bΦ Bmask Lgoal Lslot Mchild Mparent κ (r/4) (physicalLoss Mglobal B ε k)
      Z ha Ψ η₀ Q Umerge Jmerge (Cp*(C₀+C₁+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hm T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤ Z:=zero_le_one.trans hp.1.le
    have hcontrol:=profile_control_mono p hU
    have hc0:=p.control_nonneg U
    have hheight1:1≤1+|t|+height:=by linarith [abs_nonneg t]
    apply hh.trans
    gcongr
  have hsave:-(2*amplification ε+1)≤ physicalLoss Mglobal B ε k:=by
    have hs:0< amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
    linarith [hmarg.1]
  have hout:=he.2 Bmask Lgoal Lslot Mchild κ (physicalLoss Mglobal B ε k) η₀ Q Umerge Jmerge
    (Cp*(C₀+C₁+1)) C₁ hκsmall (by positivity) hC₁ hmarg.2.2.1 hsave hold hm'
  have hC:Cfixed*(Cp*(C₀+C₁+1)+1)+C₁≤ Cout*(C₀+C₁+1):=by
    dsimp [Cout]
    nlinarith [mul_nonneg hCfixed.le hC₀,mul_nonneg hCfixed.le hC₁]
  constructor
  · exact CenteredMomentEnergyStageMonotonicity.positiveLowAt_transport (α:=α) M H hH W bslot
      a b bΦ Bmask Lgoal Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) η₀ Q Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.1
  · exact CenteredMomentEnergyStageMonotonicity.zeroLowAt_transport (internalQ Q η₀)
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.2

end SevenEighths.Cycle25CenteredMomentEnergyNaturalLowStage

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.NaturalLowStage -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveHighSourceBound ; sha256 c08b37e87e3b3bd1096ab57aa6bd96fbd40dba67dd052970faf4f51be5573ae7 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveHighSourceBound.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/








namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveHighSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open Cycle25CenteredMomentEnergyPositiveHighSource (balancedInput)
open Cycle25CenteredMomentEnergyPositiveHighBound CenteredMomentEnergyBandMonotonicity
open Cycle25CenteredMomentEnergyPositiveHighAssembly (low_restrict)
def PhysicalHighAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0< a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤ w i)→(∀i,w i≤ Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤ hi,
    0≤ height→(∀i,|freq i|≤ height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤ state.width→state.width≤ Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,
    X₁≤ Z^L→X₂≤ Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ state.width→
    5*state.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
    let inp:=balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂;
    (Z^(state.width/4)≤ inp.X₁ ∧ Z^(state.width/4)≤ inp.X₂ ∧
      Z^(state.width/4)≤ inp.Y₁ ∧ Z^(state.width/4)≤ inp.Y₂)→
    physicalMass inp state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ/volume inp≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

def PositiveHighAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤ w i)→(∀i,w i≤ Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤ hi)→
    0≤ height→(∀i,|v i|≤ height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→ rho≤ s.width→s.width≤ Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0< X₁→0< X₂→X₁≤ Z^L→X₂≤ Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=> primePool M H bslot (Z^(w i)))
      (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

theorem actual_high_stage_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (hrho:0< rho)(hε:0<ε)(hMcap:0≤ Mcap)(hBmask:0≤ Bmask)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0< Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀(L Lslot κ e emass efinal:ℝ)(η₀:Character)(Q:Ideal O)(K Cphysical:ℝ),
      7/10≤κ→0≤ e→0≤ K→0≤ Cphysical→e+ε≤ efinal→emass≤ efinal→εdiag≤ efinal→-saving≤ efinal→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
        Lslot lo hi Mcap e κ Z η₀ Q degree S K→
      PhysicalHighAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ emass Z ha Ψ η₀ Q Smass Jmass Cphysical→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap efinal κ Z η₀ Q
        Jout U (Cfixed*(K+Cphysical+1)):=by
  have hfixed (T:Finset α):=actual_high_from_physical (α:=T) M H hH W aslot bslot lo hi
    haslot hWs hW a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε
    hMcap hBmask hbslot hεdiag hξ
  choose Lj hLj hLjcap Ψ hΨs hΨn hj using hfixed
  refine ⟨Ψ,hΨs,hΨn,?_⟩
  intro degree S Jmass Smass
  have hall (T:Finset α):=hj T degree S Jmass Smass
  choose Jj Uj Cj hCj hbound using hall
  let Jout:ℕ:=∑T:Finset α,Jj T
  let U:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0< Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤ Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  have hJJ (T:Finset α):Jj T≤ Jout:=Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ T)
  have hUU (T:Finset α):Uj T⊆U:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ T,hx⟩
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  have hevent:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hevent,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro L Lslot κ e emass efinal η₀ Q K Cphysical hκ he hK hCphysical hefinal hmassFinal
    hdiagFinal htailFinal hlow hmass
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hlowT:=CenteredMomentEnergyLowBandSubtype.positiveLowAt_subtype (α:=α) M H hH T
    W bslot a b bΦ Bmask (Mcap+Bmask+rho/100) Lslot lo hi Mcap e κ Z η₀ Q degree S K hlow
  have hlowLj:=low_restrict (α:=T) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
    (Lj T) Lslot lo hi Mcap e e κ Z η₀ Q degree S K hZ1.le (hLjcap T) le_rfl hK hlowT
  have hphys:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo
    hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hh:=(hZ T).2 e emass efinal Lslot κ η₀ Q K Cphysical he hK hCphysical
    hefinal hmassFinal hdiagFinal htailFinal hlowLj θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ state hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcapacity hphys
  have hc:=hCC T
  have hp:=profile_control_mono p (hUU T)
  have hp0:=p.control_nonneg (Uj T)
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  have hpow:=pow_le_pow_right₀ hbase (hJJ T)
  have hd:=diagonalControl_nonneg state.radial.profile
  have hz:0≤ Z:=zero_le_one.trans hZ1.le
  apply hh.trans
  gcongr

omit [Fintype α] [DecidableEq α] in
theorem positive_from_stages
    (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap e κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(J:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hold:PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q J S C)
    (hlow:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J S C)
    (hhigh:PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap e κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J S C:=by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity
  by_cases hsmall:s.width≤ rho
  · exact hold T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hsmall p X₁ X₂
      hX₁ hX₂ hcap₁ hcap₂ hcapacity
  by_cases hl:length Z X₁+length Z X₂+(∑i,w i)≤5*s.width/6
  · exact hlow T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
      hX₁ hX₂ hcap₁ hcap₂ hcapacity hl
  exact hhigh T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ (le_of_not_ge hsmall) hs
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity (le_of_not_ge hl)

end SevenEighths.Cycle25CenteredMomentEnergyPositiveHighSourceBound

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveHighSourceBound -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.FiniteBins ; sha256 888c1a8e4741dd1d32befd9fa707e93b4e6e627c68729f498f885015c497d054 -/
section


/-! Finite dilation boxes summed after the weighted fourth-moment estimate.
The coefficient mass stays a single linear factor. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

theorem finite_weighted_dilation_bins {ι : Type*} (s : Finset ι) (n : ℕ)
    (S Q : ℕ → ι → ℂ) (P f : ι → ℂ)
    (kap U R q L z xi delta loss epsilon Ccount Cmoment M : ℝ)
    (hkap : 7/10 ≤ kap)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hxi : 0 ≤ xi)
    (hcard : (s.card : ℝ) ≤ Ccount*U^R)
    (hsplit : ∀ i ∈ s, f i = ∑ j ∈ Finset.range (n+1),
      ((M * U^(-delta*((j : ℝ)*xi)/4) : ℝ) : ℂ) * S j i)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i ∈ s,
      U^(q*selectedCapacity kap z ((j : ℝ)*xi+xi)-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : ∀ j ∈ Finset.range (n+1),
      (∑ i ∈ s, ‖S j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i ∈ s, ‖f i * P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hdelta : 0 ≤ delta := by linarith
  let E : ℝ := q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4
  have hj (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i ∈ s, ‖(((M * U^(-delta*((j : ℝ)*xi)/4) : ℝ) : ℂ) * S j i) * P i‖) ≤
      M*Ccount*Cmoment*U^E := by
    have hd := weighted_dilation_bin s (S j) (Q j) P kap U R q L z ((j : ℝ)*xi) xi delta
      loss epsilon Ccount Cmoment hkap hU hc hm hq hqdelta (mul_nonneg (Nat.cast_nonneg _) hxi)
      hxi hcard (hselected j hj) hfull (henergy j hj)
    have hpow : U^(E-11*delta*((j : ℝ)*xi+xi)/84) ≤ U^E :=
      Real.rpow_le_rpow_of_exponent_le hU (by
        have hv : 0 ≤ (j : ℝ)*xi+xi := by positivity
        have := mul_nonneg hdelta hv
        dsimp only [E]
        nlinarith)
    calc
      _ = M * (U^(-delta*((j : ℝ)*xi)/4) * (∑ i ∈ s, ‖S j i * P i‖)) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_assoc,norm_mul,Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg hM (Real.rpow_nonneg hU0.le _))]
        ring
      _ ≤ M * (Ccount*Cmoment*U^(E-11*delta*((j : ℝ)*xi+xi)/84)) :=
        mul_le_mul_of_nonneg_left hd hM
      _ ≤ M * (Ccount*Cmoment*U^E) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (by have hc0 := zero_le_one.trans hc; have hm0 := zero_le_one.trans hm; positivity)) hM
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ Finset.range (n+1),
        ‖(((M * U^(-delta*((j : ℝ)*xi)/4) : ℝ) : ℂ) * S j i) * P i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hsplit i hi,Finset.sum_mul]
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n+1), ∑ i ∈ s,
        ‖(((M * U^(-delta*((j : ℝ)*xi)/4) : ℝ) : ℂ) * S j i) * P i‖ := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (n+1), M*Ccount*Cmoment*U^E := Finset.sum_le_sum hj
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; dsimp only [E]; ring

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.FiniteBins -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorLabelReconstruction ; sha256 2ff4d0865f5264bf0f516667cb4967c41034e435a8474f874cdbf62ce852d0aa -/
section



/-! The literal error-label numerator has precisely the global coefficient packet
whose damped mass is used in the weighted fourth moment. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem label_packet_central_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (weight : ∀i,T i→ℂ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2) :
    Summable (fun e : LabelPacketIndex S u T=>‖labelPacketCoefficient S hS η u T hT weight x z e‖*
      (labelPacketScale S u T e:ℝ)^(-(1/2:ℝ))) := by
  apply (summable_sigma_of_nonneg (fun e=> mul_nonneg (norm_nonneg _) (by positivity))).mpr
  refine ⟨?_,(hasSum_fintype _).summable⟩
  intro P
  have hs := (error_packet_central_summable S hS firsteps hfirst η u (labelPrimes T P)
    (labelSupported S hS T hT P) x z hx hz hmargin).mul_left ‖∏i,weight i (P i)‖
  simpa only [labelPacketCoefficient,labelPacketScale,norm_mul,mul_assoc] using hs

theorem partialErrorTuple_label_series {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤ P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2) (t : ℝ) :
    (∑P:(∀i:J,T i.val),partialErrorTuple S hS η u J T hT P W Yp x ((1/2:ℂ)+t*I) z)=
    ∑'e : LabelPacketIndex S u (fun i:J=> T i.val),
      labelPacketCoefficient S hS η u (fun i:J=> T i.val) (fun i=> hT i.val)
        (fun i P=> physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z e*
      (labelPacketScale S u (fun i:J=> T i.val) e:ℂ)^(-((1/2:ℂ)+t*I)) := by
  have hs := label_packet_central_summable S hS firsteps hfirst η u
    (fun i:J=> T i.val) (fun i=> hT i.val)
    (fun i P=> physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z hx hz hmargin
  have hc : Summable (fun e : LabelPacketIndex S u (fun i:J=> T i.val)=>
      labelPacketCoefficient S hS η u (fun i:J=> T i.val) (fun i=> hT i.val)
        (fun i P=> physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z e*
      (labelPacketScale S u (fun i:J=> T i.val) e:ℂ)^(-((1/2:ℂ)+t*I))) := by
    apply Summable.of_norm
    convert hs using 1
    funext e
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u (fun i:J=> T i.val) e))]
    norm_num
  unfold LabelPacketIndex at hc ⊢
  rw [hc.tsum_sigma,tsum_fintype]
  apply Finset.sum_congr rfl
  intro P hP
  rw [partialErrorTuple_packet S hS η u J T hT P (hdis P) (partial_image_supported S hS J T hT P)]
  have hηP : ∀Q∈labelPrimes (fun i:J=> T i.val) P,IsCoprime Q.val η.modulus := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hη i.val _ (P i).property
  have hQP : ∀Q∈labelPrimes (fun i:J=> T i.val) P,(4:ℝ)≤ Q.val.absNorm := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hQ i.val _ (P i).property
  have he := error_packet_expansion S hS firsteps hfirst η u (labelPrimes (fun i:J=> T i.val) P)
    (labelSupported S hS (fun i:J=> T i.val) (fun i:J=> hT i.val) P) hηP x ((1/2:ℂ)+t*I) z hQP hx hz
    (by simp;norm_num) (by simpa using hmargin)
  simp only [labelPrimes] at he
  apply Eq.trans (congrArg (fun v : ℂ=>(∏i:J,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*v) he)
  simp only [labelPacketCoefficient,labelPacketScale,labelPrimes]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro e
  ring

theorem errorLabelNumerator_reconstruction {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤ P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0< Y) :
    errorLabelNumerator S hS η u J T hT W Yp x z W1 Y=
      (Y:ℂ)^(-(1/2:ℂ))*∑'e : LabelPacketIndex S u (fun i:J=> T i.val),
        labelPacketCoefficient S hS η u (fun i:J=> T i.val) (fun i=> hT i.val)
          (fun i P=> physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z e*
        (labelPacketScale S u (fun i:J=> T i.val) e:ℂ)^(-(1/2:ℂ))*
        HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W1
          (Y/(labelPacketScale S u (fun i:J=> T i.val) e:ℝ)) 0 0 := by
  let f (P : ∀i:J,T i.val) (t : ℝ) :=
    (Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W1 ((1/2:ℂ)+t*I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*I)*
      partialErrorTuple S hS η u J T hT P W Yp x ((1/2:ℂ)+t*I) z
  have hfi (P : ∀i:J,T i.val) : Integrable (f P) := by
    apply partialErrorTuple_kernel_integrable S hS firsteps hfirst η u hrow J T hT P (hdis P)
      (partial_image_supported S hS J T hT P) _ _ W Yp x z hx hz hmargin W1 a b ha hsupp hW Y hY
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hη i.val _ (P i).property
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hQ i.val _ (P i).property
  have he : errorLabelNumerator S hS η u J T hT W Yp x z W1 Y=
      (1/(2*Real.pi):ℂ)*(∫t : ℝ,∑P:(∀i:J,T i.val),f P t) := by
    rw [integral_finsetSum Finset.univ (fun P _=> hfi P),Finset.mul_sum]
    unfold errorLabelNumerator
    apply Finset.sum_congr rfl
    intro P hP
    exact (partialErrorTuple_mellin S hS η u J T hT P (hdis P)
      (partial_image_supported S hS J T hT P) W Yp x z W1 Y).symm
  rw [he]
  simp only [f,←Finset.mul_sum]
  simp_rw [partialErrorTuple_label_series S hS firsteps hfirst η u J T hT hdis hη hQ W Yp x z hx hz hmargin]
  exact MellinReconstruction.weighted_numerator_mellin (rowCharacter S hS.prime u) hrow
    W1 a b ha hsupp hW Y hY _ _
    (fun e=> lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u (fun i:J=> T i.val) e))
    (label_packet_central_summable S hS firsteps hfirst η u (fun i:J=> T i.val) (fun i=> hT i.val)
      (fun i P=> physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z hx hz hmargin)

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorLabelReconstruction -/
