/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.local44_20261013.Bundles.B010
import Submissions.local44_20261013.Bundles.B013
import Submissions.local44_20261013.Bundles.B031
import Submissions.local44_20261013.Bundles.B036
import Submissions.local44_20261013.Bundles.B047
import Submissions.local44_20261013.Bundles.B064
import Submissions.local44_20261013.Bundles.B065
import Submissions.local44_20261013.Bundles.B068
import Submissions.local44_20261013.Bundles.B076
import Submissions.local44_20261013.Bundles.B077
import Submissions.local44_20261013.Bundles.B078
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass

/- BEGIN ORIGINAL MODULE Global.Numerator.SourceParameters ; sha256 126fe11ff6a5ded93872319517ed7890799a7dc55022d3a2247b195935818385 -/
section




/-! Eligibility of the actual physical source for the coefficient packet bound. -/
noncomputable section
open scoped BigOperators Classical
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator
open Cycle25.Weighted OAI.SevenEighths.Cycle25DetectorRowCount
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification

theorem source_packet_lines {Δ : ℝ} (D : HighParameters.HighData Δ) (a : ℝ)
    (ha : (51/100:ℝ) ≤ a) (hatop : a ≤ 7/8) :
    0 ≤ (2*a-1)/4 ∧ (2*a-1)/4 ≤ 1 ∧
    1-a-6*D.e ≤ 1/2-(2*a-1)/4 ∧
    -(1/100:ℝ) ≤ 1/2-(2*a-1)/4 ∧
    1+4*D.e ≤ (a+16*D.e)+(1/2-(2*a-1)/4) := by
  have he := D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem source_complex_profile_norm {D : MomentData} (F : WeightedSourceData D) (y : ℝ) :
    ‖F.W y‖ ≤ 1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded y).1]
  exact (F.bounded y).2

theorem source_main_normalized_upper {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z d delta : ℝ) (hZ : 1 < Z) (hd : 0 < d)
    (main : Finset (Fin D.N)) (g : Fin D.N→ℝ) (u : FreeRow) (z : ℂ)
    (hupper : ∀j∈main,‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z‖ ≤
      (Z^(D.ell j))^(g j+D.t)) :
    let q := HeckeDetectorPhysicalSelection.weightedMean Finset.univ (fun j=> D.ell j/d) (maskedGain main g)
    ‖(∏j∈main,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z) /
      (((Z^d)^(D.t*(ell/d)):ℝ):ℂ)‖ ≤ (Z^d)^(q*(ell/d)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hd
  have hw (j : Fin D.N) : 0 ≤ D.ell j/d := (div_pos (D.slots_bounds j).1 hd).le
  have hL : (∑j,D.ell j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
  have hscale (j : Fin D.N) : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd.ne']
  have hb := masked_main_product_upper main (fun j=> D.ell j/d) g (Z^d) D.t
    (fun j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)
    hU.le D.t_pos.le hw (by rw [hL];exact div_pos ell_pos hd) (by
      intro j hj
      calc
        _ ≤ (Z^(D.ell j))^(g j+D.t) := hupper j hj
        _ = _ := by rw [←hscale j,←Real.rpow_mul (zero_lt_one.trans hU).le])
  rw [hL] at hb
  exact upper_bin_normalized _ (Z^d) _ _ (zero_lt_one.trans hU) hb

end Submission20261012.Global.Numerator

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

-- New geometry wrapper, 13 October 2026; inherited analytic core unchanged.
end
/- END ORIGINAL MODULE Global.Numerator.SourceParameters -/

/- BEGIN ORIGINAL MODULE Analytic.JointExtractedErrorBudget ; sha256 84ee1dfbca26a12e771a04836418182fc363f85664690dd0643edb706b3ef014 -/
section



/-! The literal error terms in joint first amplification are the errorInput
sources bounded by ActualErrorPower. Actual prime extraction allocations
are summed with the source mass bound before the normalized prime average. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularInput
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstChildProfileControl
open CenteredMomentFirstErrorAllocationPower CenteredMomentSecondHeightFamily
open CenteredMomentFirstScale CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentAmplifiedRetainedRadius
local notation "O" => HeckeFamily.O

/-- Definitional identification of every literal extracted common-child
term with the source errorInput consumed by actual_original_subsets_error_power. -/
theorem firstExtractedErrors_common_child {ι : Type*} [Fintype ι]
    (src : Input ι) (C D R₀ seed E : Ideal O) (B : actualAllocations src.pools C)
    (τ : Character) (t Z K sigma delta reserve : ℝ) (p : O)
    (family : Fin 3 → RayCharacter → Character) :
    firstExtractedErrors (child src C R₀ B τ t) (R₀*C) seed Z
      (Real.logb Z (D.absNorm : ℝ)) (Real.logb Z (firstNominalScale C D E K (volume src)))
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve p family =
      ∑ i : Fin 3, (16*(errorIndex i+2 : ℝ)*localErrorCost p (errorIndex i))*
        ∑ χ : RayCharacter, ∑ Bp : actualAllocations (activeInput (child src C R₀ B τ t)).pools
            ((Ideal.span {p})^(errorIndex i+1)),
          normalizedGaussSource
            (errorInput src C R₀ B τ t (Ideal.span {p}) (errorIndex i+1) Bp (family i χ) t)
            ((R₀*C)*(Ideal.span {p})^(errorIndex i+1)) seed ballProfile
            (errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
              (Real.logb Z (firstNominalScale C D E K (volume src)))
              (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve p (errorIndex i+1)) := rfl

/-- The actual extraction allocations cost only the fixed valuation factor.
All source profile mass remains outside, and no first-label count is used. -/
theorem firstExtractedErrors_power_budget {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (Z d K₀ c sigma delta reserve : ℝ)
    (p : O) (hp : Prime (Ideal.span {p}))
    (hslot : ∀ j, ∀ I ∈ (activeInput s).slots j, IsCoprime (Ideal.span {p}) I)
    (family : Fin 3 → RayCharacter → Character)
    (aerror : Fin 3 → RayCharacter → Fin 4 → ℝ) (alpha : Fin 4 → ℝ)
    (haerror : ∀ i χ j, 0 ≤ aerror i χ j)
    (hbound : ∀ i χ,
      ∀ B : actualAllocations (activeInput s).pools ((Ideal.span {p})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p})^(errorIndex i+1))
          R seed B (family i χ) s.t ballProfile
          (errorCommonRadius Z d K₀ c sigma delta reserve p (errorIndex i+1)) ≤
        (∑ j, aerror i χ j*(volume (child (activeInput s)
          ((Ideal.span {p})^(errorIndex i+1)) R B (family i χ) s.t))^(alpha j))*
          mass (child (activeInput s) ((Ideal.span {p})^(errorIndex i+1)) R B (family i χ) s.t)^2) :
    firstExtractedErrors s R seed Z d K₀ c sigma delta reserve p family ≤
      mass s^2*∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*localErrorCost p (errorIndex i)*
        ∑ χ : RayCharacter, ∑ j : Fin 4, aerror i χ j*
          (volume s/(normValue p)^(errorIndex i+1))^(alpha j) := by
  have herror (i : Fin 3) (χ : RayCharacter) :
      (∑ B : actualAllocations (activeInput s).pools ((Ideal.span {p})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p})^(errorIndex i+1))
          R seed B (family i χ) s.t ballProfile
          (errorCommonRadius Z d K₀ c sigma delta reserve p (errorIndex i+1))) ≤
      (errorIndex i+2 : ℝ)*(∑ j : Fin 4, aerror i χ j*
        (volume s/(normValue p)^(errorIndex i+1))^(alpha j))*mass s^2 := by
    apply (Finset.sum_le_sum (fun B _ => hbound i χ B)).trans
    have hb := budget_sum_le (activeInput s) (Ideal.span {p}) hp (errorIndex i+1) hslot R
      (fun _ => family i χ) (fun _ => s.t) 4 (aerror i χ) alpha (haerror i χ)
    have hmass : mass (activeInput s) = mass s := rfl
    have hvolume : volume (activeInput s) = volume s := rfl
    have hcount : ((errorIndex i+1+1 : ℕ) : ℝ) = (errorIndex i : ℝ)+2 := by
      push_cast
      ring
    rw [hmass,hvolume,hcount] at hb
    simpa only [normValue] using hb
  unfold firstExtractedErrors
  calc
    _ ≤ ∑ i : Fin 3, (16*(errorIndex i+2 : ℝ)*localErrorCost p (errorIndex i))*
        ∑ χ : RayCharacter,
          ((errorIndex i+2 : ℝ)*(∑ j : Fin 4, aerror i χ j*
            (volume s/(normValue p)^(errorIndex i+1))^(alpha j))*mass s^2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => herror i χ))
      exact mul_nonneg (by positivity) (localErrorCost_nonneg _ _)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

#print axioms firstExtractedErrors_common_child
#print axioms firstExtractedErrors_power_budget
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExtractedErrorBudget -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighRetainedDominated ; sha256 e79f8548b203888d76b5de4d8090f278156bebc5ef75ba745bae2af70f083fa8 -/
section





/-! The actual retained source sum uses the joint high theorem exactly
once, after selecting one literal branch in each arithmetic fiber. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
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

/-- `hsource` is the exact source realization furnished by
`actual_retained_buffered_data`; it contains no bound for the products.
The full allocation mass and the joint high estimate are proved internally.
The maximum of the explicit fixed profile factors is retained for later
uniform source-profile control, without a sum or count of labels. -/
theorem actual_joint_high_retained_dominated_contribution
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss) :
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (s : JointReconstructionLabel → CommonSecondKernelLabel Slot)
        (Ds : JointReconstructionLabel → Finset (Ideal O))
        (z : JointReconstructionLabel → O) (t₁ t₂ H₁ H₂ : JointReconstructionLabel → ℝ)
        (aSource : ℝ), 0 < aSource →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < H₁ v ∧ 0 < H₂ v ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ H₁ v ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ H₂ v) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ Csrc : ℝ, 0 ≤ Csrc →
      (∀ v ∈ S, ∀ q ∈ (s v).activeFullRetainedFiber (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v),
        ∃ DL DR : SurvivingBufferedData η (w v) Slot orders profileBound p.lower e,
          (s v).fullFiberValue (t₁ v) (t₂ v) (z v) q ≤
            Csrc*(‖DL.value M H η₀ V Bprofile Z d‖*‖DR.value M H η₀ V Bprofile Z d‖) ∧
          d*DL.length ≤ A-c-c₂+lengthLoss ∧ d*DR.length ≤ A-c-d₂+lengthLoss ∧
          DL.Admissible M H hH η₀ Aprofile Bprofile Rwidth τ ηaux σmin σmax Z d p.height ∧
          DR.Admissible M H hH η₀ Aprofile Bprofile Rwidth τ ηaux σmin σmax Z d p.height) →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss)*
        (∑ v ∈ S, ∑ D ∈ Ds v, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ *
          ((s v).withProjector D).retainedPair (t₁ v) (t₂ v) (z v) (H₁ v) (H₂ v)) ≤
        (C*Csrc)*retainedProfileEnvelope S s aSource*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨τ,ν,orders,N,Ch,hν,hντ,hτdet,hheight,horders,hCh,hhigh⟩ :=
    actual_joint_high_contribution η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV Rwidth dmax ε e κ ηaux σmin σmax
      productLoss populationLoss loss B hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget
      hproductLoss hpopulationLoss hB hloss τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      profileBound hprofile
  obtain ⟨Cm,hCm,hmass⟩ := actual_complete_retained_fiber_mass lo hi (2*B) fiberLoss
    (by positivity) hfiberLoss
  refine ⟨τ,ν,orders,N,Cm*Ch,hν,hντ,hτdet,hheight,horders,mul_pos hCm hCh,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t₁ t₂ H₁ H₂ aSource haSource
    hsourceIntervals hsourceNorm hprojectorNorm hphysical
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂ Csrc hCsrc hsource
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal
  let outside := A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss
  let target := π+A-c+R₁+E+Bc-144011/109800000
  let envelope := retainedProfileEnvelope S s aSource
  let Ebound := Ch*Z^target/Z^(outside+fiberLoss)
  let massBound := Cm*Z^fiberLoss*envelope
  let fiber := fun v => (s v).activeFullRetainedFiber (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v)
  let weight := fun v => (s v).fullFiberWeight (t₁ v) (t₂ v) (H₁ v) (H₂ v)
  let value := fun v => (s v).fullFiberValue (t₁ v) (t₂ v) (z v)
  let gate := fun v (DL DR : SurvivingBufferedData η (w v) Slot orders profileBound p.lower e) =>
    d*DL.length ≤ A-c-c₂+lengthLoss ∧ d*DR.length ≤ A-c-d₂+lengthLoss ∧
    DL.Admissible M H hH η₀ Aprofile Bprofile Rwidth τ ηaux σmin σmax Z d p.height ∧
    DR.Admissible M H hH η₀ Aprofile Bprofile Rwidth τ ηaux σmin σmax Z d p.height
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have henv : 0 ≤ envelope := retainedProfileEnvelope_nonneg S s aSource
  have hmassBound (v : JointReconstructionLabel) (hv : v ∈ S) :
      (∑ q ∈ fiber v, weight v q) ≤ massBound := by
    apply ((s v).activeFullRetainedFiber_mass_le (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v)).trans
    apply (hZ.2 (s v) (hsourceIntervals v hv).1 (hsourceIntervals v hv).2
      (hsourceNorm v hv).1 (hsourceNorm v hv).2 (Ds v) (hprojectorNorm v hv)
      (t₁ v) (t₂ v) (H₁ v) (H₂ v) aSource haSource
      (hphysical v hv).1 (hphysical v hv).2.1 (hphysical v hv).2.2.1 (hphysical v hv).2.2.2).trans
    exact mul_le_mul_of_nonneg_left (retainedProfileEnvelope_bound S s aSource v hv) (by positivity)
  have hselected (T : Finset JointReconstructionLabel) (hTS : T ⊆ S)
      (FL FR : ∀ v, SurvivingBufferedData η (w v) Slot orders profileBound p.lower e)
      (hgates : ∀ v ∈ T, gate v (FL v) (FR v)) :
      (∑ v ∈ T, ‖(FL v).value M H η₀ V Bprofile Z d‖ *
        ‖(FR v).value M H η₀ V Bprofile Z d‖) ≤ Ebound := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hZpos _)).mpr
    have hh := hhigh Z d P W hZ.1 hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
      unit T w (fun v hv => hw v (hTS hv)) R hR (fun v hv => hsup v (hTS hv))
      (fun v hv => heq v (hTS hv)) (fun v hv => hproj v (hTS hv))
      (fun v hv => hbin v (hTS hv)) (fun v hv => hnorm v (hTS hv))
      (fun v hv => hNw v (hTS hv)) (fun v hv => hNr v (hTS hv)) FL FR
      (fun v hv => (hgates v hv).2.2.1) (fun v hv => (hgates v hv).2.2.2)
      A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost (omegaLoss+fiberLoss) geometryLoss lengthLoss missingLoss c₂ d₂
      hb₂ (fun v hv => (hgates v hv).1) (fun v hv => (hgates v hv).2.1)
      hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂ hgeometryLoss hlengthLoss
      hW hP (by linarith)
    convert hh using 1 <;> dsimp [outside,target] <;> ring
  have hweighted := joint_buffered_product_fibers_of_le M H η η₀ V Bprofile
    orders profileBound p.lower e Z d S w fiber weight value massBound Ebound Csrc
    (by dsimp [massBound]; positivity) (by dsimp [Ebound]; positivity) hCsrc gate
    (fun v _ q _ => (s v).fullFiberWeight_nonneg _ _ _ _ q)
    (fun v _ q _ => (s v).withProjector q.1 |>.fiberValue_nonneg _ _ _ q.2)
    hmassBound hsource hselected
  calc
    _ ≤ Z^outside*(∑ v ∈ S, ∑ q ∈ fiber v, weight v q*value v q) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZpos.le _)
      exact Finset.sum_le_sum (fun v hv =>
        (s v).retained_projector_sum_le_activeFullFiber (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v))
    _ ≤ Z^outside*(massBound*(Csrc*Ebound)) := mul_le_mul_of_nonneg_left hweighted (Real.rpow_nonneg hZpos.le _)
    _ = ((Cm*Ch)*Csrc)*retainedProfileEnvelope S s aSource*Z^target := by
      dsimp only [massBound,Ebound,envelope]
      rw [Real.rpow_add hZpos outside fiberLoss]
      field_simp
      <;> ring

end FixedData
#print axioms actual_joint_high_retained_dominated_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighRetainedDominated -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSource ; sha256 7fb03589300f9d37b07b7462a05e0071a866d522e4070bad2819c09c9edc62e6 -/
section


/-! The high retained source estimate with every buffered product
constructed internally from its literal source coefficient identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
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

theorem actual_joint_high_source_contribution
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (hσmin : σmin ≤ 0) (hσmax : 0 ≤ σmax)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (s : JointReconstructionLabel → CommonSecondKernelLabel Slot)
        (Ds : JointReconstructionLabel → Finset (Ideal O))
        (z : JointReconstructionLabel → O) (t₁ t₂ H₁ H₂ : JointReconstructionLabel → ℝ)
        (aSource : ℝ), 0 < aSource →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < H₁ v ∧ 0 < H₂ v ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ H₁ v ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ H₂ v) →
      ∀ (parentL parentR : JointReconstructionLabel → JointParentLabel η)
        (NL : ∀ v, CenteredMomentNaturalRowSource.NaturalRow (parentL v).val (w v).val)
        (NR : ∀ v, CenteredMomentNaturalRowSource.NaturalRow (parentR v).val (w v).val)
        (punctureL punctureR : JointReconstructionLabel → Ideal O),
      (∀ v, punctureL v ≠ 0) → (∀ v, punctureR v ≠ 0) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, ∀ j, (s v).input.slots j =
        CenteredMomentPrimeSlot.primePool M H (Bprofile j) ((s v).input.P j)) →
      (∀ v ∈ S, ∀ j J, (s v).input.ν j J = idealCoeff (η₀ j).inverse J) →
      (∀ v ∈ S, ∀ j, (s v).input.W j = V j) →
      (∀ v ∈ S, ∀ J : Ideal O, CenteredMomentHeckeExpansion.rowWeight
        (CenteredMomentChildRows.childCharacter (s v).parent (s v).leftRay)
        (fixedBadMask*idealGenerator ((s v).puncture*((s v).firstCommon*(s v).second.val.1)))
        (s v).toKernelLabel.frequency (z v) (t₁ v) J =
        CenteredMomentHeckeExpansion.rowWeight (parentL v).val
          (fixedBadMask*idealGenerator (punctureL v)) 1 (w v).val (t₁ v) J) →
      (∀ v ∈ S, ∀ J : Ideal O, CenteredMomentHeckeExpansion.rowWeight
        (CenteredMomentChildRows.childCharacter (s v).parent ((s v).rightRay⁻¹))
        (fixedBadMask*idealGenerator ((s v).puncture*((s v).firstCommon*(s v).second.val.2)))
        (s v).toKernelLabel.frequency (-(z v)) (t₂ v) J =
        CenteredMomentHeckeExpansion.rowWeight (parentR v).val
          (fixedBadMask*idealGenerator (punctureR v)) 1 (w v).val (t₂ v) J) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ label, (bufferedProductFamily M H hH η₀
        (CenteredMomentNaturalRowSource.excluded (NL v).character (punctureL v)) label).modulus.absNorm ≤ Z^d) →
      (∀ v ∈ S, ∀ label, (bufferedProductFamily M H hH η₀
        (CenteredMomentNaturalRowSource.excluded (NR v).character (punctureR v)) label).modulus.absNorm ≤ Z^d) →
      (∀ v ∈ S, |t₁ v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ ∧ |t₂ v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux → (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      (∀ v ∈ S, ∀ j, 2*(|Real.log (Aprofile j)|+|Real.log (Bprofile j)|)+1 ≤ Real.log ((s v).input.P j)) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      (∀ v ∈ S, ∀ q ∈ (s v).activeFullRetainedFiber (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v),
        (s v).fullLeftLength Z q+Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ A-c-c₂+lengthLoss ∧
        (s v).fullRightLength Z q+Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ A-c-d₂+lengthLoss) →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss)*
        (∑ v ∈ S, ∑ D ∈ Ds v, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ *
          ((s v).withProjector D).retainedPair (t₁ v) (t₂ v) (z v) (H₁ v) (H₂ v)) ≤
        C*retainedProfileEnvelope S s aSource*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨profileBound,hprofile,hdata⟩ := actual_retained_buffered_data
    W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  obtain ⟨τ,ν,orders,N,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_retained_contribution η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV Rwidth dmax ε e κ ηaux σmin σmax
      productLoss populationLoss loss B hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget
      hproductLoss hpopulationLoss hB hloss τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      profileBound (fun k => (hprofile k).le) lo hi fiberLoss hfiberLoss
  refine ⟨profileBound,hprofile,τ,ν,orders,N,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t₁ t₂ H₁ H₂ aSource haSource
    hsourceIntervals hsourceNorm hprojectorNorm hphysical parentL parentR NL NR punctureL punctureR
    hpunctureL hpunctureR hplain hslots hνsource hWsource hrowL hrowR hscale hprimeScale
    hcondL hcondR hfreq hfour htwo hlog
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂ hlength
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal
  have hdne : d ≠ 0 := by
    intro hh
    rw [hh,Real.rpow_zero] at hbase
    norm_num at hbase
  apply hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t₁ t₂ H₁ H₂ aSource haSource
    hsourceIntervals hsourceNorm hprojectorNorm hphysical
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂ ?_
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal
  intro v hv q hq
  have hqLive := (s v).activeFullRetainedFiber_live (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v) hq
  obtain ⟨DL,DR,hnorm,hlenL,hlenR,hadL,hadR⟩ := hdata orders p.lower e
    (by linarith [p.upper_bound]) he'.le M H hH η (w v) (parentL v) (parentR v) (NL v) (NR v)
    (punctureL v) (punctureR v) (hpunctureL v) (hpunctureR v)
    (s v) (Ds v) (z v) (t₁ v) (t₂ v) Z d η₀ V Aprofile Bprofile i
    Rwidth τ ηaux σmin σmax p.height (hplain v hv).1 (hplain v hv).2
    (hslots v hv) (hνsource v hv) (hWsource v hv) (hrowL v hv) (hrowR v hv)
    hZ.1 hdne (lt_of_lt_of_le (by norm_num) hbase) hRw
    (hscale v hv).1 (hscale v hv).2.1 (hscale v hv).2.2.1 (hscale v hv).2.2.2
    (hprimeScale v hv) hσmin hσmax (hcondL v hv) (hcondR v hv)
    (hfreq v hv).1 (hfreq v hv).2 hfour htwo (hlog v hv)
    (by rw [hheightBin]) q hqLive
  exact ⟨DL,DR,hnorm,hlenL.trans (hlength v hv q hq).1,
    hlenR.trans (hlength v hv q hq).2,hadL,hadR⟩

end FixedData
#print axioms actual_joint_high_source_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowClipped ; sha256 36b3684fe95cd25bbe5c39c71077a56054db210e93307d685efc4c87360996c9 -/
section





/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot ConcretePrimeRowBridge LocalMoment LocalMomentSourceAudit
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
open CenteredMomentEnergyCapacityRemoval
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedChildren
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero
open CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentAllocatedNaturalSource
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance lowClippedFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


def restrictedLowRadial (r : Radial) (low : O → Prop) : Radial :=
  {r with keep := fun z => r.keep z ∧ low z}

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma allocated_low_pair {Z Bmask radial a b : ℝ} (s : NaturalState Z Bmask radial)
    (hunit : s.puncture = 1) (low : O → Prop)
    (D : Ideal O) (alloc : Allocation D (Finset.univ : Finset (α ⊕ Fin 2)))
    (ha : 0 < a) (p : Profiles a b) (pool : α → Finset (Ideal O))
    (β : α → Ideal O → ℂ) (P : α → ℝ) (v X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset α) :
    allocatedEnergy s.character (restrictedLowRadial s.radial low) D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1)) pool β P v X₁ X₂ hX₁ hX₂ F₁ F₂ J =
    energy s.character s.mask 1 0
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 0)
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 1)
      (fun i : ↥(liveIndices D alloc \ J) => pool i)
      (fun i : ↥(liveIndices D alloc \ J) => CenteredMomentCommonMaskEnergy.heightCoefficient (β i) v)
      (fun i : ↥(liveIndices D alloc \ J) => P i)
      (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
      (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale := by
  simp only [allocatedEnergy,restrictedLowRadial,pair,retainedPair,scale,NaturalState.mask,hunit,
    Matrix.cons_val_zero,Matrix.cons_val_one]

theorem actual_clipped_allocated_low_moment
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hL : 0 ≤ L) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (v height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (s : NaturalState Z Bmask radial) (hQ : s.fixedModulus = internalQ Q η₀),
      s.puncture = 1 → s.width ≤ Mcap → ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : s.radial.keep z, low z → NaturalLowGate M H hH s η₀ Q hQM hQ d τ e abin k z hz) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (p : Profiles a b) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂), X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ src : Input α, Matches M H hH src η₀ θ w σ freq W bslot Z →
      ∀ (C R : Ideal O) (B : actualAllocations src.pools C) (D : Ideal O)
        (alloc : Allocation D (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
        (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)),
      ∀ F₁ F₂ : Finset (Ideal O), (∀ I ∈ F₁, I ≠ 0) → (∀ I ∈ F₂, I ≠ 0) →
      let data := commonData (withHeight src s.character v) C R B
      allocatedEnergy s.character (restrictedLowRadial s.radial low) D alloc
        (sourcePlain a b ha (p.profile 0) (p.support 0))
        (sourcePlain a b ha (p.profile 1) (p.support 1))
        data.slots data.coefficient data.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cbound*diagonalControl s.radial.profile*(p.control S)^2*(1+|v|+height)^degree *
        Z^(s.width+(67/450)*max (length Z (scale D alloc X₁ 0 F₁)+length Z (scale D alloc X₂ 1 F₂)+
          (9/2)*(∑ i ∈ originalImage src C B D alloc J, w i)-s.width) 0+loss) := by
  have hmax : 0 < max 1 b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha' : 0 < a/max 1 b := div_pos ha hmax
  have haUpper' : a/max 1 b ≤ 1/4 := by
    apply (div_le_iff₀ hmax).mpr
    nlinarith [le_max_left (1 : ℝ) b]
  obtain ⟨degree,S,hmain⟩ := actual_allocated_low_moment (α := α) M H hH W
    aslot bslot (a/max 1 b) b radial Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha' haUpper' hb hrad hmask hMcap hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss
  obtain ⟨n,T,Cp,hCp,hprofile⟩ := retained_pair_control a b ha S
  refine ⟨degree+4*n,T,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound*Cp^2,mul_pos hCbound (sq_pos_of_pos hCp),?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s hQ hunit hs low abin k
    habin habinTop hbase hT hlow hfreqGate hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
    src hmatch C R B D alloc J F₁ F₂ hF₁ hF₂ data
  rw [allocated_low_pair s hunit low]
  have hh := hmain.2 θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s hQ hs
    low abin k habin habinTop hbase hT hlow hfreqGate hheightSource
    (pair D alloc ha p v X₁ X₂ hX₁ hX₂) (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
    (scale_pos D alloc X₁ 0 F₁ hF₁) (scale_pos D alloc X₂ 1 F₂ hF₂)
    (scale_cap D alloc Z L X₁ hmain.1.le hL hX₁ hc₁ 0 F₁ hF₁)
    (scale_cap D alloc Z L X₂ hmain.1.le hL hX₂ hc₂ 1 F₂ hF₂)
    src hmatch C R B D alloc J
  let U : Fin 2 → ℝ := ![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
  have hU : ∀ i, 0 < U i := by
    intro i; fin_cases i
    · exact rawScale_pos D alloc X₁ hX₁ 0
    · exact rawScale_pos D alloc X₂ hX₂ 1
  have hcontrol : (pair D alloc ha p v X₁ X₂ hX₁ hX₂).control S ≤
      Cp*p.control T*(1+|v|+height)^(2*n) := by
    have hh := hprofile p U hU v
    have hpw : (1+‖v‖)^(2*n) ≤ (1+|v|+height)^(2*n) :=
      pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs]; linarith) _
    exact hh.trans (mul_le_mul_of_nonneg_left hpw (mul_nonneg hCp.le (p.control_nonneg T)))
  apply hh.trans
  have hdiag := diagonalControl_nonneg s.radial.profile
  calc
    _ ≤ Cbound*diagonalControl s.radial.profile*
        (Cp*p.control T*(1+|v|+height)^(2*n))^2*(1+|v|+height)^degree *
        Z^(s.width+(67/450)*max (length Z (scale D alloc X₁ 0 F₁)+
          length Z (scale D alloc X₂ 1 F₂)+(9/2)*(∑ i ∈ originalImage src C B D alloc J,w i)-s.width) 0+loss) := by
      gcongr
      · exact Real.rpow_nonneg (le_trans zero_le_one hmain.1.le) _
      · exact (pair D alloc ha p v X₁ X₂ hX₁ hX₂).control_nonneg S
    _ = _ := by
      have hpow : (1+|v|+height)^(4*n) = ((1+|v|+height)^(2*n))^2 := by
        rw [←pow_mul]
        congr 1
        omega
      simp only [mul_pow,pow_add,hpow]
      ring

theorem actual_clipped_allocated_low_contribution
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hL : 0 ≤ L) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (v height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (s : NaturalState Z Bmask radial) (hQ : s.fixedModulus = internalQ Q η₀),
      s.puncture = 1 → s.width ≤ Mcap → ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : s.radial.keep z, low z → NaturalLowGate M H hH s η₀ Q hQM hQ d τ e abin k z hz) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (p : Profiles a b) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂), X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ src : Input α, Matches M H hH src η₀ θ w σ freq W bslot Z →
      ∀ (C R : Ideal O) (B : actualAllocations src.pools C) (D : Ideal O)
        (alloc : Allocation D (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
        (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)),
      ∀ F₁ F₂ : Finset (Ideal O), (∀ I ∈ F₁, I ≠ 0) → (∀ I ∈ F₂, I ≠ 0) →
      ∀ nominal pad g allowance ledgerLoss : ℝ,
      0 ≤ pad → s.width ≤ nominal+pad → 0 ≤ g → g ≤ 37/10000 →
      3/500 ≤ allowance → 0 ≤ ledgerLoss →
      length Z (scale D alloc X₁ 0 F₁)+length Z (scale D alloc X₂ 1 F₂)+
        (9/2)*(∑ i ∈ originalImage src C B D alloc J,w i)-nominal ≤ g+6*(3/500)+ledgerLoss →
      pad+loss+(67/450)*ledgerLoss ≤ 401/9000000 →
      let data := commonData (withHeight src s.character v) C R B
      allocatedEnergy s.character (restrictedLowRadial s.radial low) D alloc
        (sourcePlain a b ha (p.profile 0) (p.support 0))
        (sourcePlain a b ha (p.profile 1) (p.support 1))
        data.slots data.coefficient data.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cbound*diagonalControl s.radial.profile*(p.control S)^2*(1+|v|+height)^degree *
        Z^(nominal+allowance-401/9000000) := by
  obtain ⟨degree,S,hmain⟩ := actual_clipped_allocated_low_moment (α := α) M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s hQ hunit hs low abin k
    habin habinTop hbase hT hlow hfreqGate hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
    src hmatch C R B D alloc J F₁ F₂ hF₁ hF₂
    nominal pad g allowance ledgerLoss hpad hwidth hg hgcap hallowance hledgerLoss hdefect hbudgetLoss data
  have hb := hmain.2 θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq
    s hQ hunit hs low abin k habin habinTop hbase hT hlow hfreqGate hheightSource
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ src hmatch C R B D alloc J F₁ F₂ hF₁ hF₂
  have hwidth := low_nominal_width s.width nominal
    (length Z (scale D alloc X₁ 0 F₁)+length Z (scale D alloc X₂ 1 F₂)+
      (9/2)*(∑ i ∈ originalImage src C B D alloc J,w i)) pad hpad hwidth
  have hmax : max (length Z (scale D alloc X₁ 0 F₁)+length Z (scale D alloc X₂ 1 F₂)+
      (9/2)*(∑ i ∈ originalImage src C B D alloc J,w i)-nominal) 0 ≤
      g+6*(3/500)+ledgerLoss := max_le hdefect (by linarith)
  have hreserve := local_low_reserve g hgcap
  have hdiag := diagonalControl_nonneg s.radial.profile
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hmain.1.le (by linarith)) (by positivity))

#print axioms actual_clipped_allocated_low_contribution

#print axioms actual_clipped_allocated_low_moment
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowClipped -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.CertifiedRetained ; sha256 13e69af4aa7063e2c57915c8841716ab43e85a3d17d61ded9cf60b7183ea8068 -/
section





namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open Cycle25WeightedNumeratorReflection
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceLowWindow CenteredMomentNaturalPrimitive
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 1000000

/-- Certified fourth moment of the actual natural primitive restoration. The
original scale X, presentation τ, primitive ψ and profile may vary independently
with the row. All dependence on that choice is controlled by the combined
conductor/scale bound and the stated profile seminorm. The selected family can
also be empty, in which case the zero-slot endpoint covers lengths up to U². -/
theorem certified_actual_retained_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (epsilon Cscale xi : ℝ) (hepsilon : 0 < epsilon) (hCscale : 0 < Cscale) (hxi : 0 < xi) :
    ∃degree:ℕ, ∃H:Finset (ℕ×ℕ), ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (G:rows→𝓢(ℝ,ℂ)) (X:rows→ℝ) (m B Rcap:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 → 0 < B →
      (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ B) →
      1 ≤ Rcap → (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Rcap) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      (2*(m+xi)+6*κ*(∑i,width i) ≤ 1 ∨ T=∅) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) (G i) (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*Rcap^epsilon*B^4*(1+2*((m+xi)*Real.log U))^2*
          (1+height)^degree*U^(1+D.t) := by
  obtain ⟨degree,Jp,Cp,hCp,hpositive⟩ := certified_reflected_fourier_moment F κ hκlo hκhi hbeta hκbeta
  obtain ⟨Jz,Cz,hCz,hzero⟩ := certified_reflected_zero_fourier_moment F
  obtain ⟨H,Cr,hCr,hretained⟩ := actual_retained_uniform_fourth epsilon hepsilon 2 (Jp+Jz) (by norm_num)
  refine ⟨degree,H,Cr*(Cp+Cz),by positivity,?_⟩
  filter_upwards [hpositive,hzero,eventually_retained_log_interval Cscale xi hCscale hxi]
    with U hp hz hg
  have hκpos : 0 < κ := by linarith
  have hU := hp.1
  have hUpos := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ G X m B Rcap he hX hm hmmax hB hG hRcap hR
    hcombined T width z height hw hwmax hreal hheight hzim hcapacity
  let n := m+xi
  have hn : 0 ≤ n := by dsimp [n]; linarith
  let P (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let E := (Cp+Cz)*(1+height)^degree*U^(1+D.t)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinterval : 0 ≤ n*Real.log U := mul_nonneg hn (Real.log_pos hU).le
  have hgeom (i:rows) (a:CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes (τ i) (ψ i)))
      (hY:0 < dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
      (ha:a.2∈CenteredMomentReflectedTruncation.retainedAnnuli (U^(xi/4))
        (dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2) hY) :
      Real.log (dyadicScale a.2*dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
        ∈ Set.Icc 0 (n*Real.log U) := hg.2 (τ i) (ψ i) (X i) m (hX i) (hcombined i) a hY ha
  have hpoly (i:rows) (W:ℝ→ℂ) (x freq:ℝ) :
      polynomial (τ i).inverse false W x 0 freq =
        polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false W x 0 freq :=
    (Cycle25.Weighted.RowConductor.polynomial_eq_of_elementCoeff_eq _ _
      (Cycle25.Weighted.RowConductor.inverse_elementCoeff_eq _ _ (he i)) false W x 0 freq).symm
  have hmoment (v w:ℝ) (j k:Fin 2) (x:ℝ) (hx:x∈Set.Icc 0 (n*Real.log U))
      (y:ℝ) (hy:y∈Set.Icc 0 (n*Real.log U)) :
      (∑i:rows, ‖polynomial (τ i).inverse false (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (2*Real.pi*v) *
        polynomial (τ i).inverse false (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k)
        (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
        ≤ E*((1+‖v‖)^(Jp+Jz))^2*((1+‖w‖)^(Jp+Jz))^2 := by
    have hxlen := reflection_window_length U n x hU hn hx
    have hylen := reflection_window_length U n y hU hn hy
    simp_rw [hpoly]
    rcases hcapacity with hcap | hempty
    · have hsum : 0 ≤ ∑s,width s := Finset.sum_nonneg (fun s _=> hw s)
      have hn1 : n ≤ 1 := by dsimp [n]; nlinarith
      have hexp : U^n ≤ U := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le hn1
      have hcap' : length U (Real.exp x)+length U (Real.exp y)+6*κ*(∑s,width s) ≤ 1 := by
        dsimp [n] at hxlen hylen
        linarith [hxlen.1,hylen.1]
      have hb := hp.2 rows hrows T width z height hw hwmax hreal hheight hzim
        (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
        (hxlen.2.trans hexp) (hylen.2.trans hexp) hcap' j k v w
      have hsumBound : (∑i:rows, ‖polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k) (Real.exp y) 0 (2*Real.pi*w) * P i‖^2) ≤
          (Cp*(1+height)^degree*U^(1+D.t))*((1+‖v‖)^Jp)^2*((1+‖w‖)^Jp)^2 := by
        rw [←Finset.sum_coe_sort rows] at hb
        simpa only [P] using hb
      apply hsumBound.trans
      dsimp [E]
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w,abs_nonneg v,abs_nonneg w] | omega
    · have hslot (i:rows) : P i = 1 := by subst T; simp [P]
      simp only [hslot,mul_one]
      have hexp : U^n ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU.le hmmax
      have hb := hz.2 rows hrows (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
        (hxlen.2.trans hexp) (hylen.2.trans hexp) j k v w
      have hsumBound : (∑i:rows, ‖polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k) (Real.exp y) 0 (2*Real.pi*w)‖^2) ≤
          (Cz*U^(1+D.t))*((1+‖v‖)^Jz)^2*((1+‖w‖)^Jz)^2 := by
        rw [←Finset.sum_coe_sort rows] at hb
        exact hb
      apply hsumBound.trans
      have hfac : Cz ≤ (Cp+Cz)*(1+height)^degree := by
        apply (show Cz ≤ Cp+Cz by linarith).trans
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))
      dsimp [E]
      gcongr <;> first | exact hfac | linarith [norm_nonneg v,norm_nonneg w,abs_nonneg v,abs_nonneg w] | omega
  have hresult := hretained G τ ψ P X (fun _=> U^(xi/4)) 0 (n*Real.log U) B E Rcap
    hX hinterval hgeom hB hE hG hRcap hR hmoment
  convert hresult using 1 <;> dsimp [E,n] <;> ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.CertifiedRetained -/
