/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.certb_local_20261013.Bundles.B047
import Submissions.certb_local_20261013.Bundles.B053
import Submissions.certb_local_20261013.Bundles.B064
import Submissions.certb_local_20261013.Bundles.B065
import Submissions.certb_local_20261013.Bundles.B067
import Submissions.certb_local_20261013.Bundles.B069
import Submissions.certb_local_20261013.Bundles.B071
import Submissions.certb_local_20261013.Bundles.B075
import Submissions.certb_local_20261013.Bundles.B077
import Submissions.certb_local_20261013.Bundles.B078
import Submissions.certb_local_20261013.Bundles.B081
import Submissions.certb_local_20261013.Bundles.B082
import Submissions.certb_local_20261013.Bundles.B083
import Submissions.certb_local_20261013.Bundles.B084
import Submissions.certb_local_20261013.Bundles.B085
import Submissions.certb_local_20261013.Bundles.B087
import Submissions.certb_local_20261013.Bundles.B089
import Submissions.certb_local_20261013.Bundles.B091
import Submissions.certb_local_20261013.Bundles.B092
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

/- BEGIN ORIGINAL MODULE Analytic.JointHighKernelActualRows ; sha256 7f1d362c7223547c4da750e3005bcc6d88b570feb173fb482b0ae7b6842e7bfe -/
section









/-! The high retained source estimate with every buffered product
constructed internally from its literal source coefficient identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
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

theorem actual_joint_high_kernel_from_source
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (ηcommon : Character) (hanchor : ∀ j, η₀ j = ηcommon)
    (Wslot : ℝ → ℂ) (hVslot : ∀ j, V j = Wslot)
    (bslot : ℝ) (hBslot : ∀ j, Bprofile j = bslot)
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
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss)
    (conductorReserve : ℝ) (hconductorReserve : 0 < conductorReserve)
    (Wkernel : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
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
        (z : JointReconstructionLabel → O) (t K Radius tbase firstU firstTheta : JointReconstructionLabel → ℝ)
        (n : JointReconstructionLabel → Fin 4 → ℤ) (rayWeight : JointReconstructionLabel → ℂ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ)
        (aSource : ℝ), 0 < aSource →
      (∀ v ∈ S, ‖rayWeight v‖ ≤ 1) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < dyadicScale (n v 2) ∧ 0 < dyadicScale (n v 3) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ dyadicScale (n v 2) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ dyadicScale (n v 3)) →
      ∀ (first : JointReconstructionLabel → FirstSidePresentation η)
        (hz : ∀ v, z v ≠ 0),
      (∀ v, (s v).parent = (first v).sourceParent) →
      (∀ v, (s v).puncture ≠ 0) →
      (∀ v, w v = (first v).row (s v) (z v) (hz v)) →
      ∀ Bmask : ℝ, W+Bmask+conductorReserve ≤ d →
      (∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, t v = tbase v+2*Real.pi*(firstU v-firstTheta v)) →
      (∀ v ∈ S, |tbase v| ≤ Z^ν ∧ |firstU v| ≤ Z^ν ∧ |firstTheta v| ≤ Z^ν) →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ supportLoss clipLoss commonLoss : ℝ, supportLoss+clipLoss+commonLoss ≤ lengthLoss →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A) →
      (∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ)) →
      (∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss) →
      Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →

      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      (∑ v ∈ S, ∑ D ∈ Ds v,
        ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius D : ℂ)*
            ((Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss) : ℝ) : ℂ)*rayWeight v) *
          ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) ≤
        C*(retainedProfileEnvelope S s aSource+128/aSource*(originalAbsoluteEnvelope S s plainBound₁ plainBound₂)^2+1)*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_kernel_from_geometry η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      Wkernel decay tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh,eventually_buffered_conductor M H hH η η₀ conductorReserve hconductorReserve]
    with Z hZ hconductor
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius tbase firstU firstTheta n rayWeight
    σ freq θ slotWidth aSource haSource hray hsourceIntervals hsourceNorm hprojectorNorm hphysical
    first hz hfirst hpuncture hwsource Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget
  let data (v : JointReconstructionLabel) :=
    (first v).naturalPair (s v) (hfirst v) (hpuncture v) (z v) (hz v) (w v) (hwsource v)
  let parentL := fun v => (data v).parentL
  let parentR := fun v => (data v).parentR
  let NL := fun v => (data v).naturalL
  let NR := fun v => (data v).naturalR
  exact hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius tbase firstU firstTheta n rayWeight
    σ freq θ slotWidth aSource haSource hray hsourceIntervals hsourceNorm hprojectorNorm hphysical
    parentL parentR NL NR (fun v => (first v).leftPuncture (s v))
    (fun v => (first v).rightPuncture (s v)) (fun v => (data v).punctureL_ne) (fun v => (data v).punctureR_ne) hplain hmatch
    (fun v _ => (data v).left_eq) (fun v _ => (data v).right_eq)
    hscale hprimeScale
    (fun v hv => hconductor.2 W Bmask d hconductorBalance (parentL v) (w v).val (NL v) _
      ((data v).punctureL_ne) (hNw v hv) (hmaskNorm v hv).1)
    (fun v hv => hconductor.2 W Bmask d hconductorBalance (parentR v) (w v).val (NR v) _
      ((data v).punctureR_ne) (hNw v hv) (hmaskNorm v hv).2)
    hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget

end FixedData
#print axioms actual_joint_high_kernel_from_source
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighKernelActualRows -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSourceCaps ; sha256 859107548aab2e8371b39dca20e3180a2c8e21bc25b33e26c7fc223251774921 -/
section





/-! Cumulative common norms, the actual second projector pool and physical
lower dyads are controlled directly by the original source columns. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSectors
open CenteredMomentSecondSectorColumns CenteredMomentSourceRow
open CenteredMomentActiveSource CenteredMomentSecondPhysicalBlock
open CenteredMomentFirstSourceConductorCaps CenteredMomentSourceBlockWindows
open CenteredMomentSectorLocalization CenteredMomentWholeDivisorShell
local notation "O" => HeckeFamily.O

namespace CommonSecondKernelLabel
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

theorem actual_cumulative_norm (s : CommonSecondKernelLabel Slot)
    (hz₁ : s.input.W₁ 0 = 0) (hz₂ : s.input.W₂ 0 = 0) :
    ((s.firstCommon*s.second.val.1).absNorm : ℝ) ≤ sourceRadius s.input ∧
      ((s.firstCommon*s.second.val.2).absNorm : ℝ) ≤ sourceRadius s.input :=
  actual_common_cumulative_norm s.input s.puncture s.seed s.firstCommon s.firstProjector
    s.hfirst hz₁ hz₂ s.second

theorem actual_right_column_norm (s : CommonSecondKernelLabel Slot)
    (hz₁ : s.input.W₁ 0 = 0) (hz₂ : s.input.W₂ 0 = 0)
    (J : s.toKernelLabel.RightIndex) :
    ((J : Ideal O).absNorm : ℝ) ≤ sourceRadius s.input := by
  have hres := (Finset.mem_filter.mp J.property).1
  have hcol := (mem_residualPool s.toKernelLabel.D s.toKernelLabel.hD.1
    (supportedColumns s.toKernelLabel.columns) (J : Ideal O)).mp hres
  have hβ := (mem_activeSource _ _ _).mp (Finset.mem_filter.mp hcol).1 |>.2
  have horig : (original s.input s.puncture s.seed).beta
      (s.firstCommon*(s.second.val.2*(J : Ideal O))) ≠ 0 := by
    intro hh
    apply hβ
    change commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector
      (s.second.val.2*(J : Ideal O)) = 0
    simp only [commonSecondBeta,hh,ite_self]
  have hn := original_column_norm s.input s.puncture s.seed
    (s.firstCommon*(s.second.val.2*(J : Ideal O))) hz₁ hz₂ horig
  apply (divisor_norm_le _ _ hn.1 ?_).trans hn.2
  exact (dvd_mul_left (J : Ideal O) s.second.val.2).trans (dvd_mul_left _ s.firstCommon)

theorem actual_projector_norm (s : CommonSecondKernelLabel Slot)
    (hz₁ : s.input.W₁ 0 = 0) (hz₂ : s.input.W₂ 0 = 0)
    (D : Ideal O) (hD : D ∈ s.physicalProjectors) :
    D ≠ 0 ∧ (D.absNorm : ℝ) ≤ sourceRadius s.input :=
  divisorPool_nonzero_norm Finset.univ (fun J : s.toKernelLabel.RightIndex => (J : Ideal O))
    (fun J _ => (sectorPool_supported _ _ _ J).1) (sourceRadius s.input)
    (fun J _ => s.actual_right_column_norm hz₁ hz₂ J) D hD

/-- No nonzero Möbius hypothesis is needed for the source pool cap. -/
theorem actual_norm_power_caps (s : CommonSecondKernelLabel Slot)
    (hz₁ : s.input.W₁ 0 = 0) (hz₂ : s.input.W₂ 0 = 0)
    (Z B : ℝ) (hsource : sourceRadius s.input ≤ Z^B) :
    (((s.firstCommon*s.second.val.1).absNorm : ℝ) ≤ Z^B ∧
      ((s.firstCommon*s.second.val.2).absNorm : ℝ) ≤ Z^B) ∧
      ∀ D ∈ s.physicalProjectors, (D.absNorm : ℝ) ≤ Z^B :=
  ⟨⟨(s.actual_cumulative_norm hz₁ hz₂).1.trans hsource,
      (s.actual_cumulative_norm hz₁ hz₂).2.trans hsource⟩,
    fun D hD => (s.actual_projector_norm hz₁ hz₂ D hD).2.trans hsource⟩

theorem actual_physical_lower_dyads (s : CommonSecondKernelLabel Slot)
    (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (h₁ : ∀ x, s.input.W₁ x ≠ 0 → a₁ ≤ x)
    (h₂ : ∀ x, s.input.W₂ x ≠ 0 → a₂ ≤ x)
    (t Radius : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ)
    (hne : physicalBlock s.parent t s.toKernelLabel.columns s.toKernelLabel.beta
      s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD
      s.partition Radius rows W K n ≠ 0) :
    0 < dyadicScale (n 2) ∧ 0 < dyadicScale (n 3) ∧
      originalLowerProfile s.input a₁ a₂*CenteredMomentExceptionalAmplitudePair.volume s.input.toData/
        ((s.firstCommon*s.second.val.1).absNorm : ℝ) ≤ dyadicScale (n 2) ∧
      originalLowerProfile s.input a₁ a₂*CenteredMomentExceptionalAmplitudePair.volume s.input.toData/
        ((s.firstCommon*s.second.val.2).absNorm : ℝ) ≤ dyadicScale (n 3) := by
  have ha := originalLowerProfile_pos s.input a₁ a₂ ha₁ ha₂
  have hh := physicalBlock_scale_lower s.parent t s.toKernelLabel.columns s.toKernelLabel.beta
    s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD
    s.partition Radius rows W K n (originalLowerProfile s.input a₁ a₂)
    (CenteredMomentExceptionalAmplitudePair.volume s.input.toData/(s.firstCommon.absNorm : ℝ)) ha
    (common_second_column_lower s.input s.puncture s.seed s.firstCommon s.firstProjector
      s.hfirst.1 a₁ a₂ ha₁.le ha₂.le h₁ h₂) hne
  refine ⟨dyadicScale_pos _,dyadicScale_pos _,?_,?_⟩
  · have h := (le_div_iff₀ ha).mp hh.1
    convert h using 1
    simp only [map_mul,Nat.cast_mul]
    field_simp <;> ring
  · have h := (le_div_iff₀ ha).mp hh.2
    convert h using 1
    simp only [map_mul,Nat.cast_mul]
    field_simp <;> ring

end CommonSecondKernelLabel

namespace ActualJointSourceRow
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] {side : Bool}

theorem actual_four_common_norms (input : Input Slot) (puncture seed : Ideal O)
    (q : ActualJointSourceRow (original input puncture seed) side)
    (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0) :
    (q.label.C₁.absNorm : ℝ) ≤ sourceRadius input ∧
      (q.label.D₁.absNorm : ℝ) ≤ sourceRadius input ∧
      (q.label.C₂.absNorm : ℝ) ≤ sourceRadius input ∧
      (q.label.D₂.absNorm : ℝ) ≤ sourceRadius input := by
  have hfirst := commonLabel_norm_bounds (original input puncture seed).columns
    (original input puncture seed).beta (sourceRadius input)
    (fun I _ hI => (original_column_norm input puncture seed I hz₁ hz₂ hI).2)
    _ _ q.first.property
  have hsecond := actual_common_cumulative_norm input puncture seed
    (sourceFirstCommon side q.first.val) q.L (sourceFirstCommon_supported _ side q.first)
    hz₁ hz₂ q.second
  have hs := CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (activeSource _ _) _ _ q.second.property
  have hc : (q.second.val.1.absNorm : ℝ) ≤ sourceRadius input :=
    (divisor_norm_le _ _
      (mul_ne_zero (sourceFirstCommon_supported _ side q.first).1 hs.1.1)
      (dvd_mul_left q.second.val.1 (sourceFirstCommon side q.first.val))).trans hsecond.1
  have hd : (q.second.val.2.absNorm : ℝ) ≤ sourceRadius input :=
    (divisor_norm_le _ _
      (mul_ne_zero (sourceFirstCommon_supported _ side q.first).1 hs.2.1)
      (dvd_mul_left q.second.val.2 (sourceFirstCommon side q.first.val))).trans hsecond.2
  cases side
  · exact ⟨hfirst.2,hfirst.1,hc,hd⟩
  · exact ⟨hfirst.1,hfirst.2,hc,hd⟩

theorem sourceRadius_pos (input : Input Slot) (puncture seed : Ideal O)
    (q : ActualJointSourceRow (original input puncture seed) side)
    (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0) :
    0 < CenteredMomentOriginalCommonHarmonic.sourceRadius input :=
  (CenteredMomentFirstScale.norm_pos _ q.label_supported.1.1).trans_le
    (q.actual_four_common_norms input puncture seed hz₁ hz₂).1

end ActualJointSourceRow
#print axioms CommonSecondKernelLabel.actual_projector_norm
#print axioms CommonSecondKernelLabel.actual_norm_power_caps
#print axioms CommonSecondKernelLabel.actual_physical_lower_dyads
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSourceCaps -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowBinSupport ; sha256 230cb8c526369617e202b3d4bd8fe3427f4719d8e63832b44646250e4e65a4c9 -/
section



/-! A single nonexceptional source bin supplies both canonical low-energy
keep predicates, including the right reflected frequency and every ray. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentChildRows
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

lemma canonical_low_keep_pair_of_source_bin
    {Slot κ : Type*} [Fintype Slot] {η : Character}
    (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (bin : NonzeroElement → Option κ)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w, bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (family : RayCharacter → Character)
    (hfamily : Family s.parent s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD s.partition family)
    (z : O) (hz : z ≠ 0) (b : κ) (hb : F.sourceBin s bin z = some b)
    (χ ξ : RayCharacter) (n : Fin 4 → ℤ) :
    (canonicalRadial (family χ) Q n).keep z ∧
      (canonicalRadial (family ξ) Q n).keep (-z) := by
  have hsource : ¬FixedInducingRow (childCharacter s.parent χ) Q fixedBadMask s.toKernelLabel.frequency z := by
    intro h
    have hn := (F.sourceBin_none_iff s hs bin Q hQ72 hbin χ fixedBadMask z
      fixedBadMask_ne_zero (by exact dvd_mul_right _ _) (by exact dvd_mul_left _ _) hz).mpr h
    rw [hb] at hn
    cases hn
  have hleft : ¬FixedInducingRow (family χ) Q fixedBadMask 1 z := by
    intro h
    exact hsource ((hfamily.inducing_iff χ Q fixedBadMask z fixedBadMask_ne_zero hz
      (by exact dvd_mul_right _ _) (by exact dvd_mul_left _ _)).mpr h)
  have hright : ¬FixedInducingRow (family ξ) Q fixedBadMask 1 (-z) := by
    intro h
    exact hleft ((hfamily.paired_inducing_iff χ ξ Q hQ72 fixedBadMask z
      fixedBadMask_ne_zero hz (by exact dvd_mul_right _ _) (by exact dvd_mul_left _ _)).mpr h)
  exact ⟨⟨hz,hleft⟩,⟨neg_ne_zero.mpr hz,hright⟩⟩

/-- The actual shared bin and the exact dyadic support restriction supply
both reflected low source supports at once. -/
lemma actual_low_bin_support_pair
    {Slot κ : Type*} [Fintype Slot] {η : Character}
    (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (bin : NonzeroElement → Option κ)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w, bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (family : RayCharacter → Character)
    (hfamily : Family s.parent s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD s.partition family)
    (b : κ) (χ ξ : RayCharacter) (n : Fin 4 → ℤ) (Radius : ℝ) :
    ∀ z ∈ ((sourceRows s.second.val.1 s.second.val.2 s.partition Radius).filter
      (fun z => F.sourceBin s bin z = some b)).filter (fun z => normValue z ≤ dyadicScale (n 1)),
      (canonicalRadial (family χ) Q n).keep z ∧
      (canonicalRadial (family ξ) Q n).keep (-z) ∧
      F.sourceBin s bin z = some b ∧ normValue z ≤ dyadicScale (n 1) := by
  intro z hz
  obtain ⟨⟨hz,hb⟩,hn⟩ := Finset.mem_filter.mp hz |>.imp_left Finset.mem_filter.mp
  have hzero := sourceRows_nonzero _ _ _ _ _ hz
  have hk := canonical_low_keep_pair_of_source_bin F s hs bin Q hQ72 hbin family hfamily z hzero b hb χ ξ n
  exact ⟨hk.1,hk.2,hb,hn⟩

#print axioms canonical_low_keep_pair_of_source_bin
#print axioms actual_low_bin_support_pair
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowBinSupport -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowPairedBound ; sha256 804193e3718dd49bec4598a28c2a47608bb41e64706ce9dfca6f19a23363fc9f -/
section
















/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
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
open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentRadialEligibleEnergy
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
local instance lowPairedBoundFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

open CanonicalQuadraticSieve CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialSource CenteredMomentSourceProfileMass CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialCost CenteredMomentCommonLinearNormalization

open ActualEisensteinCubic RayFourExpansion CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentEnergyChildState
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit CenteredMomentExceptionalAmplitudePair

open CenteredMomentActiveSource CenteredMomentCompleteCommon CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate
theorem actual_second_low_paired_values_of_common_bin
    (W : ℝ → ℂ) (aslot bslot a b Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hL : 0 ≤ L) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss)
    (Mslot εmask : ℝ) (hMslot : 0 ≤ Mslot) (hεmask : 0 < εmask)
    (loInput hiInput : α → ℝ) (Bcommon δcommon : ℝ) (hBcommon : 0 ≤ Bcommon) (hδcommon : 0 < δcommon)
    (ηfirst : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss)
    (ξconductor : ℝ) (hξconductor : 0 < ξconductor) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (vL vR height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (C₁ D₁ Rmask seed Lproj Lfirst : Ideal O) (hC₁ : Supported C₁) (hD₁ : D₁ ≠ 0)
        (p₂ : ActiveLabel (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)),
      let C₂ := p₂.val.1
      let D₂ := p₂.val.2
      let hC₂ := lowActiveLeftSupported p₂
      let hD₂ := lowActiveRightSupported p₂
      primeSupport C₂ = primeSupport D₂ →
      ∀ (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
      activeConductor C₁ D₁ = (u : O)*∏ i,activePrimary C₁ D₁ i ∧
      ∀ left : Bool, let parent := firstSideCharacter F left
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family parent C₂ D₂ hC₂ hD₂ U family →
      Rmask ≠ 0 → seed ∣ C₁*C₂ → seed ∣ C₁*D₂ → Squarefree Lproj →
      ((C₁*C₂).absNorm : ℝ) ≤ Z^Bcommon → ((C₁*D₂).absNorm : ℝ) ≤ Z^Bcommon →
      (Lproj.absNorm : ℝ) ≤ Z^Bcommon →
      ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
        (Wrad : 𝓢(ℝ,ℂ)) (Kcut : ℝ) (n : Fin 4 → ℤ)
        (Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip : ℝ),
      0 < Kcut → 0 < Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 429/100000 → 0 ≤ omegaLoss → 3/500 ≤ allowance →
      0 ≤ profileLoss → 0 ≤ clip → Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let c := Real.logb Z (C₁.absNorm : ℝ)
      let d₁ := Real.logb Z (D₁.absNorm : ℝ)
      let r₁ := Real.logb Z (normValue (activeConductor C₁ D₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E₁))
      let radius := frequencyRadius (jointSecondNominal C₁ Hsource Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss) Z ξ
      let nominal := jointLowNominal Mparent c d₁ (3/500) omegaLoss
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ))
      let pad := 2*sourceLoss+parentLoss+ξ/2+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → nominal+pad ≤ Mcap → nominal+pad+Bmask+ξconductor ≤ d →
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 19/30000000 →
      ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows Wrad Kcut n ≠ 0,
      ∀ χL χR : RayCharacter,
      let sL := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χL (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      let sR := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χR (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      ∀ (holes : O → JointRelativeLabel ηfirst (Option (α × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ z label,holes z label ≠ 0),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState sL).radial.keep z, low z →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes z) (hholes z) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left z (sL.row_ne_zero z hz.1))) →
      (∀ z, ∀ hz : (supportedNaturalState sR).radial.keep z, low (-z) →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes (-z)) (hholes (-z)) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left (-z) (neg_ne_zero.mpr (sR.row_ne_zero z hz.1)))) →
      (∀ i, |vL+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (∀ i, |vR+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (HL HR : ℝ), 0 < HL → 0 < HR → ∀ Ω : Finset O,
      (∀ z ∈ Ω,sL.radial.keep z ∧ low z) →
      (∀ z ∈ Ω,sR.radial.keep (-z) ∧ low z) →
      (∀ z ∈ Ω,normValue z ≤ dyadicScale (n 1)) →
      let BL := Cbound*((Rmask*(C₁*C₂)).radical.absNorm : ℝ)^εmask*profileCost src*
        diagonalControl sL.radial.profile*(p.control S)^2*(1+|vL|+height)^degree *
        Z^(δcommon+(nominal+allowance-19/30000000))/(((C₁*C₂).absNorm : ℝ)*Lproj.absNorm)
      let BR := Cbound*((Rmask*(C₁*D₂)).radical.absNorm : ℝ)^εmask*profileCost src*
        diagonalControl sR.radial.profile*(p.control S)^2*(1+|vR|+height)^degree *
        Z^(δcommon+(nominal+allowance-19/30000000))/(((C₁*D₂).absNorm : ℝ)*Lproj.absNorm)
      (∑ z ∈ Ω,
        ‖secondChildValue parent vL
          (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)
          C₂ hC₂ (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) Lproj χL z HL‖ *
        ‖secondChildValue parent vR
          (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)
          D₂ hD₂ (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) Lproj χR (-z) HR‖) ≤
        (volume src.toData/Real.sqrt (HL*HR))*(Real.sqrt BL*Real.sqrt BR) := by
  obtain ⟨degree,S,hmain⟩ := actual_second_low_source_of_common_bin M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain] with Z hmain
  intro hZ θ w σ freq vL vR height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ C₂ D₂ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  have hbase (v : ℝ) := hmain hZ θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ C₂ D₂ Rmask seed Lproj hC₁ hD₁ hC₂ hD₂ hCD₂ E₁ ξ₁ ξ₂ F
  refine ⟨(hbase vL).1,?_⟩
  intro left parent U family hfamily hR hseedL hseedR hLproj hCcap hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hconductorSource hbudgetSource hne χL χR sL sR low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hbinR hfreqGateL hfreqGateR hheightSource HL HR hHL hHR Ω hkeepL hkeepR hnorm BL BR
  have hbL := (hbase vL).2 left U family hfamily C₂ (Or.inl rfl) hR hseedL hLproj hCcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hconductorSource hbudgetSource hne χL false low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hfreqGateL hheightSource
  have hbR := (hbase vR).2 left U family hfamily D₂ (Or.inr rfl) hR hseedR hLproj hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hconductorSource hbudgetSource hne χR true (fun z => low (-z)) abin k
    (fun z => holes (-z)) (fun z => hholes (-z))
    habin habinTop hbaseScale hT hbinR hfreqGateR hheightSource
  have hmajorL (z : O) (hz : z ∈ Ω) :
      1 ≤ ((restrictedLowRadial sL.radial low).profile
        (‖ConcreteTraceCRT.eisEmbedding z‖^2/(restrictedLowRadial sL.radial low).scale)).re := by
    change 1 ≤ (CenteredMomentFirstAmplificationChoice.ballProfile
      (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (n 1))).re
    simpa only [normValue_eq_embedding] using
      CenteredMomentFirstAmplificationChoice.ballProfile_majorizes (dyadicScale (n 1)) (dyadicScale_pos _) z (hnorm z hz)
  have hmajorR (z : O) (hz : z ∈ Ω) :
      1 ≤ ((restrictedLowRadial sR.radial (fun z => low (-z))).profile
        (‖ConcreteTraceCRT.eisEmbedding (-z)‖^2/(restrictedLowRadial sR.radial (fun z => low (-z))).scale)).re := by
    change 1 ≤ (CenteredMomentFirstAmplificationChoice.ballProfile
      (‖ConcreteTraceCRT.eisEmbedding (-z)‖^2/dyadicScale (n 1))).re
    have hh := hmajorL z hz
    change 1 ≤ (CenteredMomentFirstAmplificationChoice.ballProfile
      (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (n 1))).re at hh
    simpa only [map_neg,norm_neg] using hh
  have hp := actual_common_second_paired_values src Rmask seed C₁ Lfirst hC₁ p₂ parent U family hfamily
    χL χR vL vR HL HR hHL hHR Lproj
    (restrictedLowRadial sL.radial low) (restrictedLowRadial sR.radial (fun z => low (-z))) Ω
    hkeepL (by
      intro z hz
      change sR.radial.keep (-z) ∧ low (-(-z))
      simpa only [neg_neg] using hkeepR z hz) hmajorL hmajorR
  apply hp.trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (Real.sqrt_le_sqrt hbL) (Real.sqrt_le_sqrt hbR) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (div_nonneg (volume_pos src.toData).le (Real.sqrt_nonneg _))

#print axioms actual_second_low_paired_values_of_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowPairedBound -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSelectedPairedBound ; sha256 66fa10cc76ba672f9690d0eea8acbb8610c29ff1ebd115339793b57cdcc419d4 -/
section
















/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
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
open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentRadialEligibleEnergy
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
local instance selectedLowPairedBoundFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

open CanonicalQuadraticSieve CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialSource CenteredMomentSourceProfileMass CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialCost CenteredMomentCommonLinearNormalization

open ActualEisensteinCubic RayFourExpansion CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentEnergyChildState
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit CenteredMomentExceptionalAmplitudePair

open CenteredMomentActiveSource CenteredMomentCompleteCommon CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate
theorem actual_selected_second_low_paired_values_of_common_bin
    (W : ℝ → ℂ) (aslot bslot a b Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hL : 0 ≤ L) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss)
    (Mslot εmask : ℝ) (hMslot : 0 ≤ Mslot) (hεmask : 0 < εmask)
    (loInput hiInput : α → ℝ) (Bcommon δcommon : ℝ) (hBcommon : 0 ≤ Bcommon) (hδcommon : 0 < δcommon)
    (ηfirst : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss)
    (ξconductor : ℝ) (hξconductor : 0 < ξconductor) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (vL vR height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (P₁ Q₁ : Ideal O) (hP₁ : Supported P₁),
      ∀ (C₁ D₁ Rmask seed Lproj Lfirst : Ideal O) (hC₁ : Supported C₁) (hD₁ : D₁ ≠ 0)
        (p₂ : ActiveLabel (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)),
      let C₂ := p₂.val.1
      let D₂ := p₂.val.2
      let hC₂ := lowActiveLeftSupported p₂
      let hD₂ := lowActiveRightSupported p₂
      primeSupport C₂ = primeSupport D₂ →
      ∀ (E₁ : Finset (CommonIndex P₁ Q₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F
      activeConductor P₁ Q₁ = (u : O)*∏ i,activePrimary P₁ Q₁ i ∧
      ∀ left : Bool, let parent := firstSideCharacter F left
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family parent C₂ D₂ hC₂ hD₂ U family →
      Rmask ≠ 0 → seed ∣ C₁*C₂ → seed ∣ C₁*D₂ → Squarefree Lproj →
      ((C₁*C₂).absNorm : ℝ) ≤ Z^Bcommon → ((C₁*D₂).absNorm : ℝ) ≤ Z^Bcommon →
      (Lproj.absNorm : ℝ) ≤ Z^Bcommon →
      ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
        (Wrad : 𝓢(ℝ,ℂ)) (Kcut : ℝ) (n : Fin 4 → ℤ)
        (Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip : ℝ),
      0 < Kcut → 0 < Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 429/100000 → 0 ≤ omegaLoss → 3/500 ≤ allowance →
      0 ≤ profileLoss → 0 ≤ clip → Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let c := Real.logb Z (C₁.absNorm : ℝ)
      let d₁ := Real.logb Z (D₁.absNorm : ℝ)
      let r₁ := Real.logb Z (normValue (activeConductor P₁ Q₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex P₁ Q₁ => P.val) E₁))
      let radius := frequencyRadius (jointSecondNominal C₁ Hsource Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss) Z ξ
      let nominal := jointLowNominal Mparent c d₁ (3/500) omegaLoss
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ))
      let pad := 2*sourceLoss+parentLoss+ξ/2+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → nominal+pad ≤ Mcap → nominal+pad+Bmask+ξconductor ≤ d →
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 19/30000000 →
      ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows Wrad Kcut n ≠ 0,
      ∀ χL χR : RayCharacter,
      let sL := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χL (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      let sR := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χR (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      ∀ (holes : O → JointRelativeLabel ηfirst (Option (α × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ z label,holes z label ≠ 0),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState sL).radial.keep z, low z →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes z) (hholes z) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow P₁ Q₁ hP₁ E₁ u C₂ D₂ hC₂ U left z (sL.row_ne_zero z hz.1))) →
      (∀ z, ∀ hz : (supportedNaturalState sR).radial.keep z, low (-z) →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes (-z)) (hholes (-z)) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow P₁ Q₁ hP₁ E₁ u C₂ D₂ hC₂ U left (-z) (neg_ne_zero.mpr (sR.row_ne_zero z hz.1)))) →
      (∀ i, |vL+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (∀ i, |vR+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (HL HR : ℝ), 0 < HL → 0 < HR → ∀ Ω : Finset O,
      (∀ z ∈ Ω,sL.radial.keep z ∧ low z) →
      (∀ z ∈ Ω,sR.radial.keep (-z) ∧ low z) →
      (∀ z ∈ Ω,normValue z ≤ dyadicScale (n 1)) →
      let BL := Cbound*((Rmask*(C₁*C₂)).radical.absNorm : ℝ)^εmask*profileCost src*
        diagonalControl sL.radial.profile*(p.control S)^2*(1+|vL|+height)^degree *
        Z^(δcommon+(nominal+allowance-19/30000000))/(((C₁*C₂).absNorm : ℝ)*Lproj.absNorm)
      let BR := Cbound*((Rmask*(C₁*D₂)).radical.absNorm : ℝ)^εmask*profileCost src*
        diagonalControl sR.radial.profile*(p.control S)^2*(1+|vR|+height)^degree *
        Z^(δcommon+(nominal+allowance-19/30000000))/(((C₁*D₂).absNorm : ℝ)*Lproj.absNorm)
      (∑ z ∈ Ω,
        ‖secondChildValue parent vL
          (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)
          C₂ hC₂ (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) Lproj χL z HL‖ *
        ‖secondChildValue parent vR
          (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)
          D₂ hD₂ (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) Lproj χR (-z) HR‖) ≤
        (volume src.toData/Real.sqrt (HL*HR))*(Real.sqrt BL*Real.sqrt BR) := by
  obtain ⟨degree,S,hmain⟩ := actual_selected_second_low_source_of_common_bin M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain] with Z hmain
  intro hZ θ w σ freq vL vR height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ C₂ D₂ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F
  have hbase (v : ℝ) := hmain hZ θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ C₂ D₂ Rmask seed Lproj hC₁ hD₁ hC₂ hD₂ hCD₂ E₁ ξ₁ ξ₂ F
  refine ⟨(hbase vL).1,?_⟩
  intro left parent U family hfamily hR hseedL hseedR hLproj hCcap hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hconductorSource hbudgetSource hne χL χR sL sR low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hbinR hfreqGateL hfreqGateR hheightSource HL HR hHL hHR Ω hkeepL hkeepR hnorm BL BR
  have hbL := (hbase vL).2 left U family hfamily C₂ (Or.inl rfl) hR hseedL hLproj hCcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hconductorSource hbudgetSource hne χL false low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hfreqGateL hheightSource
  have hbR := (hbase vR).2 left U family hfamily D₂ (Or.inr rfl) hR hseedR hLproj hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hconductorSource hbudgetSource hne χR true (fun z => low (-z)) abin k
    (fun z => holes (-z)) (fun z => hholes (-z))
    habin habinTop hbaseScale hT hbinR hfreqGateR hheightSource
  have hmajorL (z : O) (hz : z ∈ Ω) :
      1 ≤ ((restrictedLowRadial sL.radial low).profile
        (‖ConcreteTraceCRT.eisEmbedding z‖^2/(restrictedLowRadial sL.radial low).scale)).re := by
    change 1 ≤ (CenteredMomentFirstAmplificationChoice.ballProfile
      (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (n 1))).re
    simpa only [normValue_eq_embedding] using
      CenteredMomentFirstAmplificationChoice.ballProfile_majorizes (dyadicScale (n 1)) (dyadicScale_pos _) z (hnorm z hz)
  have hmajorR (z : O) (hz : z ∈ Ω) :
      1 ≤ ((restrictedLowRadial sR.radial (fun z => low (-z))).profile
        (‖ConcreteTraceCRT.eisEmbedding (-z)‖^2/(restrictedLowRadial sR.radial (fun z => low (-z))).scale)).re := by
    change 1 ≤ (CenteredMomentFirstAmplificationChoice.ballProfile
      (‖ConcreteTraceCRT.eisEmbedding (-z)‖^2/dyadicScale (n 1))).re
    have hh := hmajorL z hz
    change 1 ≤ (CenteredMomentFirstAmplificationChoice.ballProfile
      (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (n 1))).re at hh
    simpa only [map_neg,norm_neg] using hh
  have hp := actual_common_second_paired_values src Rmask seed C₁ Lfirst hC₁ p₂ parent U family hfamily
    χL χR vL vR HL HR hHL hHR Lproj
    (restrictedLowRadial sL.radial low) (restrictedLowRadial sR.radial (fun z => low (-z))) Ω
    hkeepL (by
      intro z hz
      change sR.radial.keep (-z) ∧ low (-(-z))
      simpa only [neg_neg] using hkeepR z hz) hmajorL hmajorR
  apply hp.trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (Real.sqrt_le_sqrt hbL) (Real.sqrt_le_sqrt hbR) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (div_nonneg (volume_pos src.toData).le (Real.sqrt_nonneg _))

#print axioms actual_selected_second_low_paired_values_of_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSelectedPairedBound -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceFinite ; sha256 db4b5a2d257d5e7eb6fe6a2903552d5946396fb3787a3d3d5f64dc0d14091cdf -/
section


/-! Exact finite source sums for fixed rays and dyadic sectors, reindexed
without changing their arithmetic multiplicity. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondBlockAggregate
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]

namespace ActualJointSourceRow
variable (s : OriginalData Slot) (side : Bool)

abbrev FirstIndex := ActiveLabel s.columns s.beta
abbrev SecondIndex (p : FirstIndex s) (L : Ideal O) :=
  ActiveLabel
    (commonSecondColumns s (sourceFirstCommon side p.val) (sourceFirstCommon_supported s side p))
    (commonSecondBeta s (sourceFirstCommon side p.val) L)

def finiteRows
    (Es : (p : FirstIndex s) → Finset (Finset (CommonIndex p.val.1 p.val.2)))
    (Ls : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) → Finset (Ideal O))
    (rows : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) →
      (L : Ideal O) → (r : SecondIndex s side p L) →
      Finset (CommonIndex r.val.1 r.val.2) → Finset O) :
    Finset (ActualJointSourceRow s side) :=
  Finset.univ.sigma fun p => (Es p).sigma fun E => (Ls p E).sigma fun L =>
    Finset.univ.sigma fun r => Finset.univ.sigma fun U => rows p E L r U

theorem mem_finiteRows
    (Es : (p : FirstIndex s) → Finset (Finset (CommonIndex p.val.1 p.val.2)))
    (Ls : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) → Finset (Ideal O))
    (rows : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) →
      (L : Ideal O) → (r : SecondIndex s side p L) →
      Finset (CommonIndex r.val.1 r.val.2) → Finset O)
    (q : ActualJointSourceRow s side) :
    q ∈ finiteRows s side Es Ls rows ↔
      q.E ∈ Es q.first ∧ q.L ∈ Ls q.first q.E ∧ q.z ∈ rows q.first q.E q.L q.second q.U := by
  dsimp only [ActualJointSourceRow] at *
  rcases q with ⟨p,E,L,r,U,z⟩
  simp only [finiteRows,Finset.mem_sigma,Finset.mem_univ,true_and]

theorem sum_finiteRows {M : Type*} [AddCommMonoid M]
    (Es : (p : FirstIndex s) → Finset (Finset (CommonIndex p.val.1 p.val.2)))
    (Ls : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) → Finset (Ideal O))
    (rows : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) →
      (L : Ideal O) → (r : SecondIndex s side p L) →
      Finset (CommonIndex r.val.1 r.val.2) → Finset O)
    (f : ActualJointSourceRow s side → M) :
    (∑ q ∈ finiteRows s side Es Ls rows, f q) =
      ∑ p : FirstIndex s, ∑ E ∈ Es p, ∑ L ∈ Ls p E,
        ∑ r : SecondIndex s side p L, ∑ U : Finset (CommonIndex r.val.1 r.val.2),
          ∑ z ∈ rows p E L r U, f ⟨p,E,L,r,U,z⟩ := by
  dsimp only [ActualJointSourceRow] at *
  simp only [finiteRows,Finset.sum_sigma]

theorem sum_labels_finiteRows {M : Type*} [AddCommMonoid M]
    (Es : (p : FirstIndex s) → Finset (Finset (CommonIndex p.val.1 p.val.2)))
    (Ls : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) → Finset (Ideal O))
    (rows : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) →
      (L : Ideal O) → (r : SecondIndex s side p L) →
      Finset (CommonIndex r.val.1 r.val.2) → Finset O)
    (f : JointReconstructionLabel → M) :
    (∑ v ∈ (finiteRows s side Es Ls rows).image label, f v) =
      ∑ p : FirstIndex s, ∑ E ∈ Es p, ∑ L ∈ Ls p E,
        ∑ r : SecondIndex s side p L, ∑ U : Finset (CommonIndex r.val.1 r.val.2),
          ∑ z ∈ rows p E L r U, f (label ⟨p,E,L,r,U,z⟩) :=
  (sum_label_image _ f).trans (sum_finiteRows s side Es Ls rows _)

variable {s side}

/-- Arbitrary source data extends along the injective arithmetic map. This
lets the full-function high theorem be applied on the exact image finset. -/
def extendData {A : Type*} (f : ActualJointSourceRow s side → A)
    (fallback : JointReconstructionLabel → A) : JointReconstructionLabel → A :=
  Function.extend label f fallback

@[simp] theorem extendData_label {A : Type*} (f : ActualJointSourceRow s side → A)
    (fallback : JointReconstructionLabel → A) (q : ActualJointSourceRow s side) :
    extendData f fallback q.label = f q := label_injective.extend_apply f fallback q

theorem sum_extendData {M : Type*} [AddCommMonoid M]
    (qs : Finset (ActualJointSourceRow s side)) (f : ActualJointSourceRow s side → M)
    (fallback : JointReconstructionLabel → M) :
    (∑ v ∈ qs.image label, extendData f fallback v) = ∑ q ∈ qs, f q := by
  rw [sum_label_image]
  simp only [extendData_label]

end ActualJointSourceRow
#print axioms ActualJointSourceRow.sum_labels_finiteRows
#print axioms ActualJointSourceRow.sum_extendData
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceFinite -/
