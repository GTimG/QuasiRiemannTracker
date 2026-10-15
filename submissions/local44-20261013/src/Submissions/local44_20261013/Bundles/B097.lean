/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B053
import Submissions.local44_20261013.Bundles.B064
import Submissions.local44_20261013.Bundles.B067
import Submissions.local44_20261013.Bundles.B069
import Submissions.local44_20261013.Bundles.B077
import Submissions.local44_20261013.Bundles.B078
import Submissions.local44_20261013.Bundles.B083
import Submissions.local44_20261013.Bundles.B084
import Submissions.local44_20261013.Bundles.B087
import Submissions.local44_20261013.Bundles.B095
import Submissions.local44_20261013.Bundles.B096
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGaussianSum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockHarmonicMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock

/- BEGIN ORIGINAL MODULE Analytic.JointFirstActualSector ; sha256 0267d8640bccc98bef32abd355e96cd2b3e490711d0a72fbd812b75426c1f581 -/
section



/-! The actual first sector needs only bounded Fourier joint targets.
The literal source coarse sums and lower target exponents are supplied
by the source geometry, before the first Fourier kernel is integrated. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance firstActualSectorDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def firstSourceCoarseConstant (N : ℕ) (F U b₁ b₂ B₁ B₂ D : ℝ) : ℝ :=
  (Fintype.card RayCharacter : ℝ)^2*128*D*(firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2

lemma firstSourceLabels_subset {ι Λ : Type*} [Fintype ι] [DecidableEq Λ]
    (S T : Finset Λ) (q : Λ → FirstJointLabel ι) (h : S ⊆ T) :
    firstSourceLabels S q ⊆ firstSourceLabels T q := by
  intro k hk
  simp only [firstSourceLabels,Finset.mem_sigma,Finset.mem_univ,true_and,and_true] at hk ⊢
  exact h hk

theorem eventually_actual_first_sector_from_local_targets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Wkernel : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay Ncap : ℕ) (ν F U b₁ b₂ B₁ B₂ D B L Cr Amin Amax J : ℝ)
    (hν : 0 < ν) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hD : 0 ≤ D)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) (hJ : 0 ≤ J) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (s : Input ι) (R seed : Ideal O),
    Fintype.card ι ≤ Ncap → (∀ i, s.M i ≤ F) → s.upper ≤ U → s.b₁ ≤ b₁ → s.b₂ ≤ b₂ →
    s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
    0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (M A δ a window Ch : ℝ), Amin ≤ A → A ≤ Amax → 0 < a → 0 ≤ Ch →
    volume s.toData = Z^A →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    let Outer := FirstSourceOuterIndex s R seed (Z^M) radius
    let q := firstSourceOuterLabel s R seed (Z^M) radius
    ∀ (labels : Finset Outer) (ref : Outer) (rows : Finset O) (t : Outer → ℝ)
      (W : Outer → 𝓢(ℝ,ℂ)) (H : Outer → ℝ),
    (∀ z ∈ rows, z ≠ 0) →
    (∀ i, 0 < H i) → (∀ i, H i ≤ Z^J) →
    (∀ i, QuadraticInitialBound.diagonalControl (W i) ≤ D) →
    (∀ i ∈ labels, a*Z^A ≤ ((q i).C.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 2)) →
    (∀ i ∈ labels, a*Z^A ≤ ((q i).D.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 3)) →
    (∀ i ∈ labels, ((q i).C.absNorm : ℝ) ≤ Z^δ*((q ref).C.absNorm : ℝ)) →
    (∀ i ∈ labels, ((q i).D.absNorm : ℝ) ≤ Z^δ*((q ref).D.absNorm : ℝ)) →
    (∀ i ∈ labels, (q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
      (q i).activeWidth Z/2+(q i).punctureWidth Z) →
    (∀ i ∈ labels, ‖V 0 ((q i).sourceRowLog (Z^M) (dyadicScale (i.2.2 0)))‖ ≤ 1) →
    (∀ i ∈ labels, ∀ z ∈ rows, ‖V 1 (Real.log (‖eisEmbedding z‖^2/dyadicScale (i.2.2 1)))‖ ≤ 1) →
    (∀ i ∈ labels, ∀ z : O, 0 ≤ (W i (‖eisEmbedding z‖^2/H i)).re) →
    (∀ i ∈ labels, ∀ z ∈ rows, 1 ≤ (W i (‖eisEmbedding z‖^2/H i)).re) →
    (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).leftEnergy (t k.1+2*Real.pi*(w-θ)) (W k.1) (H k.1)) ≤
        (Z^A/((q ref).C.absNorm : ℝ))*(Ch*Z^((q ref).leftTargetWidth Z A))) →
    (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).rightEnergy (t k.1+2*Real.pi*(w-(-θ))) (W k.1) (H k.1)) ≤
        (Z^A/((q ref).D.absNorm : ℝ))*(Ch*Z^((q ref).rightTargetWidth Z A))) →
    ‖∑ i ∈ labels,
      (((1+dyadicScale (i.2.2 0)*dyadicScale (i.2.2 1)/
        (dyadicScale (i.2.2 2)*dyadicScale (i.2.2 3)))^decay : ℝ) : ℂ)*
      (q i).sourceBlock (t i) rows Wkernel V (Z^M) (dyadicScale (i.2.2 0))
        (dyadicScale (i.2.2 1)) (dyadicScale (i.2.2 2)) (dyadicScale (i.2.2 3))‖/Z^A ≤
      C*(Ch+firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂ D)*(Real.exp window/a)*Z^(M+δ) := by
  obtain ⟨degree,C,hC,hsector⟩ := joint_first_centered_sector_from_local_joint_targets
    (ι := ι) Wkernel V Mwin hMwin hV hV₂c hV₂s hV₃c hV₃s decay ν
    (J+6*B+Amax+2) (Amin-B) hν
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_actual_first_source_coarse_powers Ncap F U b₁ b₂ B₁ B₂ D B L Cr Amax J
    hB₁ hB₂ hD hB hL hCr hJ,eventually_ge_atTop (2:ℝ)] with Z hcoarse hZ₂
  have hZ : 1 < Z := lt_of_lt_of_le (by norm_num) hZ₂
  have hz : 0 < Z := zero_lt_one.trans hZ
  intro s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
    M A δ a window Ch hAmin hAmax ha hCh hvolume radius hr
  dsimp only
  intro labels ref rows t W H hrows hH hHcap hW hl hr' hNC hND hscalarWidth hV₀ hV₁ hpos hmajor hleft hright
  let q := firstSourceOuterLabel s R seed (Z^M) radius
  let Ct := firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂ D
  have hCt : 0 ≤ Ct := by dsimp only [Ct,firstSourceCoarseConstant]; positivity
  have hvolcap : volume s.toData ≤ Z^Amax := by
    rw [hvolume]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hAmax
  have hc := hcoarse ι s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
    hvolcap (Z^M) (by positivity) radius hr W H hH hHcap hW ref.1
  rw [hvolume] at hc
  have hsub := firstSourceLabels_subset labels Finset.univ q (Finset.subset_univ _)
  have hcl : (∑ k ∈ firstSourceLabels labels q,
      ((q k.1).sourceChild k.2).leftCoarse (W k.1) (H k.1)) ≤
      (Z^A/((q ref).C.absNorm : ℝ))*(Ct*Z^(J+6*B+Amax+2)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => CenteredMomentFirstDivisorCommonBound.coarse_nonneg _ _ _ _ _ _)).trans hc.1
  have hcr : (∑ k ∈ firstSourceLabels labels q,
      ((q k.1).sourceChild k.2).rightCoarse (W k.1) (H k.1)) ≤
      (Z^A/((q ref).D.absNorm : ℝ))*(Ct*Z^(J+6*B+Amax+2)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => CenteredMomentFirstDivisorCommonBound.coarse_nonneg _ _ _ _ _ _)).trans hc.2
  have hn := commonLabel_norm_bounds (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) (Z^B)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hsource)
    ref.1.val.1 ref.1.val.2 ref.1.property
  have htarget := (q ref).target_widths_lower Z A Amin B hZ hAmin hn.1 hn.2
  exact hsector labels rows q (q ref) Z M A δ a window Ch Ct hZ ha hCh hCt htarget.1 htarget.2
    t (fun i => dyadicScale (i.2.2 0)) (fun i => dyadicScale (i.2.2 1))
    (fun i => dyadicScale (i.2.2 2)) (fun i => dyadicScale (i.2.2 3)) hrows
    (fun _ => dyadicScale_pos _) (fun _ => dyadicScale_pos _)
    (fun _ => dyadicScale_pos _) (fun _ => dyadicScale_pos _)
    hl hr' hNC hND hscalarWidth hV₀ hV₁ (fun k => W k.1) (fun k => H k.1)
    (fun k _ => hH k.1)
    (fun k hk => hpos k.1 (Finset.mem_sigma.mp hk).1)
    (fun k hk => hmajor k.1 (Finset.mem_sigma.mp hk).1) hleft hright hcl hcr

#print axioms eventually_actual_first_sector_from_local_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstActualSector -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighPhysicalSectors ; sha256 82e29e7e068895bf4501668940b27b038a3eb22dec6363e04fc7c5aa0b117d69 -/
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
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
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

theorem actual_joint_high_physical_sector_contribution
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
    (aSource Mslot upper : ℝ) (haSource : 0 < aSource) (hMslot : 0 ≤ Mslot)
    (conductorReserve : ℝ) (hconductorReserve : 0 < conductorReserve)
    (Sbad : Finset (Ideal O)) (primeLoss : ℝ) (hprimeLoss : 0 < primeLoss)
    (hprimeReserve : primeLoss ≤ 144011/219600000)
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
        (slotWidth : JointReconstructionLabel → Slot → ℝ),
      (∀ v ∈ S, ‖rayWeight v‖ ≤ 1) →
      (∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain) →
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
      ∀ scalarLoss : ℝ,
      (∀ v ∈ S, 0 < K v ∧
        K v ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss))) →
      (∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂cost-b₂+scalarLoss) →
      (∑ v ∈ S, ∑ D ∈ Ds v,
        ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius D : ℂ)*
            ((s v).actualPrecount Z A c (actualHighPrimeCount M H Sbad Z) (K v) (n v) : ℂ)*rayWeight v) *
          ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) ≤
        C*Z^(π+A-c+R₁+E+Bc-144011/219600000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_kernel_uniform η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      aSource Mslot upper haSource hMslot conductorReserve hconductorReserve Wkernel decay tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh,eventually_actual_high_prime_ratio M H hH Sbad primeLoss hprimeLoss]
    with Z hZ hprime
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius tbase firstU firstTheta n rayWeight
    σ freq θ slotWidth hray hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    first hz hfirst hpuncture hwsource Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
  have hh := hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius tbase firstU firstTheta n rayWeight
    σ freq θ slotWidth hray hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    first hz hfirst hpuncture hwsource Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  apply (joint_actual_precount_norm_sum_sector S s Ds t K Radius n z rayWeight Wkernel decay
    Z A c d₁ R₁ E omegaLoss g₂ t₂cost b₂ scalarLoss (actualHighPrimeCount M H Sbad Z)
    hZ.1 hprime.2.1 hKactual hcost).trans
  calc
    _ ≤ (Z^(3/500 : ℝ)/actualHighPrimeCount M H Sbad Z)*
        (C*Z^(π+A-c+R₁+E+Bc-144011/109800000)) :=
      mul_le_mul_of_nonneg_left hh (div_nonneg (Real.rpow_nonneg hZpos.le _) hprime.2.1.le)
    _ ≤ Z^primeLoss*(C*Z^(π+A-c+R₁+E+Bc-144011/109800000)) :=
      mul_le_mul_of_nonneg_right hprime.2.2 (by positivity)
    _ = C*Z^(π+A-c+R₁+E+Bc-144011/109800000+primeLoss) := by
      rw [Real.rpow_add hZpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)) hC.le

end FixedData
#print axioms actual_joint_high_physical_sector_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPhysicalSectors -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowNormalization ; sha256 29fb508f94309d64bd4615e1696de0c6f7288fde1eb70c2aa34cf915d5cbe102 -/
section



/-! The physical lower column dyads cancel the two cumulative source
normalizers. With the minimum low allowance, the remaining second
common weight is the genuine harmonic pair weight. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSecondBlockHarmonicMass
local notation "O" => HeckeFamily.O

lemma low_pair_source_normalization (V HL HR NL NR P E a : ℝ)
    (hV : 0 < V) (hHL : 0 < HL) (hHR : 0 < HR) (hNL : 0 < NL) (hNR : 0 < NR)
    (hP : 0 < P) (hE : 0 ≤ E) (ha : 0 < a)
    (hL : a*V/NL ≤ HL) (hR : a*V/NR ≤ HR) :
    (V/Real.sqrt (HL*HR))*(Real.sqrt (E/(NL*P))*Real.sqrt (E/(NR*P))) ≤ E/(a*P) := by
  have hmul := mul_le_mul ((div_le_iff₀ hNL).mp hL) ((div_le_iff₀ hNR).mp hR)
    (mul_nonneg ha.le hV.le) (mul_nonneg hHL.le hNL.le)
  have hs : (a*V)^2 ≤ (HL*HR)*(NL*NR) := by nlinarith [hmul]
  have hden : a*V ≤ Real.sqrt (HL*HR)*Real.sqrt (NL*NR) := by
    have hh := Real.sqrt_le_sqrt hs
    rw [Real.sqrt_sq (mul_nonneg ha.le hV.le),Real.sqrt_mul (mul_nonneg hHL.le hHR.le)] at hh
    exact hh
  have hdpos : 0 < Real.sqrt (HL*HR)*Real.sqrt (NL*NR) := by positivity
  have hv : V/(Real.sqrt (HL*HR)*Real.sqrt (NL*NR)) ≤ 1/a := by
    apply (div_le_div_iff₀ hdpos ha).mpr
    simpa only [one_mul,mul_comm V a] using hden
  have hp : Real.sqrt (E/(NL*P))*Real.sqrt (E/(NR*P)) = E/(Real.sqrt (NL*NR)*P) := by
    rw [←Real.sqrt_mul (div_nonneg hE (mul_pos hNL hP).le)]
    rw [show E/(NL*P)*(E/(NR*P))=E^2/((NL*NR)*P^2) by ring]
    rw [Real.sqrt_div (sq_nonneg E),Real.sqrt_sq hE,
      Real.sqrt_mul (mul_nonneg hNL.le hNR.le),Real.sqrt_sq hP.le]
  rw [hp]
  calc
    _ = (V/(Real.sqrt (HL*HR)*Real.sqrt (NL*NR)))*(E/P) := by ring
    _ ≤ (1/a)*(E/P) := mul_le_mul_of_nonneg_right hv (div_nonneg hE hP.le)
    _ = _ := by ring

lemma low_precount_nominal_identity (A c d R e M a omega g₂ t₂ b₂ δ saving : ℝ) :
    (A-min c d+R+e-M+5*a+g₂-t₂-b₂+omega)+
      (δ+jointLowNominal M c d a omega g₂ t₂+a-saving) =
      A-c+R+e+δ-saving-b₂ := by
  have hm : min c d+max (c-d) 0 = c := by
    by_cases h : c ≤ d
    · rw [min_eq_left h,max_eq_right (sub_nonpos.mpr h)]; ring
    · have hd : d ≤ c := le_of_not_ge h
      rw [min_eq_right hd,max_eq_left (sub_nonneg.mpr hd)]; ring
  unfold jointLowNominal
  linarith

lemma pairWeight_eq_power (C D : Ideal O) (hC : C ≠ 0) (hD : D ≠ 0)
    (Z : ℝ) (hZ : 1 < Z) :
    pairWeight C D = Z^(-((Real.logb Z (C.absNorm : ℝ)+Real.logb Z (D.absNorm : ℝ))/2)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hc : 0 < (C.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hd : 0 < (D.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hc' := Real.rpow_logb hZ0 (ne_of_gt hZ) hc
  have hd' := Real.rpow_logb hZ0 (ne_of_gt hZ) hd
  unfold pairWeight
  rw [Real.rpow_neg hZ0.le,one_div]
  congr 1
  rw [div_eq_mul_inv,Real.rpow_mul hZ0.le,←one_div (2 : ℝ),←Real.sqrt_eq_rpow,Real.rpow_add hZ0,hc',hd']

/-- The actual physical normalization leaves precisely the summable
common-pair harmonic factor, with no slot or row population spent. -/
theorem low_physical_normalized_pair (C D : Ideal O) (hC : C ≠ 0) (hD : D ≠ 0)
    (Z A c d R e M a omega g₂ t₂ δ saving V HL HR NL NR P E aSource : ℝ)
    (hZ : 1 < Z) (hV : 0 < V) (hHL : 0 < HL) (hHR : 0 < HR)
    (hNL : 0 < NL) (hNR : 0 < NR) (hP : 0 < P) (hE : 0 ≤ E) (haSource : 0 < aSource)
    (hL : aSource*V/NL ≤ HL) (hR : aSource*V/NR ≤ HR) :
    let b₂ := (Real.logb Z (C.absNorm : ℝ)+Real.logb Z (D.absNorm : ℝ))/2
    Z^(A-min c d+R+e-M+5*a+g₂-t₂-b₂+omega)*
      ((V/Real.sqrt (HL*HR))*(Real.sqrt (E/(NL*P))*Real.sqrt (E/(NR*P))) *
        Z^(δ+jointLowNominal M c d a omega g₂ t₂+a-saving)) ≤
      (E/(aSource*P))*pairWeight C D*Z^(A-c+R+e+δ-saving) := by
  intro b₂
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (low_pair_source_normalization V HL HR NL NR P E aSource hV hHL hHR hNL hNR hP hE haSource hL hR)
      (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _)).trans_eq
  rw [pairWeight_eq_power C D hC hD Z hZ]
  calc
    _ = (E/(aSource*P))*Z^((A-min c d+R+e-M+5*a+g₂-t₂-b₂+omega)+
        (δ+jointLowNominal M c d a omega g₂ t₂+a-saving)) := by
      conv_rhs => rw [Real.rpow_add hZ0]
      ring
    _ = (E/(aSource*P))*Z^(A-c+R+e+δ-saving-b₂) := by rw [low_precount_nominal_identity]
    _ = _ := by rw [sub_eq_add_neg,Real.rpow_add hZ0]; ring

#print axioms low_pair_source_normalization
#print axioms low_physical_normalized_pair
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowNormalization -/

/- BEGIN ORIGINAL MODULE Analytic.JointSelectedSourceData ; sha256 81975e38bb3f44dfe750d06bf1ccec97861b4f6c9647b3c48c272ed149107d22 -/
section


/-! Numerical data selected on a finite source subset extends to the global
joint-label functions without imposing any condition outside the subset. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.Local44.Analytic
open CenteredMomentFirstAmplificationChoice

namespace NonzeroJointSourceRow
variable {Slot : Type*} [Fintype Slot] {s : OriginalData Slot} {side : Bool}

theorem finiteLabel_injective (S : Finset (NonzeroJointSourceRow s side)) :
    Function.Injective (fun a : S => a.val.label) := by
  intro a b h
  exact Subtype.ext (label_injective h)

def extendFiniteData {A : Type*} [Inhabited A]
    (S : Finset (NonzeroJointSourceRow s side)) (f : S → A) : JointReconstructionLabel → A :=
  Function.extend (fun a : S => a.val.label) f (fun _ => default)

@[simp] theorem extendFiniteData_apply {A : Type*} [Inhabited A]
    (S : Finset (NonzeroJointSourceRow s side)) (f : S → A) (a : S) :
    extendFiniteData S f a.val.label = f a := (finiteLabel_injective S).extend_apply f _ a

theorem extendFiniteData_of_mem {A : Type*} [Inhabited A]
    (S : Finset (NonzeroJointSourceRow s side)) (q : NonzeroJointSourceRow s side)
    (hq : q ∈ S) (f : S → A) :
    extendFiniteData S f q.label = f ⟨q,hq⟩ := extendFiniteData_apply S f ⟨q,hq⟩

end NonzeroJointSourceRow
#print axioms NonzeroJointSourceRow.extendFiniteData_apply
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSelectedSourceData -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceLiveRows ; sha256 a89c3a8247e0a5e6a174cad2d3588bb9ab13c6763a5e3565d6a1eb7a3539b97f -/
section



/-! The actual retained frequency domain enters the source embedding with
its literal nonzero support and exact finite-sum multiplicity. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentFirstAmplificationChoice CenteredMomentCanonicalFirst
open CenteredMomentSecondBlockAggregate CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondLiveBlock
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]

namespace ActualJointSourceRow
variable {s : OriginalData Slot} {side : Bool}

def nonzeroRows (qs : Finset (ActualJointSourceRow s side))
    (hz : ∀ q ∈ qs, q.z ≠ 0) : Finset (NonzeroJointSourceRow s side) :=
  qs.attach.image fun q => ⟨q.val,hz q.val q.property⟩

theorem sum_nonzeroRows {M : Type*} [AddCommMonoid M]
    (qs : Finset (ActualJointSourceRow s side)) (hz : ∀ q ∈ qs, q.z ≠ 0)
    (f : ActualJointSourceRow s side → M) :
    (∑ q ∈ nonzeroRows qs hz, f q.val) = ∑ q ∈ qs, f q := by
  unfold nonzeroRows
  rw [Finset.sum_image]
  · exact Finset.sum_attach _ _
  · intro q hq r hr he
    exact Subtype.ext (congrArg (fun x : NonzeroJointSourceRow s side => x.val) he)

theorem nonzeroRows_label_image
    (qs : Finset (ActualJointSourceRow s side)) (hz : ∀ q ∈ qs, q.z ≠ 0) :
    (nonzeroRows qs hz).image NonzeroJointSourceRow.label = qs.image label := by
  ext v
  constructor
  · intro hv
    obtain ⟨q,hq,hv⟩ := Finset.mem_image.mp hv
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hq
    subst q
    exact Finset.mem_image.mpr ⟨r.val,r.property,hv⟩
  · intro hv
    obtain ⟨q,hq,hv⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨⟨q,hz q hq⟩,?_,hv⟩
    exact Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_attach _ _,rfl⟩

theorem finiteRows_nonzero
    (Es : (p : FirstIndex s) → Finset (Finset (CommonIndex p.val.1 p.val.2)))
    (Ls : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) → Finset (Ideal O))
    (rows : (p : FirstIndex s) → Finset (CommonIndex p.val.1 p.val.2) →
      (L : Ideal O) → (r : SecondIndex s side p L) →
      Finset (CommonIndex r.val.1 r.val.2) → Finset O)
    (hrows : ∀ p E L r U z, z ∈ rows p E L r U → z ≠ 0) :
    ∀ q ∈ finiteRows s side Es Ls rows, q.z ≠ 0 := by
  intro q hq
  exact hrows q.first q.E q.L q.second q.U q.z ((mem_finiteRows s side Es Ls rows q).mp hq).2.2

/-- Includes both the exact canonical partition and nonzero disk weight. -/
def liveFrequencyRows (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) : Finset O :=
  liveRows C D U R
    (CenteredMomentSecondRetainedRows.retainedRows R
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))

theorem liveFrequencyRows_nonzero (C D : Ideal O) (U : Finset (CommonIndex C D))
    (R : ℝ) (z : O) (hz : z ∈ liveFrequencyRows C D U R) : z ≠ 0 := by
  apply retainedRows_ne_zero R (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z
  exact (Finset.mem_filter.mp hz).1

end ActualJointSourceRow
#print axioms ActualJointSourceRow.sum_nonzeroRows
#print axioms ActualJointSourceRow.liveFrequencyRows_nonzero
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceLiveRows -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowGaussianSum ; sha256 c61b61ff00d132e2f844e090f22a7ecb900c628127343eb4ef01b4133798e5ff -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGaussianSum.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_dyad_norm_split (f : ℕ→ℂ) (p : ℕ→Prop) [DecidablePred p]
    (hc : Summable (fun j=> if p j then 0 else ‖f j‖))
    (hr : Summable (fun j=> if p j then ‖f j‖ else 0)) :
    Summable f ∧ ‖∑'j,f j‖≤(∑'j,if p j then 0 else ‖f j‖)+(∑'j,if p j then ‖f j‖ else 0) := by
  have he (j : ℕ) : ‖f j‖=(if p j then 0 else ‖f j‖)+(if p j then ‖f j‖ else 0) := by
    split_ifs <;> ring
  have hn : Summable (fun j=>‖f j‖) := (hc.add hr).congr (fun j=>(he j).symm)
  refine ⟨hn.of_norm,?_⟩
  apply (norm_tsum_le_tsum_norm hn).trans_eq
  exact (tsum_congr he).trans (hc.tsum_add hr)

theorem low_all_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤ C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε) := by
  obtain ⟨Cc,hCc,hcentral⟩ := low_central_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr,hCr,hremote⟩ := low_remote_gaussian_dyads S hS ell hell hsum b ε hε V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc+Cr,add_pos hCc hCr,?_⟩
  filter_upwards [hcentral,hremote] with Z hc hr
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j=> lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j)) hc'.1 hr'.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : Z^(-1:ℝ)≤ Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε) := Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith [Submission20261012.Global.LowGeometry.signal_pos])
  calc
    _≤ Cc*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε)+Cr*Z^(-1:ℝ) := add_le_add hc'.2 hr'.2
    _≤ Cc*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε)+Cr*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _=_ := by ring

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowGaussianSum -/
