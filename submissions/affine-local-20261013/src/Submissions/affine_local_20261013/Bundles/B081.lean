/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B047
import Submissions.affine_local_20261013.Bundles.B062
import Submissions.affine_local_20261013.Bundles.B075
import Submissions.affine_local_20261013.Bundles.B079
import Submissions.affine_local_20261013.Bundles.B080
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowCompletedRows

/- BEGIN ORIGINAL MODULE Analytic.JointLowFromParent ; sha256 8abcd78b4679835466393906913576bfb7f0cf0670a06397f565101a4a483862 -/
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
open CenteredMomentEnergyCanonicalLiveBound
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
local instance lowFromParentFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α]

theorem actual_allocated_low_from_parent
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
      ∀ A Mparent nominal pad g allowance geometryLoss clip : ℝ,
      A+(7/2)*(∑ i : CenteredMomentCommonProfile.liveIndices B.val,w i.val) ≤ Mparent →
      Real.logb Z (X₁*X₂*∏ i : CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-nominal ≤
        A-Mparent+6*(3/500)+g+geometryLoss →
      0 ≤ pad → s.width ≤ nominal+pad → 0 ≤ g → g ≤ 37/10000 →
      3/500 ≤ allowance → 0 ≤ geometryLoss → 0 ≤ clip →
      Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      pad+loss+(67/450)*(geometryLoss+2*clip) ≤ 401/9000000 →
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
    A Mparent nominal pad g allowance geometryLoss clip hparent hshift
    hpad hwidth hg hgcap hallowance hgeometry hclip hclipCost hbudgetLoss data
  let V₁ := sourcePlain a b ha (p.profile 0) (p.support 0)
  let V₂ := sourcePlain a b ha (p.profile 1) (p.support 1)
  let rad := restrictedLowRadial s.radial low
  have hdiag := diagonalControl_nonneg s.radial.profile
  by_cases hlive : LiveChild s.character rad D alloc V₁ V₂
      data.slots data.coefficient data.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J
  · have hb := hmain.2 θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq
      s hQ hunit hs low abin k habin habinTop hbase hT hlow hfreqGate hheightSource
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ src hmatch C R B D alloc J F₁ F₂ hF₁ hF₂
    have hgeometryCost := live_source_low_nominal_cost src C R B D alloc J s.character rad V₁ V₂
      v Z X₁ X₂ A Mparent nominal s.width pad g geometryLoss clip w hX₁ hX₂ F₁ F₂
      hmain.1 hw hmatch.scale hF₁ hF₂ hparent hshift hwidth hpad hg hgeometry hclip hclipCost hlive
    have hreserve := live_source_low_reserve nominal pad g geometryLoss clip loss allowance
      hgcap hallowance hbudgetLoss
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hmain.1.le (by linarith)) (by positivity))
  · have hz := energy_zero_of_not_live s.character rad (fun z hz => s.row_ne_zero z hz.1)
      D alloc V₁ V₂ data.slots data.coefficient data.P data.P_pos
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂ hlive
    change allocatedEnergy s.character rad D alloc V₁ V₂ data.slots data.coefficient data.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤ _
    rw [hz]
    have hZpos : 0 < Z := zero_lt_one.trans hmain.1
    positivity

#print axioms actual_allocated_low_from_parent
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowFromParent -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSupported ; sha256 50662ce6bd17b63c9be2edec3915aee08284524c86269288bf170f1bf99c518f -/
section



/-! Restricting a natural state to the support of its existing radial
profile leaves every weighted child energy unchanged. On this support the
literal presentation-conductor gate follows from the state width. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentNaturalRowSource HeckePrimeRay
open HeckeDetectorZeros CenteredMomentNaturalFixedRaySource CenteredExceptionalProfile
open HeckeInverseAmplification CenteredMomentSecondHeightFamily ProbeHighRowFamily
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

def supportedNaturalState {Z Bmask radial : ℝ}
    (s : NaturalState Z Bmask radial) : NaturalState Z Bmask radial :=
  {s with
    radial := {s.radial with
      keep := fun z => s.radial.keep z ∧
        s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0}
    row_ne_zero := fun z hz => s.row_ne_zero z hz.1
    nonexceptional := fun z hz => s.nonexceptional z hz.1}

lemma supportedNaturalState_weight {Z Bmask radial : ℝ}
    (s : NaturalState Z Bmask radial) (low : O → Prop) (z : O) :
    (restrictedLowRadial (supportedNaturalState s).radial low).weight z =
      (restrictedLowRadial s.radial low).weight z := by
  by_cases hk : s.radial.keep z
  · by_cases hl : low z
    · by_cases hp : s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) = 0
      · simp [Radial.weight, restrictedLowRadial, supportedNaturalState, hk, hl, hp]
      · simp [Radial.weight, restrictedLowRadial, supportedNaturalState, hk, hl, hp]
    · simp [Radial.weight, restrictedLowRadial, supportedNaturalState, hk, hl]
  · simp [Radial.weight, restrictedLowRadial, supportedNaturalState, hk]

lemma supportedNaturalState_childEnergy {Z Bmask radial : ℝ}
    (s : NaturalState Z Bmask radial) (low : O → Prop)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : CenteredMomentEligibleEnergy.Data ι) (D : Ideal O)
    (alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    childEnergy data (restrictedLowRadial (supportedNaturalState s).radial low) D alloc =
      childEnergy data (restrictedLowRadial s.radial low) D alloc := by
  unfold childEnergy
  apply tsum_congr
  intro z
  rw [supportedNaturalState_weight]

lemma supportedNaturalState_row_norm {Z Bmask radial : ℝ}
    (s : NaturalState Z Bmask radial) (z : O)
    (hz : (supportedNaturalState s).radial.keep z) :
    ((Ideal.span {z}).absNorm : ℝ) ≤ radial*Z^s.rowWidth := by
  have hp := s.radial_support hz.2
  change ‖eisEmbedding z‖^2/s.radial.scale ≤ radial at hp
  have hh := (div_le_iff₀ s.radial.scale_pos).mp hp
  rwa [eisEmbedding_norm_sq_eq_absNorm_span,s.scale_eq] at hh

variable (M : Ideal O) [NeZero M]
local instance lowSupportedFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The threshold precedes every live natural state, row, width and ray
label. No separate conductor hypothesis remains on the supported rows. -/
theorem eventually_supported_relative_conductor
    (η₀ : Character) (radial ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (Bmask d : ℝ) (s : NaturalState Z Bmask radial),
      s.width+Bmask+ξ ≤ d →
      ∀ (z : O) (hz : (supportedNaturalState s).radial.keep z),
      ∀ θ : RayQuotient.Characters M H,
        ((twistedFamily M H hH ((excluded
          (naturalRow s.character z (s.row_ne_zero z hz.1)).character s.puncture).product
          η₀.inverse) θ).modulus.absNorm : ℝ) ≤ Z^d := by
  filter_upwards [eventually_natural_relative_conductor M H hH η₀ (ξ/2) (by linarith),
    (tendsto_rpow_atTop (show 0 < ξ/2 by linarith)).eventually (eventually_ge_atTop radial)]
    with Z hcond hrad
  refine ⟨hcond.1,?_⟩
  intro Bmask d s hd z hz θ
  have hZ : 0 < Z := zero_lt_one.trans hcond.1
  have hrow : ((Ideal.span {z}).absNorm : ℝ) ≤ Z^(s.rowWidth+ξ/2) := by
    apply (supportedNaturalState_row_norm s z hz).trans
    rw [Real.rpow_add hZ]
    calc
      radial*Z^s.rowWidth ≤ Z^(ξ/2)*Z^s.rowWidth :=
        mul_le_mul_of_nonneg_right hrad (Real.rpow_nonneg hZ.le _)
      _ = _ := mul_comm _ _
  exact hcond.2 s.characterWidth (s.rowWidth+ξ/2) Bmask d
    (by dsimp [NaturalState.width] at hd; linarith)
    s.character z (naturalRow s.character z (s.row_ne_zero z hz.1)) s.puncture
    s.puncture_ne_zero s.modulus_bound hrow s.radical_bound θ

/-- The common dictionary upper edge implies the low gate on precisely the
rows used by the weighted energy. The conductor condition is proved from
the natural-state width, with one threshold before every source label. -/
theorem eventually_supported_low_gate
    (η₀ : Character) (radial ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (Bmask d : ℝ) (s : NaturalState Z Bmask radial),
      s.width+Bmask+ξ ≤ d →
      ∀ (η : Character) (Q : Ideal O) (hQM : Q ≤ M)
        (hQ : s.fixedModulus = internalQ Q η₀)
        (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}),
      ∀ (w : NonzeroElement)
        (hex : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 w.val),
      ∀ (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
        (R : Ideal O), R ≠ 0 →
      ∀ (z : O) (hz : (supportedNaturalState s).radial.keep z),
      (∀ I : Ideal O,
        idealCoeff (excluded (naturalRow s.character z (s.row_ne_zero z hz.1)).character s.puncture) I =
          idealCoeff (excluded N.character R) I) →
      ∀ (τ e a : ℝ) (k : ℕ),
      zeroMaximum
          (fun label => (momentData (jointRelativeParent η
            (relativeSlotTranslate M H hH (fun _ : Unit => η₀)) label)).character w)
          (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH (fun _ : Unit => η₀))
            (internalQ Q η₀) hQ72
            (relativeSlotTranslate_fixedQ M H hH (fun _ : Unit => η₀) (internalQ Q η₀)
              (inf_le_left.trans hQM) (fun _ => inf_le_right)) w hex)
          (3*(k+1 : ℕ)*Z^τ) < a+2*e →
      NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM hQ d τ e a k z hz := by
  filter_upwards [eventually_supported_relative_conductor M H hH η₀ radial ξ hξ]
    with Z hcond
  refine ⟨hcond.1,?_⟩
  intro Bmask d s hd η Q hQM hQ hQ72 w hex parent N R hR z hz hcoeff τ e a k hupper
  exact naturalLowGate_of_joint_maximum M H hH (supportedNaturalState s) η η₀ Q hQM hQ
    hQ72 w hex parent N R hR z hz hcoeff d τ e a k hupper
    (hcond.2 Bmask d s hd z hz)

#print axioms supportedNaturalState_childEnergy
#print axioms eventually_supported_relative_conductor
#print axioms eventually_supported_low_gate
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSupported -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondKernelCutoff ; sha256 807d8586bb3f7ed7fcf97df74b3a698b33eca3c4591f14bd0287ebffcd5ada95 -/
section



/-! The bounded Fourier region and the genuine coarse source estimate
feed the actual second-kernel integral without separating first labels. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentLogDyadic RayFourExpansion CenteredMomentFixedRay
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem retainedPair_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : CommonSecondKernelLabel ι) (t₁ t₂ : ℝ) (z : O) (H₁ H₂ : ℝ) :
    0 ≤ s.retainedPair t₁ t₂ z H₁ H₂ := by
  unfold CommonSecondKernelLabel.retainedPair secondRetainedPairBound
  positivity

theorem actual_second_phase_coefficient_le_one (D E : O) (χ ξ : RayCharacter) :
    ‖pairCoeff (phaseTable D E) χ ξ‖ ≤ 1 :=
  pairCoeff_norm_le _ 1 (fun r s => phaseTable_norm D E r s) χ ξ

def secondProjectedJointRetained {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
    (t : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (scale θ u v : ℝ) : ℝ :=
  scale*∑ k ∈ labels, ∑ L ∈ Ds k, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
    ((s k).withProjector L).retainedPair
      (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
      (dyadicScale (n k 2)) (dyadicScale (n k 3))

/-- All three Fourier variables share one joint arithmetic sum. The
global fallback is used only to choose a fixed polynomial degree outside
the bounded region; the actual kernel theorem pays its moments. -/
theorem joint_second_projector_kernel_from_cutoff
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ) (ν B target : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι]
        (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
        (t K R : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (weight : α → ℂ),
      (∀ k ∈ labels, ‖weight k‖ ≤ 1) → ∀ Z scale Ch Ct : ℝ,
      1 ≤ Z → 0 ≤ scale → 0 ≤ Ch → 0 ≤ Ct →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν →
        secondProjectedJointRetained labels s Ds t n z scale θ u v ≤ Ch*Z^target) →
      (∀ θ u v : ℝ,
        secondProjectedJointRetained labels s Ds t n z scale θ u v ≤ Ct*Z^B) →
      (∑ k ∈ labels, ∑ L ∈ Ds k,
        ‖(((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius L : ℂ)*((scale : ℂ)*weight k)) *
            ((s k).withProjector L).toKernelLabel.kernelRow
              (t k) (z k) W (K k) (R k) (n k)‖) ≤ C*((Ch+Ct)*Z^target) := by
  obtain ⟨N,hpoly⟩ := three_variable_polynomial_extension ν B target hν
  obtain ⟨C,hC,hkernel⟩ := joint_second_kernel_norm_sum_from_moebius_retained W decay N N N
  refine ⟨N,C,hC,?_⟩
  intro ι α instι instDι labels s Ds t K R n z weight hweight Z scale Ch Ct hZ hscale hCh hCt hlocal hcoarse
  have hglobal := hpoly Z Ch Ct hZ hCh hCt
    (secondProjectedJointRetained labels s Ds t n z scale) hlocal hcoarse
  have hpoint (θ u v : ℝ) :
      (∑ q ∈ labels.sigma Ds,
        ‖(UniqueFactorizationMonoid.moebius q.2 : ℂ)*((scale : ℂ)*weight q.1)‖ *
          ((s q.1).withProjector q.2).retainedPair
            (t q.1+2*Real.pi*(u-θ)) (t q.1+2*Real.pi*(v-(-θ))) (z q.1)
            (dyadicScale (n q.1 2)) (dyadicScale (n q.1 3))) ≤
        (((Ch+Ct)*Z^target)*(1+‖θ‖)^N)*(1+‖u‖)^N*(1+‖v‖)^N := by
    apply le_trans ?_ (hglobal θ u v)
    unfold secondProjectedJointRetained
    simp only [Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum
    intro L hL
    have hr := retainedPair_nonneg ((s k).withProjector L)
      (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
      (dyadicScale (n k 2)) (dyadicScale (n k 3))
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hscale]
    calc
      _ = (scale*‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*
          ((s k).withProjector L).retainedPair
            (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
            (dyadicScale (n k 2)) (dyadicScale (n k 3)))*‖weight k‖ := by ring
      _ ≤ (scale*‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*
          ((s k).withProjector L).retainedPair
            (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
            (dyadicScale (n k 2)) (dyadicScale (n k 3)))*1 :=
        mul_le_mul_of_nonneg_left (hweight k hk) (by positivity)
      _ = _ := by ring
  have hh := hkernel (labels.sigma Ds) (fun q => (s q.1).withProjector q.2)
    (fun q => t q.1) (fun q => K q.1) (fun q => R q.1) (fun q => n q.1) (fun q => z q.1)
    (fun q => (scale : ℂ)*weight q.1) ((Ch+Ct)*Z^target) hpoint
  simpa only [Finset.sum_sigma,CommonSecondKernelLabel.withProjector] using hh

#print axioms joint_second_projector_kernel_from_cutoff
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondKernelCutoff -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.RetainedFixed ; sha256 a1b0113420a0c6626dd430777a8e6228406b5f078d6341d0e4ef39bec41f13f6 -/
section


namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 800000

lemma eventually_retained_log_cost (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠU:ℝ in atTop, 1 < U ∧ ∀n:ℝ, 0 ≤ n → n ≤ 2 →
      (1+2*(n*Real.log U))^2 ≤ 25*U^(loss/2) := by
  have hlog := (isLittleO_log_rpow_atTop (by linarith:0 < loss/4)).bound (by norm_num:(0:ℝ)<1)
  filter_upwards [hlog,eventually_gt_atTop (1:ℝ)] with U hlog hU
  have hUpos := zero_lt_one.trans hU
  have hlog0 := (Real.log_pos hU).le
  have hh : Real.log U ≤ U^(loss/4) := by
    simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hUpos.le _)] using hlog
  refine ⟨hU,?_⟩
  intro n hn hn2
  have hpow : 1 ≤ U^(loss/4) := Real.one_le_rpow hU.le (by linarith)
  have hbase : 1+2*(n*Real.log U) ≤ 5*U^(loss/4) := by
    have hm := mul_le_mul_of_nonneg_right hn2 hlog0
    nlinarith
  have hnonneg : 0 ≤ 1+2*(n*Real.log U) := by positivity
  calc
    _ ≤ (5*U^(loss/4))^2 := pow_le_pow_left₀ hnonneg hbase 2
    _ = _ := by
      rw [mul_pow,←Real.rpow_natCast (U^(loss/4)) 2,←Real.rpow_mul hUpos.le]
      norm_num
      congr 1
      ring

/-- Fixed source profile version with all restoration and logarithmic losses
absorbed into any prescribed positive exponent loss. The constant is independent
of rowwise coefficient choices and all amplitude/count constants. -/
theorem certified_retained_fixed_profile {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (G:𝓢(ℝ,ℂ)) (loss Cscale Ccond xi:ℝ)
    (hloss:0 < loss) (hCscale:0 < Cscale) (hCcond:0 < Ccond) (hxi:0 < xi) :
    ∃degree:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (X:rows→ℝ) (m:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 →
      (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      (2*(m+xi)+6*κ*(∑i,width i) ≤ 1 ∨ T=∅) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) G (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,H,Cr,hCr,hr⟩ := certified_actual_retained_fourth F κ hκlo hκhi hbeta hκbeta (loss/2) Cscale xi
    (by linarith) hCscale hxi
  let B := 1+H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G
  let K := max 1 Ccond
  have hB : 0 < B := by have := apply_nonneg (H.sup (schwartzSeminormFamily ℝ ℝ ℂ)) G; dsimp [B]; linarith
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨degree,25*Cr*K^(loss/2)*B^4,by positivity,?_⟩
  filter_upwards [hr,eventually_retained_log_cost loss hloss] with U hr hl
  have hU := hr.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ X m he hX hm hmmax hred hcombined T width z height
    hw hwmax hreal hh him hcapacity
  have hRcap : 1 ≤ K*U := by nlinarith
  have hred' (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ K*U :=
    (hred i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hUp.le)
  have hGB (i:rows) : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ B := by dsimp [B]; linarith
  have hb := hr.2 rows hrows τ ψ (fun _=> G) X m B (K*U) he hX hm hmmax hB hGB
    hRcap hred' hcombined T width z height hw hwmax hreal hh him hcapacity
  have hlog := hl.2 (m+xi) (by linarith) hmmax
  apply hb.trans
  calc
    _ ≤ Cr*(K*U)^(loss/2)*B^4*(25*U^(loss/2))*(1+height)^degree*U^(1+D.t) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hKpos.le hUp.le]
      calc
        _ = (25*Cr*K^(loss/2)*B^4)*(1+height)^degree*
            (U^(loss/2)*U^(loss/2)*U^(1+D.t)) := by ring
        _ = _ := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]; congr 2; ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.RetainedFixed -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowCompletedRows ; sha256 43f5d20c4d9090bab3f424e4ee35d92d473c77bbe0f23767c98bc285de0e0639 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowCompletedRows.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_completed_rows_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤ Z → 0≤ d → d≤ Submission20261012.Global.ell → 0≤ ell0 → ell0≤ Submission20261012.Global.ell-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+507*η) := by
  have hsubmissionEll := Submission20261012.Global.ell_interval
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_completed_fiber_energy Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  obtain ⟨D,hD,ha⟩ := completed_representative_aggregation 2 η (by norm_num) hη
  let mask := Ideal.span {m}*F
  let Z₁ := max Z₀ (max 2 (max Ck (Ideal.absNorm mask:ℝ)))
  refine ⟨degree,D*C,Z₁,mul_pos hD hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  have hZZ : Z₀≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 2≤ Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0< Z := by linarith
  have hz1 : 1≤ Z := by linarith
  have hCkZ : Ck≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskZ : (Ideal.absNorm mask:ℝ)≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskn : (Ideal.absNorm mask:ℝ)≤ Z^(2:ℝ) := hmaskZ.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hz1 (show (1:ℝ)≤2 by norm_num))
  have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Z^(2:ℝ) := by
    intro I hI
    refine ⟨(hparents I hI).1,(hparents I hI).2.trans ?_⟩
    calc
      _ ≤ Z*Z^((1-Submission20261012.Global.ell)-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+((1-Submission20261012.Global.ell)-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hh := ha Z hZ2 parents mask hparentn
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hmaskn
    (C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+506*η))
    (fun I => ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
    (by positivity) (fun J hJ => he (σ:=σ) J (hparents J hJ).1 Z d ell0 shift
      hZZ hd hd1 hell hellcap hshift (hparents J hJ).2
      parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod
      Ψ hΨnorm hΨperiod u θ w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+‖θ‖)^degree*(Z^η*Z^(((1-Submission20261012.Global.ell)-d)+506*η)) := by ring
    _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowCompletedRows -/

/- BEGIN ORIGINAL MODULE Analytic.ActualExtractedErrorCapsFull ; sha256 7c9ac5a5f4bc3b8c92a07cedffe7eac4e430adfc0e18cd01db14c19782c785c0 -/
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
local instance actualExtractedErrorCapsDecEqFull {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualExtractedErrorCapsFiniteFull : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_firstExtractedErrors_power_from_caps_full
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
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost)
    (Avol Dscale Pmask qmoving εgeo : ℝ) (hεgeo : 0 < εgeo)
    (hbudget : CenteredMomentFirstSecondInputGates.exponent Avol Dscale Pmask qmoving εgeo ξ ≤ Bcap):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀θ:α→RayQuotient.Characters M H,
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀ prime : O, Prime (Ideal.span {prime}) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀ family : Fin 3 → RayCharacter → Character,
    (∀ i χ, (family i χ).modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    (∀ i χ, ((family i χ).modulus.absNorm:ℝ)≤
      cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (errorIndex i+1))) →
    let radius := fun i : Fin 3 => errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (errorIndex i+1)
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol →
    (R0.absNorm : ℝ)≤ Z^Pmask → R0≠0 →
    (∀ i, (radius i)⁻¹≤ Z^Dscale) →
    (∀ i χ, ((family i χ).modulus.absNorm : ℝ)≤ Z^qmoving) →
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
    ∀r : Fin 3 → RayCharacter → ℝ,
    (∀ (i : Fin 3) (χ : RayCharacter)
      (Bp : actualAllocations (activeInput (child src C R0 B τ t)).pools
        ((Ideal.span {prime})^(errorIndex i+1))),
      let input := errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t
      Z^(r i χ) ≤ input.X₁ ∧ Z^(r i χ) ≤ input.X₂ ∧ Z^(r i χ) ≤ input.Y₁ ∧ Z^(r i χ) ≤ input.Y₂) →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    firstExtractedErrors (child src C R0 B τ t) (R0*C) seed Z
      (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime family ≤
      mass (child src C R0 B τ t)^2*
        ∑i : Fin 3, 16*(errorIndex i+2:ℝ)^2*localErrorCost prime (errorIndex i)*
          ∑χ : RayCharacter, ∑j : Fin 4,
            ((Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
              Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/
                (seed.absNorm:ℝ))*
              CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (errorIndex i+1)
                (τ.modulus.absNorm:ℝ) Z (radius i)
                (refinedErrorDeficit prime Z (errorIndex i+1) sigma
                  (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid saving (r i χ) j)*
              (volume (child src C R0 B τ t)/(normValue prime)^(errorIndex i+1))^(powers εsrc j) := by
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_original_subsets_error_power_full (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ,
    eventually_active_error_ready N upper (max 1 b) (max 1 b) εgeo
      hupper (le_max_left _ _) (le_max_left _ _) hεgeo] with Z hZ hreadyZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime hprimeScale hslot family hrad hfamily
  dsimp only
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip
    hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower r hr
  have hzpos : 0 < Z := zero_lt_one.trans hZ.1
  have hp0 : prime ≠ 0 := fun h => hprime.ne_zero (by simp [h])
  apply firstExtractedErrors_power_budget (child src C R0 B τ t) (R0*C) seed Z
    (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime hprime hslot family
  · intro i χ j
    apply mul_nonneg
    · positivity
    · fin_cases j <;>
        simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
        (try unfold errorCommonRadius) <;> positivity
  · intro i χ Bp
    let d := errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t
    let Re := (R0*C)*(Ideal.span {prime})^(errorIndex i+1)
    let Ke := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve prime (errorIndex i+1)
    by_cases hdead : ∀ I : Ideal O, (original d Re seed).beta I = 0
    · have he := CenteredMomentFirstSecondInputGates.normalized_zero d Re seed hdead ballProfile Ke
      change normalizedGaussSource d Re seed ballProfile Ke ≤ _
      rw [he]
      apply mul_nonneg _ (sq_nonneg _)
      apply Finset.sum_nonneg
      intro j hj
      apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · fin_cases j <;>
            simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
            (try unfold errorCommonRadius) <;> positivity
      · exact Real.rpow_nonneg (volume_pos _).le _
    have hlive : ∃ I : Ideal O, (original d Re seed).beta I ≠ 0 := by
      simpa only [not_forall] using hdead
    have he : Endpoints upper (max 1 b) (max 1 b) src :=
      ⟨hupperSrc, (fun i => by rw [hhiSrc i]; exact hhighs i), hb1, hb1max, hb2, hb2max⟩
    have hKe : 0 < Ke := Real.rpow_pos_of_pos hzpos _
    have hR := hreadyZ.2 src hcard he C R0 seed B τ t hR0 hB
      (Ideal.span {prime}) (Ideal.span_singleton_eq_bot.not.mpr hp0) (errorIndex i+1)
      hslot Bp (family i χ) t Ke Avol Dscale Pmask qmoving ξ hKe hξ.le hzero1 hzero2
      hvolumeCap (hradInv i) hmaskCap (hconductorCap i χ) hlive
    have hready : Ready d Re Ke Z ξ Bcap := ready_mono d Re Ke Z ξ _ Bcap hZ.1.le hbudget hR
    have hk : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by
      fin_cases i <;> norm_num [errorIndex]
    exact hZ.2 θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
      prime hp0 (errorIndex i) hk hprimeScale hslot Bp (family i χ) χ t (hrad i χ) (hfamily i χ)
      (errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t) rfl
      hready seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (r i χ) (hr i χ Bp).1 (hr i χ Bp).2.1 (hr i χ Bp).2.2.1 (hr i χ Bp).2.2.2

#print axioms actual_firstExtractedErrors_power_from_caps_full
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualExtractedErrorCapsFull -/
