import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.FinalLow.Chain

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61FinalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle61FinalNatural Cycle61FinalCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

def mainRadius {s : Input α} (q : Chain s) (D₁ : Ideal O) (E : Finset (CommonIndex q.C₁ D₁))
    (Z Mrow amp δ reserve ξ b : ℝ) (N : ℕ) : ℝ :=
  frequencyRadius ((b^N*volume s/(q.C₁.absNorm:ℝ))^2/
    mainCommonRadius Z (Real.logb Z (D₁.absNorm:ℝ))
      (nominalLog q.C₁ D₁ (Ideal.span {primeSubsetGenerator (fun j:CommonIndex q.C₁ D₁=>j.val) E})
        (Z^Mrow) (volume s) Z) (Real.logb Z (q.C₁.absNorm:ℝ)) (3*amp) δ reserve) Z ξ

/-- Genuine main second-transform data. Every field is a physical support,
 character, coefficient or radius identity; no norm or capacity estimate. -/
structure MainGeometry (s : Input α) (q : Chain s) (Z Mrow amp omega ξ b : ℝ) (N : ℕ) where
  D₁ : Ideal O
  hC₁ : Supported q.C₁
  hD₁ : Supported D₁
  heq₁ : primeSupport q.C₁=primeSupport D₁
  E : Finset (CommonIndex q.C₁ D₁)
  hmod : q.η₁.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun j:CommonIndex q.C₁ D₁=>j.val) E*activeConductor q.C₁ D₁}
  δ : ℝ
  reserve : ℝ
  homega : δ+reserve=omega
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  heq : primeSupport C=primeSupport D
  U : Finset (CommonIndex C D)
  τ : RayFourExpansion.RayCharacter→Character
  family : Family q.η₁ C D hC hD U τ
  label : q.E₂=C ∨ q.E₂=D
  first_nonzero : frozenCoefficient q.B₁.val q.C₁ q.R₁ s.ν s.W s.P≠0
  second_nonzero : frozenCoefficient q.B₂.val q.E₂ q.R₂ q.first.ν q.first.W q.first.P≠0
  cols : Finset (Ideal O)
  coefficient : Ideal O→ℂ
  frequencies : Finset O
  profile : 𝓢(ℝ,ℂ)
  scale : ℝ
  scale_pos : 0<scale
  bin : Fin 4→ℤ
  block_nonzero : physicalBlock q.η₁ q.t₁ cols coefficient C D hC hD U
    (mainRadius q D₁ E Z Mrow amp δ reserve ξ b N) frequencies profile scale bin≠0

def MainGeometry.radius {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : MainGeometry s q Z Mrow amp omega ξ b N) := mainRadius q g.D₁ g.E Z Mrow amp g.δ g.reserve ξ b N

/-- The actual nonzero block supplies the final retained state width. -/
theorem main_state_width {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : MainGeometry s q Z Mrow amp omega ξ b N) (Bmask : ℝ) (hZ : 1<Z) (hb : 0<b)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask) :
    (retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U).width ≤
      secondNominal Mrow Z amp omega q.C₁ g.D₁ g.C g.D g.U+
        (Real.logb Z (s.η.modulus.absNorm:ℝ)+
          Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+
          ξ/2+Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))) := by
  have hh := actual_main_retainedState_width s.η q.η₁ q.C₁ g.D₁ g.hC₁ g.hD₁ g.heq₁ g.E
    (Z^Mrow) (volume s) Z amp g.δ g.reserve ξ b N
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (volume_pos s) hZ hb g.hmod
    g.C g.D g.hC g.hD g.U g.τ g.family q.t₁ g.cols g.coefficient g.frequencies
    g.profile g.scale g.scale_pos g.bin Bmask χ Q _ hP hPN g.block_nonzero
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  change (retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U).width≤_ at hh
  unfold secondNominal
  linarith [g.homega]

/-- Both genuine second labels have the same supported final capacity. -/
theorem main_source_capacity {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ}
    (g : MainGeometry s q Z Mrow amp omega ξ b (Fintype.card α)) (hb : 1≤b)
    (hs : s.upper≤b) (hZ : 1<Z) (hM : 0<Mrow) (hP : ∀j,1≤s.P j)
    (hz : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle61.Arithmetic.B*Mrow)
    (η : Character) (v : ℝ) (second : Bool) (L₂ : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L₂ (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle61.Physical.sourcePositiveRow (q.final η v).toSource second L₂ a z≠0) :
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    CenteredMomentEnergyBands.length Z (Cycle61Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle61Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)+
        (9/2)*CenteredMomentAllocatedChildCapacity.remainingLogs L₂ a Z (q.final η v).P-
        secondNominal Mrow Z amp omega q.C₁ g.D₁ g.C g.D g.U ≤
      Mrow*Cycle61.Arithmetic.g cell+6*amp+omega+supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  have shift : Real.logb Z (normValue (commonFrequencyGenerator g.C g.D))-
      Real.logb Z ((∏j∈g.U,j.val).absNorm:ℝ)≤Real.logb Z (q.E₂.absNorm:ℝ) := by
    rcases g.label with h|h
    · rw [h]; exact actual_common_shift_le g.C g.D g.hC g.hD g.heq g.U Z hZ
    · rw [h]; exact actual_common_shift_le_right g.C g.D g.hC g.hD g.heq g.U Z hZ
  let X := Cycle61.Physical.sourcePlainScales (q.final η v).toSource second
  have hp : X 0*X 1=(q.final η v).X₁*(q.final η v).X₂ := by
    cases second; rfl; exact (q.final η v).same_product
  have ht := two_stage_supported_capacity s q.C₁ q.R₁ q.B₁ η v q.E₂ q.R₂ q.B₂ L₂ a Z hZ hP
    (X 0) (X 1) (Cycle61Moment.LowBranch.source_plain_positive _ second 0)
    (Cycle61Moment.LowBranch.source_plain_positive _ second 1) hp z hne
  have hr₁ := common_reduction_log_lower (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁ g.first_nonzero Z hZ
  have hr₂ := common_reduction_log_lower (Fintype.card α) b hb q.first (live_card_le q.B₁.val) hs
    q.E₂ q.R₂ q.B₂ g.second_nonzero Z hZ
  have hc := original_affine_capacity s Z Mrow hZ hM hz haff
  have hm : max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0≤Real.logb Z (q.C₁.absNorm:ℝ) :=
    max_le (sub_le_self _ (Real.logb_nonneg hZ (norm_ge_one _ g.hD₁.1)))
      (Real.logb_nonneg hZ (norm_ge_one _ g.hC₁.1))
  have he : CenteredMomentEnergyBands.length Z (Cycle61Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle61Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)=
      CenteredMomentAllocatedChildCapacity.plainLogs L₂ a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))=_
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]; rfl
  dsimp only at hc ht ⊢
  rw [he]; unfold secondNominal supportPadding
  change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume s.toData)+(7/2)*(∑j,Real.logb Z (s.P j))≤_ at hc
  change _≤_ at ht hr₂
  dsimp only [Chain.first,Chain.final,CenteredMomentCommonRadialData.commonData,
    CenteredMomentCommonHeightEnvelope.withHeight,CenteredMomentAmplificationChildInput.child] at ht hr₂ ⊢
  linarith

#print axioms main_source_capacity
#print axioms main_state_width
end
end OAI.SevenEighths.Cycle61FinalLow
