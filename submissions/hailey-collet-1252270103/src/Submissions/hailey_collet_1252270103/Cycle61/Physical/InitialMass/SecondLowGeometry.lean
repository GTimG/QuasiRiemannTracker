import Submissions.hailey_collet_1252270103.Cycle61.Physical.FinalLow.Chain
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondOrientedWidth

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle61FinalLow
open Cycle61FinalNatural Cycle61FinalCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A main branch described by its literal retained row. It supports both
first orientations and does not require its whole oscillatory block to be
nonzero. All bounds will be derived from these data. -/
structure LiveMainGeometry (s : Input α) (q : Chain s)
    (Z Mrow amp omega ξ b : ℝ) (N : ℕ) where
  reflected : Bool
  C₀ : Ideal O
  D₀ : Ideal O
  hC₀ : Supported C₀
  hD₀ : Supported D₀
  heq₀ : primeSupport C₀=primeSupport D₀
  selected : q.C₁=if reflected then D₀ else C₀
  E₀ : Finset (CommonIndex C₀ D₀)
  hmod : q.η₁.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun j:CommonIndex C₀ D₀=>j.val) E₀*activeConductor C₀ D₀}
  δ : ℝ
  reserve : ℝ
  homega : δ+reserve=omega
  datum : SecondInputDatum α
  parent : datum.input.η=q.η₁
  row : secondLiveRows (fun _:Unit=>datum.block)
  radius_eq : datum.radius=frequencyRadius
    ((b^N*volume s/((if reflected then D₀ else C₀).absNorm:ℝ))^2/
      mainCommonRadius Z (Real.logb Z ((if reflected then C₀ else D₀).absNorm:ℝ))
        (nominalLog C₀ D₀ (Ideal.span {primeSubsetGenerator (fun j:CommonIndex C₀ D₀=>j.val) E₀})
          (Z^Mrow) (volume s) Z)
        (Real.logb Z ((if reflected then D₀ else C₀).absNorm:ℝ)) (3*amp) δ reserve) Z ξ
  label : q.E₂=datum.C ∨ q.E₂=datum.D
  first_nonzero : frozenCoefficient q.B₁.val q.C₁ q.R₁ s.ν s.W s.P≠0
  second_nonzero : frozenCoefficient q.B₂.val q.E₂ q.R₂ q.first.ν q.first.W q.first.P≠0

def LiveMainGeometry.D₁ {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) : Ideal O :=
  if g.reflected then g.C₀ else g.D₀

theorem LiveMainGeometry.hC₁ {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) : Supported q.C₁ := by
  rw [g.selected]
  split <;> first | exact g.hC₀ | exact g.hD₀

theorem LiveMainGeometry.hD₁ {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) : Supported g.D₁ := by
  unfold LiveMainGeometry.D₁
  split <;> first | exact g.hC₀ | exact g.hD₀

/-- Width follows from the actual live row, its conductor and the exact
oriented Fourier cutoff. -/
theorem live_main_state_width {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (Bmask : ℝ) (hZ : 1<Z) (hb : 0<b)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask) :
    (retainedState Z Bmask hZ (g.datum.τ χ) Q (q.R₂*q.E₂) hP hPN
      g.datum.radius g.datum.C g.datum.D g.datum.inactive).width ≤
      secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive+
        (Real.logb Z (s.η.modulus.absNorm:ℝ)+
          Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+
          ξ/2+Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))) := by
  have hm : g.datum.input.η.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun j:CommonIndex g.C₀ g.D₀=>j.val) g.E₀*activeConductor g.C₀ g.D₀} := by
    rw [g.parent]; exact g.hmod
  have hh := actual_second_live_main_width_oriented g.reflected (fun _:Unit=>g.datum) g.row
    s.η g.C₀ g.D₀ g.hC₀ g.hD₀ g.heq₀ g.E₀ (Z^Mrow) (volume s) Z amp g.δ g.reserve ξ b N
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (volume_pos s) hZ hb hm
    Bmask χ Q _ hP hPN g.radius_eq
  dsimp only at hh
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  unfold secondNominal LiveMainGeometry.D₁
  rw [g.selected]
  linarith [g.homega]

theorem live_main_source_capacity {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b (Fintype.card α)) (hb : 1≤b)
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
        secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive ≤
      Mrow*Cycle61.Arithmetic.g cell+6*amp+omega+supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  have shift : Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
      Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ)≤Real.logb Z (q.E₂.absNorm:ℝ) := by
    rcases g.label with h|h
    · rw [h]; exact actual_common_shift_le g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
    · rw [h]; exact actual_common_shift_le_right g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
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

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.live_main_state_width
#print axioms OAI.SevenEighths.Cycle61InitialMass.live_main_source_capacity
