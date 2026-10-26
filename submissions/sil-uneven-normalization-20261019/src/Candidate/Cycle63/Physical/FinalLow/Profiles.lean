import Candidate.Cycle63.Physical.FinalLow.Chain
import Candidate.Cycle63.Moment.LowBranch.PaidMain
import Candidate.Cycle63.Physical.FinalProfiles

/- Original module: Candidate.Cycle63.Physical.FinalLow.Geometry. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63FinalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle63FinalNatural Cycle63FinalCapacity
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
      Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle63.Arithmetic.B*Mrow)
    (η : Character) (v : ℝ) (second : Bool) (L₂ : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L₂ (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L₂ a z≠0) :
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)+
        (9/2)*CenteredMomentAllocatedChildCapacity.remainingLogs L₂ a Z (q.final η v).P-
        secondNominal Mrow Z amp omega q.C₁ g.D₁ g.C g.D g.U ≤
      Mrow*Cycle63.Arithmetic.g cell+6*amp+omega+supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  have shift : Real.logb Z (normValue (commonFrequencyGenerator g.C g.D))-
      Real.logb Z ((∏j∈g.U,j.val).absNorm:ℝ)≤Real.logb Z (q.E₂.absNorm:ℝ) := by
    rcases g.label with h|h
    · rw [h]; exact actual_common_shift_le g.C g.D g.hC g.hD g.heq g.U Z hZ
    · rw [h]; exact actual_common_shift_le_right g.C g.D g.hC g.hD g.heq g.U Z hZ
  let X := Cycle63.Physical.sourcePlainScales (q.final η v).toSource second
  have hp : X 0*X 1=(q.final η v).X₁*(q.final η v).X₂ := by
    cases second; rfl; exact (q.final η v).same_product
  have ht := two_stage_supported_capacity s q.C₁ q.R₁ q.B₁ η v q.E₂ q.R₂ q.B₂ L₂ a Z hZ hP
    (X 0) (X 1) (Cycle63Moment.LowBranch.source_plain_positive _ second 0)
    (Cycle63Moment.LowBranch.source_plain_positive _ second 1) hp z hne
  have hr₁ := common_reduction_log_lower (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁ g.first_nonzero Z hZ
  have hr₂ := common_reduction_log_lower (Fintype.card α) b hb q.first (live_card_le q.B₁.val) hs
    q.E₂ q.R₂ q.B₂ g.second_nonzero Z hZ
  have hc := original_affine_capacity s Z Mrow hZ hM hz haff
  have hm : max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0≤Real.logb Z (q.C₁.absNorm:ℝ) :=
    max_le (sub_le_self _ (Real.logb_nonneg hZ (norm_ge_one _ g.hD₁.1)))
      (Real.logb_nonneg hZ (norm_ge_one _ g.hC₁.1))
  have he : CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)=
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
end OAI.SevenEighths.Cycle63FinalLow
end

/- Original module: Candidate.Cycle63.Physical.FinalLow.Main. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63FinalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Actual main second low energy. Constants are chosen on the original
 ambient labels before either common allocation, all rows and all heights. -/
theorem actual_main_low_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs bp₁ bp₂ εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤bs → s.b₁=bp₁ → s.b₂=bp₂ →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤Rwidth) → 0≤mesh → (∀j,w j≤mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤21/25 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤Mrow → 0≤omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle63.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle63.Arithmetic.amp cell
    ∀g : MainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    let src := q.final (g.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.C g.D g.U
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p : Profiles ap bp,
      dilated s.W₁ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 0/
        (Ideal.absNorm (selectedPlain L₂ alloc 0):ℝ)))=p.profile 0 →
      dilated s.W₂ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 1/
        (Ideal.absNorm (selectedPlain L₂ alloc 1):ℝ)))=p.profile 1 →
      finalPlain src second L₂ alloc 0≤Z^L → finalPlain src second L₂ alloc 1≤Z^L →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle63.Arithmetic.q0/9)*padding+Cycle63.Arithmetic.q0*mesh) := by
  obtain ⟨degree,Sp,hmain⟩ := actual_paid_low_main (α:=α) M H hH W A B ap bp 2 Bmask L lo hi Mcap εold
    hA hWs hW hB hap hap' hbp (by norm_num) hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C^(Fintype.card α)*(C₀+C₁),by positivity,?_⟩
  filter_upwards [hbound,Cycle63FinalRadius.fixed_final_width_loss_uniform (fun _:Unit=>ηseed)
    (Fintype.card α) bs 1 εwidth Mmin (zero_lt_one.trans_le hbs) (by norm_num) hew hmin,
    support_padding_eventually_mass (Fintype.card α) bs bp₁ bp₂ εpad Mmin (zero_lt_one.trans_le hbs) hep hmin]
    with Z hZ hwidthLoss hpadLoss
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p hp₁ hp₂ hXcap₁ hXcap₂
  dsimp only
  have hM : 0<Mrow := hmin.trans_le hMmin
  obtain ⟨hc₁,hc₂,_,_⟩ := Cycle63.Moment.originalCell_mem
    (show (17/500:ℝ)≤(∑j,Real.logb Z (s.P j))/Mrow ∧ (∑j,Real.logb Z (s.P j))/Mrow≤1/25 from
      ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩)
  have hcell := Cycle63.Arithmetic.cellUpper_bounds hc₁ hc₂
  have hamp := (mul_pos hM (Cycle63.Arithmetic.amp_pos hcell)).le
  have hshift := CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.C g.D g.hC g.U Z hZone
  have hnmax : 0≤max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0 := le_max_right _ _
  have hnominal : nominal≤Mrow := by unfold nominal secondNominal; linarith
  have hwidth : st.width-nominal≤δwidth := by
    have ht := main_state_width g Bmask hZone (zero_lt_one.trans_le hbs) χ (internalQ Q η₀) hP hPN
    have hl := hwidthLoss.2 () Mrow hMmin
    rw [←hsη] at hl
    norm_num only [Real.logb_one] at hl
    change st.width≤nominal+_ at ht
    dsimp [δwidth]; linarith
  have hδ : 0≤δwidth := by dsimp [δwidth]; positivity
  have hpadding : 0≤padding := by dsimp [padding]; positivity
  have hs : st.width≤Mcap := by dsimp only [δwidth] at hwidth; linarith
  by_cases live : ∃z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0
  · obtain ⟨z,hzrow⟩ := live
    have htotal := main_source_capacity g hbs hsupper hZone hM
      (fun j=>by rw [hm.scale j]; exact Real.one_le_rpow hZone.le (hw j)) hz haff (g.τ χ) v second L₂ alloc z hzrow
    rw [original_slot_sum s q (g.τ χ) v Z hZone w hm.scale L₂ alloc] at htotal
    have hpadd := hpadLoss.2 Mrow hMmin
    rw [←hsb₁,←hsb₂] at hpadd
    have htotal' : length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
        (9/2)*(∑j∈q.indices L₂ alloc,w j)-nominal≤Mrow*Cycle63.Arithmetic.g cell+6*amp+padding := by
      change _≤_ at htotal; dsimp [padding]; linarith
    obtain ⟨R,hR,hpaid,henergy⟩ := hZ.2 (q.indices L₂ alloc) θ w σ freq v height mesh aLow i hw hwL
      (fun j _=>hwr j) hmesh (fun j _=>hwm j) hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh
      st rfl hs p _ _ (zero_lt_one.trans_le (clippedScale_ge_one _))
      (zero_lt_one.trans_le (clippedScale_ge_one _)) hXcap₁ hXcap₂ cell Mrow nominal δwidth padding
      hcell hM.le hwidth hδ hpadding htotal'
    rw [original_low_energy M H hH s η₀ θ w σ freq W B Z Bmask hZone hm q (g.τ χ) v
      (internalQ Q η₀) hP hPN g.radius g.C g.D g.U second L₂ alloc _,hp₁,hp₂]
    exact henergy.trans_eq (by ring)
  · have hzrow : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      simpa only [not_exists,not_not] using live
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms actual_main_low_uniform
end
end OAI.SevenEighths.Cycle63FinalLow
end

/- Original module: Candidate.Cycle63.Physical.FinalLow.Profiles. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63FinalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Literal retained plain quotients, before clipping. -/
def profileScales {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (j : Fin 2) : ℝ :=
  Cycle63.Physical.sourcePlainScales src.toSource second j/(selectedPlain L₂ alloc j).absNorm

theorem profile_scales_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (j : Fin 2) : 0<profileScales src second L₂ alloc j := by
  apply div_pos (source_plain_positive src second j)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero L₂ Finset.univ alloc (Sum.inr j)))

/-- An actual surviving row forces both retained support tests. -/
theorem profile_scales_survive {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O) (hne : Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0) :
    1≤profileScales src second L₂ alloc 0*src.b₁ ∧
      1≤profileScales src second L₂ alloc 1*src.b₂ := by
  exact allocated_survives src L₂ alloc z _ _ (source_plain_positive src second 0)
    (source_plain_positive src second 1) hne

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Actual low bound controlled by the original plain profiles. The uniform
control and all constants precede the moving retained scales. -/
theorem actual_main_low_profiles
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤Rwidth) → 0≤mesh → (∀j,w j≤mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤21/25 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤Mrow → 0≤omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle63.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle63.Arithmetic.amp cell
    ∀g : MainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    let src := q.final (g.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.C g.D g.U
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      finalPlain src second L₂ alloc 0≤Z^L → finalPlain src second L₂ alloc 1≤Z^L →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle63.Arithmetic.q0/9)*padding+Cycle63.Arithmetic.q0*mesh) := by
  have haClip : 0<a/max 1 b := div_pos ha (by positivity)
  have haClip' : a/max 1 b≤1/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<max 1 b)).mpr
    exact ha'.trans (by nlinarith [le_max_left (1:ℝ) b])
  obtain ⟨degree,S,hmain⟩ := actual_main_low_uniform (α:=α) M H hH W A B (a/max 1 b) b Bmask L lo hi Mcap εold
    hA hWs hW hB haClip haClip' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs b b εwidth εpad Mmin hbs hew hep hmin
  obtain ⟨Sp,Cp,hCp,hcontrol⟩ := clipped_pair_control a b ha S
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C*Cp^2,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p₀ hp₁ hp₂ hXcap₁ hXcap₂
  dsimp only
  let U := profileScales src second L₂ alloc
  have hU : ∀j,0<U j := profile_scales_pos src second L₂ alloc
  by_cases hret : ∀j,1≤U j*b
  · let p := retainedPair a b ha p₀ U hU 0
    have hp (j : Fin 2) : (p.profile j : ℝ→ℂ)=dilated (p₀.profile j) (clipDilation (U j)) :=
      actual_clipped_pair a b ha p₀ U hU hret j
    have henergy := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
      Mrow omega ξ hMmin hω hξ hMcap' hz haff q g χ hP hPN second L₂ alloc p
      (by rw [hp 0,←hp₁]; rfl) (by rw [hp 1,←hp₂]; rfl) hXcap₁ hXcap₂
    have hc := hcontrol p₀ U hU
    have hc2 : (p.control S)^2≤Cp^2*(p₀.control Sp)^2 := by
      calc (p.control S)^2≤(Cp*p₀.control Sp)^2 := pow_le_pow_left₀ (Profiles.control_nonneg p S) hc 2
           _=Cp^2*(p₀.control Sp)^2 := by ring
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    let exponent : ℝ := nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
      (2*Cycle63.Arithmetic.q0/9)*padding+Cycle63.Arithmetic.q0*mesh
    apply henergy.trans
    change C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
      (1+|v|+height)^degree*Z^exponent≤_
    calc C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
          (1+|v|+height)^degree*Z^exponent≤
        C*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p₀.control Sp)^2)*
          (1+|v|+height)^degree*Z^exponent := by gcongr
         _=_ := by ring
  · have hzrow : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      intro z
      by_contra hne
      have hh := profile_scales_survive src second L₂ alloc z hne
      have hb₁ : src.b₁=b := hsb₁
      have hb₂ : src.b₂=b := hsb₂
      rw [hb₁,hb₂] at hh
      apply hret
      intro j; fin_cases j
      · exact hh.1
      · exact hh.2
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms profile_scales_survive
#print axioms actual_main_low_profiles
end
end OAI.SevenEighths.Cycle63FinalLow
end
