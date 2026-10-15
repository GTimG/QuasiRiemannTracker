/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B115
import Submissions.gao_cycle61_plane_20261013.Bundles.B122
import Submissions.gao_cycle61_plane_20261013.Bundles.B125
import Submissions.gao_cycle61_plane_20261013.Bundles.B129
import Submissions.gao_cycle61_plane_20261013.Bundles.B136
import Submissions.gao_cycle61_plane_20261013.Bundles.B140

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorRetained; sha256 2206e68c50f9d9e4055885a0be64e550d79a732c0d409ee8c320fe2f108b2098 -/
section
                                                          

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondLocalization
local notation "O" => HeckeFamily.O
local instance errorRetainedDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Canceled physical blocks are removed before absolute values or column
estimates. Every surviving block supplies the nonvanishing field required
by the extracted-prime geometry theorem. -/
theorem actual_nonzero_retained_assembly (slots : Finset α)(s : Input slots)
    (R seed : Ideal O)(hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (W : 𝓢(ℝ,ℂ))(K Tsec Z ξ : ℝ)(hK : 0< K) :
    let datum := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK
    let blocks := Finset.univ.filter (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
      (datum q).block.value W≠0)
    secondRetainedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) W K Tsec Z ξ=
      ∑q : blocks,actualSecondBlockWeight s R seed K Tsec Z ξ q.val*(datum q.val).block.value W := by
  intro datum blocks
  rw [actual_original_retained_assembly slots s R seed hseed hz₁ hz₂ W K Tsec Z ξ hK]
  symm
  rw [Finset.sum_coe_sort blocks (fun q=>actualSecondBlockWeight s R seed K Tsec Z ξ q*(datum q).block.value W)]
  dsimp only [blocks]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  change (if (datum q).block.value W≠0 then actualSecondBlockWeight s R seed K Tsec Z ξ q*(datum q).block.value W else 0)=actualSecondBlockWeight s R seed K Tsec Z ξ q*(datum q).block.value W
  by_cases hz : (datum q).block.value W=0
  · simp only [hz,ne_eq,not_true_eq_false,ite_false,mul_zero]
  · simp only [hz,ne_eq,not_false_eq_true,ite_true]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_nonzero_retained_assembly

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorRetained -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorSecondSplit; sha256 5db89053cf529f0524e4484706b2cafe07191dd604195334f612dd6d487b9544 -/
section
                                                       
                                                            

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSecondLocalization CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSupportedTailAggregate EisensteinSchwartzPoisson
open CenteredMomentCommonAllocationSum CenteredMomentFirstAnnularInput
open CenteredMomentCommonProfile CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentFirstReferenceSource CenteredMomentAmplifiedRetainedRadius
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _

theorem actual_heterogeneous_normalized_source_budget {Label : Type*} [Fintype Label]
    (α : Label→ Type*) [∀l,Fintype (α l)] (s : (l : Label)→ Input (α l))
    (R seed : Label→ Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec : Label→ℝ) (Z ξ : ℝ)
    (hK : ∀l,0< K l)(weight : Label→ℝ)(hw : ∀l,0≤ weight l) :
    (∑l,weight l*normalizedGaussSource (s l) (R l) (seed l) W (K l))≤
      (∑l,(weight l/volume (s l))*(‖originalSecondZero (s l) (R l) (seed l) W (K l)‖+
        ‖secondDiscardedEnergy (s l).η (s l).t (original (s l) (R l) (seed l)).columns
          (original (s l) (R l) (seed l)).beta W (K l) (Tsec l) Z ξ‖))+
      ‖∑l,((weight l/volume (s l):ℝ):ℂ)*secondRetainedEnergy (s l).η (s l).t
        (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
          W (K l) (Tsec l) Z ξ‖ := by
  let ret := fun l=>secondRetainedEnergy (s l).η (s l).t
    (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
      W (K l) (Tsec l) Z ξ
  let tail := fun l=>secondDiscardedEnergy (s l).η (s l).t
    (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
      W (K l) (Tsec l) Z ξ
  let zero := fun l=>originalSecondZero (s l) (R l) (seed l) W (K l)
  let c := fun l=>weight l/volume (s l)
  have hc (l : Label) : 0≤ c l := div_nonneg (hw l) (volume_pos (s l)).le
  have he (l : Label) : weight l*normalizedGaussSource (s l) (R l) (seed l) W (K l)=
      c l*(zero l).re+c l*(ret l).re+c l*(tail l).re := by
    unfold normalizedGaussSource
    rw [sourceGaussEnergy_localized _ _ _ _ W (K l) (Tsec l) Z ξ (hK l)]
    simp only [Complex.add_re]
    dsimp only [c,zero,ret,tail,originalSecondZero]
    ring
  have hr : (∑l,c l*(ret l).re)≤‖∑l,(c l:ℂ)*ret l‖ := by
    have heq : (∑l,c l*(ret l).re)=(∑l,(c l:ℂ)*ret l).re := by
      simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [heq]
    exact Complex.re_le_norm _
  have hz : (∑l,(c l*(zero l).re+c l*(tail l).re))≤
      ∑l,c l*(‖zero l‖+‖tail l‖) := by
    apply Finset.sum_le_sum
    intro l hl
    calc
      _≤ c l*‖zero l‖+c l*‖tail l‖ := add_le_add
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hc l))
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hc l))
      _=_ := by ring
  simp_rw [he]
  calc
    _=(∑l,(c l*(zero l).re+c l*(tail l).re))+(∑l,c l*(ret l).re) := by
      simp only [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _≤ _ := add_le_add hz hr


/-- The literal extracted-prime sources, across a heterogeneous family
of first common children, retain one joint second-transform sum. -/
theorem actual_joint_error_second_split {First : Type*}[Fintype First]
    (α : First→ Type*) [∀q,Fintype (α q)]
    (s : (q : First)→ Input (α q))(g : First→ FirstBranchGeometry)
    (w : First→ℝ)(hw : ∀q,0≤ w q)(Z sigma Csec ξ reserve : ℝ)(hZ : 0< Z)
    (P : Finset (Ideal O))
    (τ : First→ elementPool P→ Fin 3→ RayCharacter→ Character) :
    let Label := (q : First) × (p : elementPool P) × (i : Fin 3) ×
      (_ψ : RayCharacter) × actualAllocations (activeInput (s q)).pools
        ((Ideal.span {p.val})^(errorIndex i+1))
    let E := fun l : Label=>(Ideal.span {l.2.1.val})^(errorIndex l.2.2.1+1)
    let source := fun l : Label=>child (s l.1) (E l) (g l.1).R
      (errorActiveAllocation (s l.1) _ l.2.2.2.2) (τ l.1 l.2.1 l.2.2.1 l.2.2.2.1) (s l.1).t
    let radius := fun l : Label=>errorCommonRadius Z (g l.1).d
      (nominalLog (g l.1).I (g l.1).J (g l.1).E (g l.1).K (g l.1).X Z)
      (g l.1).cLog sigma (frequencyLoss Z (32*Csec) ξ) reserve l.2.1.val (errorIndex l.2.2.1+1)
    let coeff := fun l : Label=>w l.1*
      (16*(errorIndex l.2.2.1+2:ℝ)*localErrorCost l.2.1.val (errorIndex l.2.2.1))
    let c := fun l : Label=>coeff l/volume (source l)
    ∀Tsec : Label→ℝ,
    (∑q : First,w q*actualErrorSources (s q) (g q) Z sigma Csec ξ reserve P (τ q))≤
      (∑l : Label,c l*(‖originalSecondZero (source l) ((g l.1).R*E l) (g l.1).seed ballProfile (radius l)‖+
        ‖secondDiscardedEnergy (source l).η (source l).t
          (original (source l) ((g l.1).R*E l) (g l.1).seed).columns
          (original (source l) ((g l.1).R*E l) (g l.1).seed).beta
          ballProfile (radius l) (Tsec l) Z ξ‖))+
      ‖∑l : Label,(c l:ℂ)*secondRetainedEnergy (source l).η (source l).t
        (original (source l) ((g l.1).R*E l) (g l.1).seed).columns
        (original (source l) ((g l.1).R*E l) (g l.1).seed).beta
        ballProfile (radius l) (Tsec l) Z ξ‖ := by
  intro Label E source radius coeff c Tsec
  have hh := actual_heterogeneous_normalized_source_budget
    (fun l : Label=>liveIndices l.2.2.2.2.val) source
    (fun l=>(g l.1).R*E l) (fun l=>(g l.1).seed) ballProfile radius Tsec Z ξ
    (fun l=>Real.rpow_pos_of_pos hZ _) coeff (by
      intro l
      have he := localErrorCost_nonneg l.2.1.val (errorIndex l.2.2.1)
      have hwq := hw l.1
      dsimp only [coeff]
      positivity)
  apply (le_of_eq ?_).trans hh
  simp_rw [actual_error_sources_lifted]
  simp only [Label,Fintype.sum_sigma,Finset.mul_sum,childNormalizedGaussSource]
  dsimp only [coeff,source,radius,E]
  simp only [mul_assoc]
  rfl

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_heterogeneous_normalized_source_budget
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_error_second_split

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorSecondSplit -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowGeometry; sha256 078ddfc75452f45c7a3d795389c36d39845968f90e6ae1317359889df91729eb -/
section
                                      
                                                       

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
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (Bmask : ℝ) (hZ : 1< Z) (hb : 0< b)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask) :
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
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b (Fintype.card α)) (hb : 1≤ b)
    (hs : s.upper≤ b) (hZ : 1< Z) (hM : 0< Mrow) (hP : ∀j,1≤ s.P j)
    (hz : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow)
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
      Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ)≤ Real.logb Z (q.E₂.absNorm:ℝ) := by
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
  have hm : max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0≤ Real.logb Z (q.C₁.absNorm:ℝ) :=
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
  change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume s.toData)+(7/2)*(∑j,Real.logb Z (s.P j))≤ _ at hc
  change _≤ _ at ht hr₂
  dsimp only [Chain.first,Chain.final,CenteredMomentCommonRadialData.commonData,
    CenteredMomentCommonHeightEnvelope.withHeight,CenteredMomentAmplificationChildInput.child] at ht hr₂ ⊢
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.live_main_state_width
#print axioms OAI.SevenEighths.Cycle61InitialMass.live_main_source_capacity

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowGeometry -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowUniform; sha256 25d9bfa0841fe1507f0bc383c6de7174253ee3ce677631aee7ceb492cc57654b -/
section
                                                     
                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
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
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual main second low energy. Constants are chosen on the original
 ambient labels before either common allocation, all rows and all heights. -/
theorem actual_live_main_low_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs bp₁ bp₂ εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=bp₁ → s.b₂=bp₂ →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤167/200 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := q.final (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p : Profiles ap bp,
      dilated s.W₁ (clipDilation (Cycle61.Physical.sourcePlainScales src.toSource second 0/
        (Ideal.absNorm (selectedPlain L₂ alloc 0):ℝ)))=p.profile 0 →
      dilated s.W₂ (clipDilation (Cycle61.Physical.sourcePlainScales src.toSource second 1/
        (Ideal.absNorm (selectedPlain L₂ alloc 1):ℝ)))=p.profile 1 →
      finalPlain src second L₂ alloc 0≤ Z^L → finalPlain src second L₂ alloc 1≤ Z^L →
    let hQM' : st.fixedModulus≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh) := by
  obtain ⟨degree,Sp,hmain⟩ := actual_paid_low_main (α:=α) M H hH W A B ap bp 2 Bmask L lo hi Mcap εold
    hA hWs hW hB hap hap' hbp (by norm_num) hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C^(Fintype.card α)*(C₀+C₁),by positivity,?_⟩
  filter_upwards [hbound,Cycle61FinalRadius.fixed_final_width_loss_uniform (fun _:Unit=>ηseed)
    (Fintype.card α) bs 1 εwidth Mmin (zero_lt_one.trans_le hbs) (by norm_num) hew hmin,
    support_padding_eventually_mass (Fintype.card α) bs bp₁ bp₂ εpad Mmin (zero_lt_one.trans_le hbs) hep hmin]
    with Z hZ hwidthLoss hpadLoss
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p hp₁ hp₂ hXcap₁ hXcap₂
  dsimp only
  have hM : 0< Mrow := hmin.trans_le hMmin
  obtain ⟨hc₁,hc₂,_,_⟩ := Cycle61.Moment.originalCell_mem
    (show (17/500:ℝ)≤(∑j,Real.logb Z (s.P j))/Mrow ∧ (∑j,Real.logb Z (s.P j))/Mrow≤1/25 from
      ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩)
  have hcell := Cycle61.Arithmetic.cellUpper_bounds hc₁ hc₂
  have hamp := (mul_pos hM (Cycle61.Arithmetic.amp_pos hcell)).le
  have hshift := CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.datum.C g.datum.D g.datum.hC g.datum.inactive Z hZone
  have hnmax : 0≤ max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0 := le_max_right _ _
  have hnominal : nominal≤ Mrow := by unfold nominal secondNominal; linarith
  have hwidth : st.width-nominal≤δwidth := by
    have ht := live_main_state_width g Bmask hZone (zero_lt_one.trans_le hbs) χ (internalQ Q η₀) hP hPN
    have hl := hwidthLoss.2 () Mrow hMmin
    rw [←hsη] at hl
    norm_num only [Real.logb_one] at hl
    change st.width≤ nominal+_ at ht
    dsimp [δwidth]; linarith
  have hδ : 0≤δwidth := by dsimp [δwidth]; positivity
  have hpadding : 0≤ padding := by dsimp [padding]; positivity
  have hs : st.width≤ Mcap := by dsimp only [δwidth] at hwidth; linarith
  by_cases live : ∃z,Cycle61.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0
  · obtain ⟨z,hzrow⟩ := live
    have htotal := live_main_source_capacity g hbs hsupper hZone hM
      (fun j=>by rw [hm.scale j]; exact Real.one_le_rpow hZone.le (hw j)) hz haff (g.datum.τ χ) v second L₂ alloc z hzrow
    rw [original_slot_sum s q (g.datum.τ χ) v Z hZone w hm.scale L₂ alloc] at htotal
    have hpadd := hpadLoss.2 Mrow hMmin
    rw [←hsb₁,←hsb₂] at hpadd
    have htotal' : length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
        (9/2)*(∑j∈q.indices L₂ alloc,w j)-nominal≤ Mrow*Cycle61.Arithmetic.g cell+6*amp+padding := by
      change _≤ _ at htotal; dsimp [padding]; linarith
    obtain ⟨R,hR,hpaid,henergy⟩ := hZ.2 (q.indices L₂ alloc) θ w σ freq v height mesh aLow i hw hwL
      (fun j _=>hwr j) hmesh (fun j _=>hwm j) hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh
      st rfl hs p _ _ (zero_lt_one.trans_le (clippedScale_ge_one _))
      (zero_lt_one.trans_le (clippedScale_ge_one _)) hXcap₁ hXcap₂ cell Mrow nominal δwidth padding
      hcell hM.le hwidth hδ hpadding htotal'
    rw [original_low_energy M H hH s η₀ θ w σ freq W B Z Bmask hZone hm q (g.datum.τ χ) v
      (internalQ Q η₀) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive second L₂ alloc _,hp₁,hp₂]
    exact henergy.trans_eq (by ring)
  · have hzrow : ∀z,Cycle61.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      simpa only [not_exists,not_not] using live
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_live_main_low_uniform
end
end OAI.SevenEighths.Cycle61InitialMass

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowUniform -/
