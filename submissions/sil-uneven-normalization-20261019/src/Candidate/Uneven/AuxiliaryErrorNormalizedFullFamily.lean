/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryErrorMain
import Candidate.Uneven.AuxiliaryCellGeometry
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Uneven.AuxiliaryErrorNormalizedClosure
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell
import Candidate.Uneven.AuxiliaryAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.AuxiliaryErrorReconstruction
open OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open OAI.SevenEighths.AuxiliaryReconstruction
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondRetainedRows
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentEligibleEnergy CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAmplificationErrorEnergy CenteredMomentRestrictedEnergy
open CenteredMomentAllocatedRayDictionary CenteredMomentSlotRatios
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Cycle63FinalNatural Cycle63Moment Cycle63FinalError Cycle63FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance errorNormalizedFullFamilySumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


/-- Arbitrary finite original block families retain both ray sums, the
complete ordinary zero-mode sets and the exact extracted-prime coefficient. -/
theorem actual_error_indexed_normalized_to_admitted_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0 < K)
    (index : Label→ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0 ≤ weight) (prime : O) (i : Fin 3)
    (N : ℕ) (a ap : ℝ) (ha : 0 < a) (hap : 0 < ap)
    (hcard : Fintype.card α ≤ N) (hlower : a ≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ap ≤ x) (hW₂ : ∀x,s.W₂ x≠0→ap ≤ x)
    (W : 𝓢(ℝ,ℂ)) (χ₀ : Label→RayCharacter) (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72:O)})
    (second : Bool) (t u : ℝ) :
    let d := fun n=>actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK (index n)
    let datum := fun n=>ordinarySecondDatum (d n) (χ₀ n) Q fixedBadMask
    let c := errorNormalizedCoefficient P weight (volume s) prime i
    let w := fun n=>(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ (index n)
    secondNormalizedSum second datum
      (secondEffectiveWeight (fun n=>(datum n).block) w W) t u ≤ 
      ∑χ : RayCharacter,∑ψ : RayCharacter,∑n,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if second then
            ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D z‖^2
           else
            ∑z∈partRows false s.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
  intro d datum c w
  have hc : 0 ≤ c := error_normalized_coefficient_nonneg P weight (volume s) hw (volume_pos s) prime i
  have hbase := actual_error_ordinary_normalized_columns N a ap ha hap d w W hcard
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂) χ₀ Q second t u
  apply hbase.trans
  calc
    _ ≤ ∑n,∑χ : RayCharacter,∑ψ : RayCharacter,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          ∑z∈partRows false s.η (χ₀ n) Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
            (if second then
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D (-z)‖^2
             else
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro χ _
      apply Finset.sum_le_sum
      intro ψ _
      have hn := actual_error_block_weight_norm s R seed K Tsec Z ξ (index n) c hc
      have hf : 0 ≤ K/lowerFactor N a ap := div_nonneg hK.le (lowerFactor_pos N a ap ha hap).le
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hf)
          (normalizer_pos (d n).C (d n).D (d n).hC (d n).inactive).le
      · exact Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>by split_ifs <;> positivity))
    _=∑n,∑χ : RayCharacter,∑ψ : RayCharacter,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if second then
            ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D z‖^2
           else
            ∑z∈partRows false s.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ψ _
      apply congrArg (fun r : ℝ=>(c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*r)
      apply Finset.sum_congr rfl
      intro D _
      exact actual_error_complete_column_rows s (d n).τ (d n).C (d n).D (d n).hC (d n).hD
        (d n).inactive R seed D Q (d n).radius hQ (χ₀ n) χ ψ second t u
    _=_ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro χ _; rw [Finset.sum_comm]


set_option linter.defProp false in
/-- Literal specialization to the lifted active extracted source. The
inferred result retains every original first key and error-radius parameter. -/
def actual_geometry_error_indexed_admitted_columns
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0 ≤ weight)
    (Ncap : ℕ) (a ap : ℝ) (ha : 0 < a) (hap : 0 < ap) (hcard : Fintype.card α ≤ Ncap)
    (hlower : a ≤ s.lower) (hW₁ : ∀x,s.W₁ x≠0→ap ≤ x) (hW₂ : ∀x,s.W₂ x≠0→ap ≤ x)
    (W : 𝓢(ℝ,ℂ))
    (χ₀ : Label→RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72:O)}) (second : Bool) (θ u : ℝ) :=
  actual_error_indexed_normalized_to_admitted_columns
    (liveIndices (errorActiveAllocation
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val)
    (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)
    ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1))
    q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property)
    hw₁ hw₂ (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
    (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
    index
    P weight hw p i Ncap a ap ha hap
    ((Fintype.card_subtype_le _).trans hcard) hlower hW₁ hW₂ W χ₀ Q hQ second θ u



private theorem error_full_ray_column_transport {Label : Type*}[Fintype Label]
    {Ds : Label→Finset (Ideal O)} {rawCoefficient paidCoefficient : Label→ℝ}
    {raw paid : RayCharacter→RayCharacter→Label→Ideal O→ℝ} {E : ℝ}
    (hc : ∀n,rawCoefficient n=paidCoefficient n)
    (hcolumn : ∀χ ψ n D,D∈Ds n → raw χ ψ n D=paid χ ψ n D)
    (hpaid : ∀χ ψ,(∑n,paidCoefficient n*∑D∈Ds n,paid χ ψ n D) ≤ E) :
    (∑χ : RayCharacter,∑ψ : RayCharacter,∑n,rawCoefficient n*∑D∈Ds n,raw χ ψ n D) ≤ 
      ((Fintype.card RayCharacter:ℝ)^2)*E := by
  calc
    _=(∑χ : RayCharacter,∑ψ : RayCharacter,∑n,paidCoefficient n*∑D∈Ds n,paid χ ψ n D) := by
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ψ _
      apply Finset.sum_congr rfl
      intro n _
      apply congrArg₂ (fun x y : ℝ=>x*y) (hc n)
      exact Finset.sum_congr rfl (fun D hD=>hcolumn χ ψ n D hD)
    _ ≤ ∑_χ : RayCharacter,∑_ψ : RayCharacter,E :=
      Finset.sum_le_sum (fun χ _=>Finset.sum_le_sum (fun ψ _=>hpaid χ ψ))
    _=((Fintype.card RayCharacter:ℝ)^2)*E := by simp; ring

set_option linter.defProp false in
/-- Literal ordinary normalized error sums from the genuine paid columns.
The two ray sums pay their fixed finite cardinality, with the first key intact. -/
def actual_geometry_error_paid_normalized_family {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hBmask : 0 ≤ Bmask) (hL : 0 ≤ L) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hloss : 0 < loss) (hmargin : 0 < margin) (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ Sil.Uneven.AuxiliarySource.kappa)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0 ≤ window) (hpad : 0 < pad) (heshell : 0 < εshell)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1 ≤ Cs)(hL₂ : 0 ≤ L₂)(heproj : 0 < εproj) :=
  let hJ : 0 < (fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  let uniform := actual_paid_error_complete_projector_family  (α:=α)
    M H hH W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
    hBmask hL hMcap hεold hloss hmargin hbeta hκbeta ηseed bs (fixedFactor:ℝ) εwidth εpad Mmin
    window pad εshell hwindow hpad heshell hbs hJ hew hep hmin N Cs L₂ εproj hCs hL₂ heproj
  let degree := Classical.choose uniform
  let profiles := Classical.choose_spec uniform
  let Sp := Classical.choose profiles
  let hfamily := Classical.choose_spec profiles
  (fun (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M)
      (hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
      (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})=>
    let receipt := hfamily η₀ Q hQM hQ0 hQt hQ72
    let Cg := Classical.choose receipt
    let bound := Classical.choose_spec receipt
    PProd.mk Cg (And.intro bound.1
      (bound.2.mono (fun Z hz=>And.intro hz.1
        (fun (hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)
          (w σ freq : α→ℝ)(height mesh : ℝ)
          hcard hM hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin
          (Mrow ξ : ℝ) hMmin hξ hMcap' hslot haff=>
        let cell := Sil.Uneven.AuxiliarySource.widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
        let amp := Mrow*Sil.Uneven.AuxiliarySource.amp cell
        fun (reserve : ℝ)(hreserve : 0 ≤ frequencyLoss Z 32 ξ+reserve)
          (reflected : Bool)(R seed : Ideal O)(t₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
          (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
          (prime : O)(i : Fin 3)(hp : prime≠0)
          (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first).slots j→IsCoprime (Ideal.span {prime}) I)
          (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first)).pools ((Ideal.span {prime})^(errorIndex i+1)))
          (υ : Character)(v₀ : ℝ)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(ψ : RayCharacter)
          (hυ : υ.modulus.absNorm ≤ radicalBound
            (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) ψ)
            fixedBadMask prime (errorMovingExponent (errorIndex i)))
          (hf₁ : frozenCoefficient first.2.val
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) R s.ν s.W s.P≠0)
          (hprime : 3*amp/4 ≤ Real.logb Z (normValue prime))=>
        fun {Label : Type v} [Fintype Label]
          (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀)=>
        let datum := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
        fun (hne : ∀n : Label,(datum n).block.value ballProfile≠0)(second : Bool)=>
        let alloc := fun n=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second
        let chains := fun n=>geometryErrorChain reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀ hp hcop
          (if second then (datum n).D else (datum n).C) (datum n).R (alloc n)
        let geom := fun n=>geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁

        fun (hP : ∀n,(chains n).R₂*(chains n).E₂≠0)
          (hPN : ∀n,(((chains n).R₂*(chains n).E₂).absNorm:ℝ) ≤ Z^Bmask)
          (p : Profiles ap bp)(hp₁ : s.W₁=p.profile 0)(hp₂ : s.W₂=p.profile 1)
          (a : ℝ)(ha : 0 < a)(hlower : a ≤ s.lower)
          (hW₁ : ∀x,s.W₁ x≠0→ap ≤ x)(hW₂ : ∀x,s.W₂ x≠0→ap ≤ x)
          (windowProfile : 𝓢(ℝ,ℂ))(χ₀ : Label→RayCharacter)
          (P : Finset (Ideal O))(weight : ℝ)(hwgt : 0 ≤ weight)
          (hcap : ∀n D,D∈(datum n).block.divisors.filter Squarefree→(D.absNorm:ℝ) ≤ Z^L₂)
          (tₑ u : ℝ)=>
        let analyticv := v₀+2*Real.pi*(u-(if second then -tₑ else tₑ))
        let Ds := fun n=>(datum n).block.divisors.filter Squarefree
        let hDs : ∀n D,D∈Ds n→Squarefree D := fun _ _ hD=>(Finset.mem_filter.mp hD).2
        let hk (n : Label) : (chains n).k=1 ∨ (chains n).k=6 ∨ (chains n).k=7 := by
          change errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7
          fin_cases i <;> norm_num [errorIndex]
        let hprime' (n : Label) : 3*amp/4 ≤ Real.logb Z (normValue (chains n).p) := hprime
        let hE₂ (n : Label) : Supported (chains n).E₂ := by
          cases second with
          | false => exact (datum n).hC
          | true => exact (datum n).hD
        let hs (n : Label) : (datum n).seed∣(chains n).E₂ := by
          have hg := actual_geometry_error_seed_gates reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
          cases second with
          | false => exact hg.1
          | true => exact hg.2
        let source := geometryErrorChild reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀
        let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i
        let columnWeight : Label→ℝ := fun n=>weight*(K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive
        let hcolumnWeight : ∀n,0 ≤ columnWeight n := by
          intro n
          have hK := actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i
          have hlf := lowerFactor_pos N a ap ha hap
          have hn := normalizer_pos (datum n).C (datum n).D (datum n).hC (datum n).inactive
          dsimp only [columnWeight]
          positivity
        let coefficient : Label→ℝ := fun n=>(56/(P.card:ℝ))*columnWeight n*16*((chains n).k+1:ℝ)/volume (chains n).extracted
        let scalar : Label→ℝ := fun n=>coefficient n*
          Z^(errorRemoval (chains n).p Z (chains n).k-errorMoving (chains n).p Z (chains n).k)*
          ((chains n).E₂.absNorm:ℝ)^(εshell-1)*
          Z^((geom n).nominal+εwidth*Mrow+ξ/2-Mrow*AuxiliaryError.branchReserve (chains n).k+
            εold+loss*(Fintype.card α:ℝ)+
            (frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+Sil.Uneven.AuxiliarySource.kappa*mesh+pad)
        let E : ℝ := Cg*(p.control Sp)^2*(1+|analyticv|+height)^degree*Z^(εproj+3*L₂*εshell)*∑n,scalar n
        let rayCost : RayCharacter→RayCharacter→ℝ := fun χ ψ₂=>(∑n,coefficient n*localErrorCost (chains n).p ((chains n).k-1)*
              ∑D∈Ds n,∑z∈partRows false (chains n).υ (if second then ψ₂⁻¹ else χ)
                (internalQ Q η₀) fixedBadMask (geom n).C (geom n).D (geom n).U (geom n).radius,
                ‖normalizedColumn (withHeight (chains n).extracted ((geom n).τ (if second then ψ₂⁻¹ else χ)) analyticv)
                  (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2)
        let hpay (χ ψ₂ : RayCharacter) : rayCost χ ψ₂ ≤ E := by
          exact hz.2 hZ s θ w σ freq analyticv height mesh hcard hM hm hsη hsupper hsb₁ hsb₂
            hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow
            (frequencyLoss Z 32 ξ+reserve) ξ hMmin hreserve hξ hMcap' hslot haff
            chains hk hprime' geom (fun _=>if second then ψ₂⁻¹ else χ) hP hPN p hp₁ hp₂
            (fun n=>(datum n).seed) hE₂ hs Ds hDs hcap P columnWeight hcolumnWeight
        let hnorm := actual_geometry_error_indexed_admitted_columns reflected s R seed Z Mrow amp ξ reserve bs t₀
          (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ index P weight hwgt
          N a ap ha hap hcard hlower hW₁ hW₂ windowProfile χ₀
          (internalQ Q η₀) hQ72 second tₑ u
        let hc (n : Label) :
            errorNormalizedCoefficient P weight (volume source) prime i*
              (K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive=
              coefficient n*localErrorCost (chains n).p ((chains n).k-1) := by
          change errorNormalizedCoefficient P weight (volume source) prime i*
            (K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive=
            (56/(P.card:ℝ))*(weight*(K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive)*
              16*((errorIndex i+1:ℕ)+1:ℝ)/volume source*localErrorCost prime ((errorIndex i+1)-1)
          simp only [Nat.add_sub_cancel]
          unfold errorNormalizedCoefficient
          push_cast
          ring
        let hcolumn := fun (χ ψ₂ : RayCharacter)(n : Label)(D : Ideal O)=>
          let hcolumns := geometryErrorSelectedGeometry_complete_columns reflected s R seed Z Mrow amp ξ reserve bs t₀
            (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁
            (internalQ Q η₀) hQ72 (if second then ψ₂⁻¹ else χ) χ ψ₂ D tₑ u
          let hrows := actual_error_complete_column_rows (datum n).input (datum n).τ
            (datum n).C (datum n).D (datum n).hC (datum n).hD (datum n).inactive
            (datum n).R (datum n).seed D (internalQ Q η₀) (datum n).radius hQ72
            (if second then ψ₂⁻¹ else χ) χ ψ₂ second tₑ u
          let ht : (chains n).extracted.t=v₀ := rfl
          let hheight := congrArg (fun v : ℝ=>
            ∑z∈partRows false (chains n).υ (if second then ψ₂⁻¹ else χ)
              (internalQ Q η₀) fixedBadMask (geom n).C (geom n).D (geom n).U (geom n).radius,
              ‖normalizedColumn (withHeight (chains n).extracted ((geom n).τ (if second then ψ₂⁻¹ else χ))
                (v+2*Real.pi*(u-(if second then -tₑ else tₑ))))
                (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2) ht
          (hrows.symm.trans hcolumns).trans hheight
        hnorm.trans (error_full_ray_column_transport (Ds:=Ds) hc
          (fun χ ψ₂ n D _=>hcolumn χ ψ₂ n D) hpay))))))

end
end OAI.SevenEighths.AuxiliaryErrorReconstruction
