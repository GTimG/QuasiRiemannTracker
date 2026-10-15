/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorNormalizedFullFamily
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorFullPayment
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorScalarTransport
import Candidate.Cycle62.Physical.InitialMass.SecondNormalizedRestriction
import Candidate.Cycle62.Physical.InitialMass.SecondDatumReindex

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open CenteredMomentFirstDiscardedEnergy
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
open Cycle62FinalNatural Cycle62Moment Cycle62FinalError Cycle62FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance errorFullNormalizedPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := errorNormalizedFullFamilySumDecidableEq

/-- The positive normalized sum splits over the actual source menu without
introducing its cardinality; effective weights are local to each block. -/
theorem second_normalized_effective_sigma {α S : Type*}
    [Fintype α] [DecidableEq α] [Fintype S]
    {B : S→Type*} [∀s,Fintype (B s)]
    (d : (s : S)→B s→SecondInputDatum α) (w : (s : S)→B s→ℂ)
    (W : 𝓢(ℝ,ℂ)) (side : Bool) (t u : ℝ) :
    secondNormalizedSum side (fun j : Sigma B=>d j.1 j.2)
      (secondEffectiveWeight (fun j : Sigma B=>(d j.1 j.2).block)
        (fun j=>w j.1 j.2) W) t u=
    ∑s,secondNormalizedSum side (d s)
      (secondEffectiveWeight (fun b=>(d s b).block) (w s) W) t u := by
  simp only [second_normalized_sum_labels,Fintype.sum_sigma,secondEffectiveWeight]

/-- The bound uses the original physical nonzero filter, before applying
ordinary-row restrictions or shifting either Mellin height. -/
def geometryErrorRawNormalizedSum {α : Type*}[Fintype α][DecidableEq α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (prime : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {prime})^(errorIndex i+1))) (υ : Character) (v₀ : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (P : Finset (Ideal O)) (weight : ℝ) (windowProfile : 𝓢(ℝ,ℂ))
    {Label : Type*}[Fintype Label]
    (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N
      hZ bin q prime i Bp υ v₀)(χ₀ : Label→RayCharacter)
    (Q : Ideal O) (side : Bool) (tₑ u : ℝ) : ℝ :=
  let source:=geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q prime i Bp υ v₀
  let datum:=fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N
    hZ bin q prime i Bp υ v₀ hw₁ hw₂ (index n)
  let ordinary:=fun n=>ordinarySecondDatum (datum n) (χ₀ n) Q fixedBadMask
  let c:=errorNormalizedCoefficient P weight (volume source) prime i
  let w:=fun n : Label=>(c:ℂ)*actualSecondBlockWeight source
    ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*
      (Ideal.span {prime})^(errorIndex i+1)) q.1.val.2.1.val
    (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q prime i)
    (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q prime i) Z ξ (index n)
  secondNormalizedSum side ordinary
    (secondEffectiveWeight (fun n=>(ordinary n).block) w windowProfile) tₑ u

def geometryErrorNormalizedLabelsConclusion {α : Type*}[Fintype α][DecidableEq α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (prime : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {prime})^(errorIndex i+1))) (υ : Character) (v₀ : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (P : Finset (Ideal O)) (weight : ℝ) (windowProfile : 𝓢(ℝ,ℂ))
    {Label : Type*}[Fintype Label]
    (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N
      hZ bin q prime i Bp υ v₀)(χ₀ : Label→RayCharacter)
    (Q : Ideal O) (side : Bool) (tₑ u : ℝ) (Ncap : ℕ)(a ap Cg control height εproj L₂ εshell error : ℝ)
    (degree : ℕ)(box : Finset (Fin 4→ℤ)) : Prop :=
  let source:=geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q prime i Bp υ v₀
  let R₂:=(R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {prime})^(errorIndex i+1)
  let first:=geometryFirstLabel s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  let analyticv:=v₀+2*Real.pi*(u-(if side then -tₑ else tₑ))
  geometryErrorRawNormalizedSum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q prime i Bp υ v₀
    hw₁ hw₂ P weight windowProfile index χ₀ Q side tₑ u≤
    (((Fintype.card RayCharacter:ℝ)^2)*(Cg*control^2*(1+|analyticv|+height)^degree*
      Z^(εproj+3*L₂*εshell)))*
    (((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lowerFactor Ncap a ap)*
      ((box.card:ℝ)*∑l∈actualSecondLabels source R₂ q.1.val.2.1.val,
        extractedErrorLabelScalar reflected side first l Z Mrow amp (frequencyLoss Z 32 ξ) reserve
          error εshell (volume s) (volume source) prime (errorIndex i+1)))

private theorem error_scalar_reassoc
    (c w K n count V P Q Z nominal width width₂ cut old card tail mesh pad : ℝ) :
    (c*(w*K*n)*16*count/V)*P*Q*Z^(nominal+width+width₂-cut+old+card+tail+mesh+pad)=
      (c*w*K*n*16*count/V)*P*Q*Z^(nominal+(width+width₂+old+card+tail+mesh+pad)-cut) := by
  have he : nominal+width+width₂-cut+old+card+tail+mesh+pad=
      nominal+(width+width₂+old+card+tail+mesh+pad)-cut := by ring
  rw [he]
  ring

theorem actual_second_scalar_label_cost_nonneg {ι : Type*}[Fintype ι]
    (s : Input ι)(R seed : Ideal O)(hseed : Squarefree seed)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(reflected second : Bool)(first : FirstSourceLabel)
    (Z M amp δ reserve error εshell V : ℝ)(prime : O)(k : ℕ)(hZ : 0≤Z) :
    ∀l∈actualSecondLabels s R seed,0≤extractedErrorLabelScalar reflected second first l
      Z M amp δ reserve error εshell V (volume s) prime k := by
  intro l hl
  exact extracted_error_label_scalar_nonneg reflected second first l
    Z M amp δ reserve error εshell V (volume s) prime k hZ
    (CenteredMomentAmplificationChildInput.volume_pos s)
    (actual_second_labels_gates s R seed hseed hw₁ hw₂ l hl).1

private theorem error_scaled_label_payment {A : Type*}[Fintype A]
    {x r f budget : ℝ}{raw : A→ℝ}(hraw : x≤r*(f*∑a,raw a))
    (cost : A→ℝ)(hc : ∀a,raw a=cost a)
    (hpaid : (∑a,cost a)≤budget)(hfactor : 0≤r*f) : x≤(r*f)*budget := by
  have hs : (∑a,raw a)=∑a,cost a := Finset.sum_congr rfl (fun a _=>hc a)
  exact hraw.trans (by
    rw [←mul_assoc,hs]
    exact mul_le_mul_of_nonneg_left hpaid hfactor)

set_option maxHeartbeats 100000 in
/-- Finite indexed disintegration retains the original label and all four
scale coordinates without constructing an image of dependent block indices. -/
theorem actual_second_indexed_positive_disintegration {ι Label : Type*}
    [Fintype ι][Fintype Label](s : Input ι)(R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (index : Label→ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (hinj : Function.Injective index)
    (hU : ∀n,(index n).2.1∈inactiveSubsets (index n).1.val.val.1 (index n).1.val.val.2)
    (box : Finset (Fin 4→ℤ))(hbox : ∀n,actualSecondDyad s R seed K Tsec Z ξ (index n)∈box)
    (cost : FirstSourceLabel→ℝ)(hcost : ∀l∈actualSecondLabels s R seed,0≤cost l) :
    (∑n,cost (actualSecondSupportedLabel s R seed K Tsec Z ξ (index n) (hU n)))≤
      (box.card:ℝ)*(∑l∈actualSecondLabels s R seed,cost l) := by
  classical
  let code := fun n=>(actualSecondSupportedLabel s R seed K Tsec Z ξ (index n) (hU n),
    actualSecondDyad s R seed K Tsec Z ξ (index n))
  have hcode : Function.Injective code := by
    intro n m h
    apply hinj
    apply actual_second_label_dyad_injective s R seed K Tsec Z ξ
    exact congrArg (fun x : FirstSourceLabel×(Fin 4→ℤ)=>
      ((⟨x.1.1,x.1.2.val⟩ : SecondArithmeticLabel),x.2)) h
  have hsub : Finset.univ.image code⊆actualSecondLabels s R seed×ˢbox := by
    intro x hx
    obtain ⟨n,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨actual_second_supported_label_mem s R seed K Tsec Z ξ
      (index n) (hU n),hbox n⟩
  calc
    _=∑x∈Finset.univ.image code,cost x.1 := by
      rw [Finset.sum_image (fun _ _ _ _ h=>hcode h)]
    _≤∑x∈actualSecondLabels s R seed×ˢbox,cost x.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x hx _
      exact hcost x.1 (Finset.mem_product.mp hx).1
    _=_ := by rw [Finset.sum_product,Finset.sum_comm]; simp

private theorem error_indexed_image_payment {A J : Type*}[DecidableEq A][Fintype J]
    (index : J→A)(hinj : Function.Injective index)(P Q : A→Prop)
    (cost : (a : A)→P a→ℝ)(hp : ∀j,P (index j))(hq : ∀j,Q (index j))
    (bound : ℝ)
    (hpaid : ∀(rows : Finset A)(hr : ∀a∈rows,P a),
      (∀a∈rows,Q a)→(∑a : rows,cost a.val (hr a.val a.property))≤bound) :
    (∑j,cost (index j) (hp j))≤bound := by
  classical
  let rows := Finset.univ.image index
  have hr : ∀a∈rows,P a := by
    intro a ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
    exact hp j
  have hqr : ∀a∈rows,Q a := by
    intro a ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
    exact hq j
  let f := fun a=>if h : P a then cost a h else 0
  have hl : (∑j,cost (index j) (hp j))=∑j,f (index j) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [f,dif_pos (hp j)]
  have hright : (∑a : rows,cost a.val (hr a.val a.property))=∑a∈rows,f a := by
    rw [←Finset.sum_coe_sort rows]
    apply Finset.sum_congr rfl
    intro a _
    simp only [f,dif_pos (hr a.val a.property)]
  have hi : (∑j,f (index j))=∑a∈rows,f a := by
    dsimp only [rows]
    rw [Finset.sum_image (fun _ _ _ _ h=>hinj h)]
  exact (hl.trans hi).trans hright.symm |>.le.trans (hpaid rows hr hqr)

section IndexedScalar
variable {α : Type*}[Fintype α][DecidableEq α]
variable {Label : Type*}[Fintype Label]
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (p : O) (i : Fin 3)
variable (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (hp : p≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
      IsCoprime (Ideal.span {p}) I)
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

variable (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : ∀n : Label,(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ (index n)).block.value ballProfile≠0)

set_option maxHeartbeats 100000 in
set_option linter.defProp false in
/-- Original nonzero blocks are paid by supported labels in a shared four-scale box. -/
theorem actual_geometry_error_indexed_scalar_payment
    (hinj : Function.Injective index)(second : Bool)(P : Finset (Ideal O))
    (weight lf error εshell : ℝ)
    (hweight : 0≤weight)(hlf : 0<lf)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀n : Label,actualSecondDyad
      (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)
      ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1))
      q.1.val.2.1.val (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
      (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ (index n)∈box) :
    let source:=geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v
    let R₂:=(R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
    let first:=geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
    (∑n : Label,geometryErrorColumnScalar reflected s R seed Z Mrow amp ξ reserve b t N
      hZ bin q p i Bp υ v hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁ P weight lf error εshell)≤
      ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
        ((box.card:ℝ)*∑l∈actualSecondLabels source R₂ q.1.val.2.1.val,
          extractedErrorLabelScalar reflected second first l Z Mrow amp (frequencyLoss Z 32 ξ)
            reserve error εshell (volume s) (volume source) p (errorIndex i+1)) := by
  intro source₀ R₀ first₀
  classical
  apply @error_indexed_image_payment
    (GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
    Label (Classical.decEq _) inferInstance index hinj
    (fun n=>(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N
      hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
    (fun n=>actualSecondDyad
      (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)
      ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1))
      q.1.val.2.1.val (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
      (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ n∈box)
    (fun n hn=>geometryErrorColumnScalar reflected s R seed Z Mrow amp ξ reserve b t N
      hZ bin q p i Bp υ v hw₁ hw₂ n hn second hp hcop ψ hυ hf₁ P weight lf error εshell)
    hne hbox
  intro rows hrows hrowsbox
  exact actual_geometry_error_scalar_disintegration reflected s R seed Z Mrow amp ξ reserve b t N
    hZ bin q p i Bp υ v hw₁ hw₂ hp hcop ψ hυ hf₁ rows hrows box hrowsbox
    second P weight lf error εshell hweight hlf

end IndexedScalar

set_option maxHeartbeats 20000 in
theorem actual_error_indexed_normalized_to_datum_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K)
    (index : Label→ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0≤weight) (prime : O) (i : Fin 3)
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (hcard : Fintype.card α≤N) (hlower : a≤s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ap≤x) (hW₂ : ∀x,s.W₂ x≠0→ap≤x)
    (W : 𝓢(ℝ,ℂ)) (χ₀ : Label→RayCharacter) (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (second : Bool) (t u : ℝ) :
    let d := fun n=>actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK (index n)
    let datum := fun n=>ordinarySecondDatum (d n) (χ₀ n) Q fixedBadMask
    let c := errorNormalizedCoefficient P weight (volume s) prime i
    let w := fun n=>(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ (index n)
    secondNormalizedSum second datum
      (secondEffectiveWeight (fun n=>(datum n).block) w W) t u≤
      ∑χ : RayCharacter,∑ψ : RayCharacter,∑n,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if second then
            ∑z∈partRows false (d n).input.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight (d n).input ((d n).τ ψ⁻¹) ((d n).input.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD (d n).R (d n).seed D z‖^2
           else
            ∑z∈partRows false (d n).input.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight (d n).input ((d n).τ χ) ((d n).input.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC (d n).R (d n).seed D z‖^2) := by
  intro d datum c w
  convert actual_error_indexed_normalized_to_admitted_columns slots s R seed hseed hz₁ hz₂
    K Tsec Z ξ hK index P weight hw prime i N a ap ha hap hcard hlower hW₁ hW₂
    W χ₀ Q hQ second t u using 1 <;> rfl

set_option maxHeartbeats 20000 in
theorem actual_error_indexed_given_datum_normalized_to_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K)
    (index : Label→ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (d : Label→SecondInputDatum α)
    (hd : d=fun n=>actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK (index n))
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0≤weight) (prime : O) (i : Fin 3)
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (hcard : Fintype.card α≤N) (hlower : a≤s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ap≤x) (hW₂ : ∀x,s.W₂ x≠0→ap≤x)
    (W : 𝓢(ℝ,ℂ)) (χ₀ : Label→RayCharacter) (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (second : Bool) (t u : ℝ) :
    let datum := fun n=>ordinarySecondDatum (d n) (χ₀ n) Q fixedBadMask
    let c := errorNormalizedCoefficient P weight (volume s) prime i
    let w := fun n=>(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ (index n)
    secondNormalizedSum second datum
      (secondEffectiveWeight (fun n=>(datum n).block) w W) t u≤
      ∑χ : RayCharacter,∑ψ : RayCharacter,∑n,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if second then
            ∑z∈partRows false (d n).input.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight (d n).input ((d n).τ ψ⁻¹) ((d n).input.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD (d n).R (d n).seed D z‖^2
           else
            ∑z∈partRows false (d n).input.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight (d n).input ((d n).τ χ) ((d n).input.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC (d n).R (d n).seed D z‖^2) := by
  subst d
  exact actual_error_indexed_normalized_to_datum_columns slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK index
    P weight hw prime i N a ap ha hap hcard hlower hW₁ hW₂ W χ₀ Q hQ second t u



set_option maxHeartbeats 20000 in
theorem actual_geometry_error_normalized_to_datum_columns {α : Type*}[Fintype α][DecidableEq α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (prime : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {prime})^(errorIndex i+1))) (υ : Character) (v₀ : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (P : Finset (Ideal O)) (weight : ℝ) (windowProfile : 𝓢(ℝ,ℂ))
    {Label : Type*}[Fintype Label]
    (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N
      hZ bin q prime i Bp υ v₀)(χ₀ : Label→RayCharacter)
    (Q : Ideal O) (side : Bool) (tₑ u : ℝ)
    (Ncap : ℕ)(a ap : ℝ)(ha : 0<a)(hap : 0<ap)(hcard : Fintype.card α≤Ncap)
    (hlower : a≤s.lower)(hW₁ : ∀x,s.W₁ x≠0→ap≤x)(hW₂ : ∀x,s.W₂ x≠0→ap≤x)
    (hwgt : 0≤weight)(hQ : Q≤Ideal.span {(72:O)}) :
    let source := geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q prime i Bp υ v₀
    let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q prime i
    let d := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q prime i Bp υ v₀ hw₁ hw₂ (index n)
    let c := errorNormalizedCoefficient P weight (volume source) prime i
    geometryErrorRawNormalizedSum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q prime i Bp υ v₀ hw₁ hw₂ P weight windowProfile index χ₀ Q side tₑ u≤
      ∑χ : RayCharacter,∑ψ : RayCharacter,∑n,
        (c*(K/lowerFactor Ncap a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if side then
            ∑z∈partRows false (d n).input.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight (d n).input ((d n).τ ψ⁻¹) ((d n).input.t+2*Real.pi*(u-(-tₑ))))
                (d n).D (d n).hD (d n).R (d n).seed D z‖^2
           else
            ∑z∈partRows false (d n).input.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight (d n).input ((d n).τ χ) ((d n).input.t+2*Real.pi*(u-tₑ)))
                (d n).C (d n).hC (d n).R (d n).seed D z‖^2) := by
  intro source K d c
  exact actual_error_indexed_given_datum_normalized_to_columns (α:=liveIndices q.2.val)
    (liveIndices (errorActiveAllocation
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val)
    source
    ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {prime})^(errorIndex i+1))
    q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property)
    hw₁ hw₂ K
    (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q prime i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q prime i)
    index d (by funext n; exact Eq.refl _) P weight hwgt prime i Ncap a ap ha hap
    ((Fintype.card_subtype_le _).trans hcard) hlower hW₁ hW₂ windowProfile χ₀ Q hQ side tₑ u

section Columns
variable {α : Type*}[Fintype α][DecidableEq α]
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (p : O) (i : Fin 3)
variable (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (hp : p≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
      IsCoprime (Ideal.span {p}) I)
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

variable (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
variable (second : Bool)
set_option maxHeartbeats 20000 in
theorem actual_geometry_error_admitted_columns_eq
    (Q : Ideal O)(hQ : Q≤Ideal.span {(72:O)})
    (χ₀ χ ψ₂ : RayCharacter)(L : Ideal O)(tₑ u : ℝ) :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
    let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
    let hE : Supported chain.E₂ := by
      cases second with
      | false => exact d.hC
      | true => exact d.hD
    (if second then
      ∑z∈partRows false d.input.η ψ₂⁻¹ Q fixedBadMask d.C d.D d.inactive d.radius,
        ‖normalizedColumn (withHeight d.input (d.τ ψ₂⁻¹) (d.input.t+2*Real.pi*(u-(-tₑ))))
          d.D d.hD d.R d.seed L z‖^2
    else
      ∑z∈partRows false d.input.η χ Q fixedBadMask d.C d.D d.inactive d.radius,
        ‖normalizedColumn (withHeight d.input (d.τ χ) (d.input.t+2*Real.pi*(u-tₑ)))
          d.C d.hC d.R d.seed L z‖^2)=
    ∑z∈partRows false chain.υ (if second then ψ₂⁻¹ else χ) Q fixedBadMask
      g.C g.D g.U g.radius,
      ‖normalizedColumn (withHeight chain.extracted (g.τ (if second then ψ₂⁻¹ else χ))
        (v+2*Real.pi*(u-(if second then -tₑ else tₑ))))
        chain.E₂ hE chain.R₂ d.seed L z‖^2 := by
  intro d chain g hE
  have hcolumns := geometryErrorSelectedGeometry_complete_columns reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hw₁ hw₂ n hne second hp hcop ψ hυ hf₁ Q hQ χ₀ χ ψ₂ L tₑ u
  have hrows := actual_error_complete_column_rows d.input d.τ d.C d.D d.hC d.hD d.inactive
    d.R d.seed L Q d.radius hQ χ₀ χ ψ₂ second tₑ u
  have ht : chain.extracted.t=v := rfl
  have hheight := congrArg (fun v : ℝ=>
    ∑z∈partRows false chain.υ (if second then ψ₂⁻¹ else χ) Q fixedBadMask
      g.C g.D g.U g.radius,
      ‖normalizedColumn (withHeight chain.extracted (g.τ (if second then ψ₂⁻¹ else χ))
        (v+2*Real.pi*(u-(if second then -tₑ else tₑ))))
        chain.E₂ hE chain.R₂ d.seed L z‖^2) ht
  exact @Eq.trans ℝ _ _ _ (@Eq.trans ℝ _ _ _ hrows.symm hcolumns) hheight
end Columns

private theorem error_normalized_ray_transport {Label : Type*}[Fintype Label]
    {Ds : Label→Finset (Ideal O)} {rawCoefficient paidCoefficient : Label→ℝ}
    {raw paid : RayCharacter→RayCharacter→Label→Ideal O→ℝ} {E : ℝ}
    (hc : ∀n,rawCoefficient n=paidCoefficient n)
    (hcolumn : ∀χ ψ n D,D∈Ds n → raw χ ψ n D=paid χ ψ n D)
    (hpaid : ∀χ ψ,(∑n,paidCoefficient n*∑D∈Ds n,paid χ ψ n D)≤E) :
    (∑χ : RayCharacter,∑ψ : RayCharacter,∑n,rawCoefficient n*∑D∈Ds n,raw χ ψ n D)≤
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
    _≤∑_χ : RayCharacter,∑_ψ : RayCharacter,E :=
      Finset.sum_le_sum (fun χ _=>Finset.sum_le_sum (fun ψ _=>hpaid χ ψ))
    _=((Fintype.card RayCharacter:ℝ)^2)*E := by simp; ring

private theorem error_volume_withHeight {ι : Type*}[Fintype ι]
    (s : Input ι)(η : Character)(t : ℝ) :
    CenteredMomentAmplificationChildInput.volume (withHeight s η t)=
      CenteredMomentAmplificationChildInput.volume s := rfl

private theorem error_height_volume_sum_transport {Label : Type*}[Fintype Label]
    {ι : Label→Type*}[∀j,Fintype (ι j)] (s : (j : Label)→Input (ι j))
    (η : Label→Character)(v : ℝ)(c x y r₁ r₂ r₃ : Label→ℝ){F : ℝ}
    (h : (∑j,c j/CenteredMomentAmplificationChildInput.volume (withHeight (s j) (η j) v)*x j*y j)≤
      F*(∑j,c j/CenteredMomentAmplificationChildInput.volume (withHeight (s j) (η j) v)*r₁ j*r₂ j*r₃ j)) :
    (∑j,c j/CenteredMomentAmplificationChildInput.volume (s j)*x j*y j)≤
      F*(∑j,c j/CenteredMomentAmplificationChildInput.volume (s j)*r₁ j*r₂ j*r₃ j) := by
  simpa only [error_volume_withHeight] using h

private theorem error_label_coefficient_nonneg (P : Finset (Ideal O)) (w lf : ℝ) (k : ℕ)
    (hw : 0≤w)(hlf : 0<lf) : 0≤(56/(P.card:ℝ))*w*16*(k:ℝ)/lf := by positivity


set_option linter.defProp false in
set_option linter.unusedVariables false in
def geometryErrorNormalizedDynamicSpec {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(B ap bp Bmask L lo hi Mcap εold loss : ℝ)(ηseed : Character)
    (bs εwidth εpad Mmin window pad εshell : ℝ)(N : ℕ)(Cs L₂ εproj Cg : ℝ)
    (Sp : Finset (ℕ×ℕ))(degree : ℕ)(η₀ : Character)(Q : Ideal O)(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ)(height mesh : ℝ)
    (hcard : Fintype.card α≤N)(hM : ∀j,s.M j≤Cs)
    (hm : Matches M H hH s η₀ θ w σ freq W B Z)
    (hsη : s.η=ηseed)(hsupper : s.upper≤bs)(hsb₁ : s.b₁=bp)(hsb₂ : s.b₂=bp)
    (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold)
    (hmesh : 0≤mesh)(hwm : ∀j,w j≤mesh)(hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤hi)
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
    (hOrig : ∀second j,Cycle62.Physical.sourcePlainScales s.toData.toSource second j≤Z^L)
    (hwin : ∀j,logWindow (s.lo j) (s.hi j)≤window)
    (Mrow ξ : ℝ)(hMmin : Mmin≤Mrow)(hξ : 0≤ξ)
    (hMcap' : Mrow+εwidth*Mrow+ξ/2≤Mcap)
    (hslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
    (haff : length Z s.X₁+length Z s.X₂+Cycle62.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle62.Arithmetic.B*Mrow),
  let cell := Cycle62.Arithmetic.cellUpper (Cycle62.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
  let amp := Mrow*Cycle62.Arithmetic.amp cell
  ∀(reserve : ℝ)(hreserve : 0≤frequencyLoss Z 32 ξ+reserve)
    (reflected : Bool)(R seed : Ideal O)(t₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (prime : O)(i : Fin 3)(hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first).slots j→IsCoprime (Ideal.span {prime}) I)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first)).pools ((Ideal.span {prime})^(errorIndex i+1)))
    (υ : Character)(v₀ : ℝ)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) ψ)
      fixedBadMask prime (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient first.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) R s.ν s.W s.P≠0)
    (hprime : 3*amp/4≤Real.logb Z (normValue prime)),
  ∀{Label : Type v} [Fintype Label]
    (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀),
  let datum := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
  ∀(hne : ∀n : Label,(datum n).block.value ballProfile≠0)(hinj : Function.Injective index)(second : Bool),
  let alloc := fun n=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second
  let chains := fun n=>geometryErrorChain reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀ hp hcop
    (if second then (datum n).D else (datum n).C) (datum n).R (alloc n)

  ∀(hP : ∀n,(chains n).R₂*(chains n).E₂≠0)
    (hPN : ∀n,(((chains n).R₂*(chains n).E₂).absNorm:ℝ)≤Z^Bmask)
    (p : Profiles ap bp)(hp₁ : s.W₁=p.profile 0)(hp₂ : s.W₂=p.profile 1)
    (a : ℝ)(ha : 0<a)(hlower : a≤s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ap≤x)(hW₂ : ∀x,s.W₂ x≠0→ap≤x)
    (windowProfile : 𝓢(ℝ,ℂ))(χ₀ : Label→RayCharacter)
    (P : Finset (Ideal O))(weight : ℝ)(hwgt : 0≤weight)
    (hcap : ∀n D,D∈(datum n).block.divisors.filter Squarefree→(D.absNorm:ℝ)≤Z^L₂)
    (tₑ u : ℝ),
  ∀(box : Finset (Fin 4→ℤ))
    (hbox : ∀n : Label,actualSecondDyad
      (geometryErrorChild reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀)
      ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val)*
          (Ideal.span {prime})^(errorIndex i+1)) first.1.val.2.1.val
      (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i)
      (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve bs (Fintype.card α) hZ bin first prime i)
      Z ξ (index n)∈box),
  let error:=εwidth*Mrow+ξ/2+εold+loss*(Fintype.card α:ℝ)+
    (frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+(3/4)*mesh+pad
  geometryErrorNormalizedLabelsConclusion reflected s R seed Z Mrow amp ξ reserve bs t₀
    (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ P weight windowProfile
    index χ₀ (internalQ Q η₀) second tₑ u N a ap Cg (p.control Sp) height
    εproj L₂ εshell error degree box


set_option linter.defProp false in
def geometryErrorProjectorPaidSpec {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(B ap bp Bmask L lo hi Mcap εold loss : ℝ)(ηseed : Character)
    (bs εwidth εpad Mmin window pad εshell : ℝ)(N : ℕ)(Cs L₂ εproj Cg : ℝ)
    (Sp : Finset (ℕ×ℕ))(degree : ℕ)(η₀ : Character)(Q : Ideal O)(Z : ℝ) : Prop :=
    ∀(_hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤bs → s.b₁=bp → s.b₂=bp →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤mesh → (∀j,w j≤mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) →
      (∀second j,Cycle62.Physical.sourcePlainScales s.toData.toSource second j≤Z^L) →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
    ∀(Mrow omega ξ : ℝ),Mmin≤Mrow → 0≤omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle62.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle62.Arithmetic.B*Mrow →
    let cell := Cycle62.Arithmetic.cellUpper (Cycle62.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle62.Arithmetic.amp cell
    ∀{Label : Type v}[Fintype Label],∀q : Label→Chain s,
    (∀j,(q j).k=1 ∨ (q j).k=6 ∨ (q j).k=7) →
    (∀j,3*amp/4≤Real.logb Z (normValue (q j).p)) →
    ∀g : (j : Label)→Geometry s (q j) Z Mrow amp omega ξ bs (fixedFactor:ℝ) (Fintype.card α),
    ∀(χ : Label→RayFourExpansion.RayCharacter)(_hP : ∀j,(q j).R₂*(q j).E₂≠0)
      (_hPN : ∀j,(((q j).R₂*(q j).E₂).absNorm:ℝ)≤Z^Bmask),
    let src := fun j=>withHeight (q j).extracted ((g j).τ (χ j)) v
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Label→Ideal O)(hE₂ : ∀j,Supported (q j).E₂),(∀j,seed j∣(q j).E₂) →
    ∀Ds : Label→Finset (Ideal O),(∀j D,D∈Ds j→Squarefree D) →
      (∀j D,D∈Ds j→(D.absNorm:ℝ)≤Z^L₂) →
    ∀(P : Finset (Ideal O))(weight : Label→ℝ),(∀j,0≤weight j) →
    let coefficient := fun j=>(56/(P.card:ℝ))*weight j*16*((q j).k+1:ℝ)/volume (src j)
    let rows := fun j=>partRows false (q j).υ (χ j) (internalQ Q η₀)
      fixedBadMask (g j).C (g j).D (g j).U (g j).radius
    (∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
      (∑D∈Ds j,∑z∈rows j,‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2))≤
      Cg*(p.control Sp)^2*(1+|v|+height)^degree*Z^(εproj+3*L₂*εshell)*
        ∑j,coefficient j*Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
          ((q j).E₂.absNorm:ℝ)^(εshell-1)*
          Z^((g j).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (q j).k+
            εold+loss*(Fintype.card α:ℝ)+(omega+εpad*Mrow)/6+(3/4)*mesh+pad)



private theorem error_datum_selected_support {ι : Type*}[Fintype ι][DecidableEq ι]
    (d : SecondInputDatum ι)(side : Bool) : Supported (if side then d.D else d.C) := by
  cases side with
  | false => exact d.hC
  | true => exact d.hD

private def error_complete_paid_rays_bound {α : Type*}{Label : Type*}[Fintype α][Fintype Label]
    (s : Input α)(chains : Label→Chain s)(Z Mrow amp omega ξ bs : ℝ)(N : ℕ)
    (geom : (n : Label)→Geometry s (chains n) Z Mrow amp omega ξ bs (fixedFactor:ℝ) N)
    (hE₂ : ∀n,Supported (chains n).E₂)(seed : Label→Ideal O)(Ds : Label→Finset (Ideal O))
    (P : Finset (Ideal O))(columnWeight : Label→ℝ)(Q : Ideal O)(second : Bool)(analyticv F : ℝ)
    (r₁ r₂ r₃ : Label→ℝ) : Prop :=
  let src := fun (χ ψ₂ : RayCharacter)(n : Label)=>withHeight (chains n).extracted
    ((geom n).τ (if second then ψ₂⁻¹ else χ)) analyticv
  let rows := fun (χ ψ₂ : RayCharacter)(n : Label)=>partRows false (chains n).υ
    (if second then ψ₂⁻¹ else χ) Q fixedBadMask
    (geom n).C (geom n).D (geom n).U (geom n).radius
  let cheight := fun (χ ψ₂ : RayCharacter)(n : Label)=>
    (56/(P.card:ℝ))*columnWeight n*16*((chains n).k+1:ℝ)/volume (src χ ψ₂ n)
  ∀(χ ψ₂ : RayCharacter),
    (∑n : Label,cheight χ ψ₂ n*localErrorCost (chains n).p ((chains n).k-1)*
      (∑D∈Ds n,∑z∈rows χ ψ₂ n,‖normalizedColumn (src χ ψ₂ n)
        (chains n).E₂ (hE₂ n) (chains n).R₂ (seed n) D z‖^2))≤
    F*∑n : Label,cheight χ ψ₂ n*r₁ n*r₂ n*r₃ n

set_option linter.defProp false in
set_option linter.unusedVariables false in
def geometryErrorConcretePaidColumnsSpec {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(B ap bp Bmask L lo hi Mcap εold loss : ℝ)(ηseed : Character)
    (bs εwidth εpad Mmin window pad εshell : ℝ)(N : ℕ)(Cs L₂ εproj Cg : ℝ)
    (Sp : Finset (ℕ×ℕ))(degree : ℕ)(η₀ : Character)(Q : Ideal O)(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ)(height mesh : ℝ)
    (hcard : Fintype.card α≤N)(hM : ∀j,s.M j≤Cs)
    (hm : Matches M H hH s η₀ θ w σ freq W B Z)
    (hsη : s.η=ηseed)(hsupper : s.upper≤bs)(hsb₁ : s.b₁=bp)(hsb₂ : s.b₂=bp)
    (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold)
    (hmesh : 0≤mesh)(hwm : ∀j,w j≤mesh)(hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤hi)
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
    (hOrig : ∀second j,Cycle62.Physical.sourcePlainScales s.toData.toSource second j≤Z^L)
    (hwin : ∀j,logWindow (s.lo j) (s.hi j)≤window)
    (Mrow ξ : ℝ)(hMmin : Mmin≤Mrow)(hξ : 0≤ξ)
    (hMcap' : Mrow+εwidth*Mrow+ξ/2≤Mcap)
    (hslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
    (haff : length Z s.X₁+length Z s.X₂+Cycle62.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle62.Arithmetic.B*Mrow),
  let cell := Cycle62.Arithmetic.cellUpper (Cycle62.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
  let amp := Mrow*Cycle62.Arithmetic.amp cell
  ∀(reserve : ℝ)(hreserve : 0≤frequencyLoss Z 32 ξ+reserve)
    (reflected : Bool)(R seed : Ideal O)(t₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (prime : O)(i : Fin 3)(hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first).slots j→IsCoprime (Ideal.span {prime}) I)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first)).pools ((Ideal.span {prime})^(errorIndex i+1)))
    (υ : Character)(v₀ : ℝ)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) ψ)
      fixedBadMask prime (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient first.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) R s.ν s.W s.P≠0)
    (hprime : 3*amp/4≤Real.logb Z (normValue prime)),
  ∀{Label : Type v} [Fintype Label]
    (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀),
  let datum := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
  ∀(hne : ∀n : Label,(datum n).block.value ballProfile≠0)(hinj : Function.Injective index)(second : Bool),
  let alloc := fun n=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second
  let chains := fun n=>geometryErrorChain reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀ hp hcop
    (if second then (datum n).D else (datum n).C) (datum n).R (alloc n)

  ∀(hP : ∀n,(chains n).R₂*(chains n).E₂≠0)
    (hPN : ∀n,(((chains n).R₂*(chains n).E₂).absNorm:ℝ)≤Z^Bmask)
    (p : Profiles ap bp)(hp₁ : s.W₁=p.profile 0)(hp₂ : s.W₂=p.profile 1)
    (a : ℝ)(ha : 0<a)(hlower : a≤s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ap≤x)(hW₂ : ∀x,s.W₂ x≠0→ap≤x)
    (windowProfile : 𝓢(ℝ,ℂ))(χ₀ : Label→RayCharacter)
    (P : Finset (Ideal O))(weight : ℝ)(hwgt : 0≤weight)
    (hcap : ∀n D,D∈(datum n).block.divisors.filter Squarefree→(D.absNorm:ℝ)≤Z^L₂)
    (tₑ u : ℝ),
  ∀(box : Finset (Fin 4→ℤ))
    (hbox : ∀n : Label,actualSecondDyad
      (geometryErrorChild reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀)
      ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val)*
          (Ideal.span {prime})^(errorIndex i+1)) first.1.val.2.1.val
      (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i)
      (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve bs (Fintype.card α) hZ bin first prime i)
      Z ξ (index n)∈box),
  let error:=εwidth*Mrow+ξ/2+εold+loss*(Fintype.card α:ℝ)+
    (frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+(3/4)*mesh+pad
  let geom := fun n : Label=>geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve bs t₀
    (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁
  let analyticv := v₀+2*Real.pi*(u-(if second then -tₑ else tₑ))
  let Ds := fun n=>(datum n).block.divisors.filter Squarefree
  let hE₂ (n : Label) : Supported (chains n).E₂ :=
    error_datum_selected_support (datum n) second
  let source := geometryErrorChild reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀
  let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i
  let columnWeight : Label→ℝ := fun n=>weight*(K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive
  error_complete_paid_rays_bound s chains Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ bs
    (Fintype.card α) geom hE₂ (fun n=>(datum n).seed) Ds P columnWeight (internalQ Q η₀) second analyticv
    (Cg*(p.control Sp)^2*(1+|analyticv|+height)^degree*Z^(εproj+3*L₂*εshell))
    (fun n=>Z^(errorRemoval (chains n).p Z (chains n).k-errorMoving (chains n).p Z (chains n).k))
    (fun n=>((chains n).E₂.absNorm:ℝ)^(εshell-1))
    (fun n=>Z^((geom n).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (chains n).k+
      εold+loss*(Fintype.card α:ℝ)+(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+(3/4)*mesh+pad))

set_option maxHeartbeats 20000 in
theorem actual_geometry_error_projector_to_concrete_paid_columns {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(B ap bp Bmask L lo hi Mcap εold loss : ℝ)(ηseed : Character)
    (bs εwidth εpad Mmin window pad εshell : ℝ)(N : ℕ)(Cs L₂ εproj Cg : ℝ)
    (Sp : Finset (ℕ×ℕ))(degree : ℕ)(η₀ : Character)(Q : Ideal O)(Z : ℝ)
    (hCg : 0<Cg)(hap : 0<ap)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hpaid : geometryErrorProjectorPaidSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z) :
    geometryErrorConcretePaidColumnsSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z := by
  classical
  intro hZ s θ w σ freq height mesh hcard hM hm hsη hsupper hsb₁ hsb₂
    hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow ξ hMmin hξ hMcap' hslot haff
    cell amp reserve hreserve reflected R seed t₀ bin first prime i hp hcop Bp υ v₀ hw₁ hw₂ ψ hυ hf₁
    hprime Label _ index datum hne hinj second alloc chains hP hPN p hp₁ hp₂ a ha hlower
    hW₁ hW₂ windowProfile χ₀ P weight hwgt hcap tₑ u box hbox error
    geom analyticv Ds hE₂ source K columnWeight χ ψ₂
  have hDs : ∀n D,D∈Ds n→Squarefree D := fun _ _ hD=>(Finset.mem_filter.mp hD).2
  have hk (n : Label) : (chains n).k=1 ∨ (chains n).k=6 ∨ (chains n).k=7 := by
    change errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7
    fin_cases i <;> norm_num [errorIndex]
  have hprime' (n : Label) : 3*amp/4≤Real.logb Z (normValue (chains n).p) := hprime
  have hs (n : Label) : (datum n).seed∣(chains n).E₂ := by
    have hg := actual_geometry_error_seed_gates reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
    cases second with
    | false => exact hg.1
    | true => exact hg.2
  have hcolumnWeight : ∀n,0≤columnWeight n := by
    intro n
    have hK : 0<K := actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i
    have hlf : 0<lowerFactor N a ap := lowerFactor_pos N a ap ha hap
    have hn : 0<normalizer (datum n).C (datum n).D (datum n).inactive :=
      normalizer_pos (datum n).C (datum n).D (datum n).hC (datum n).inactive
    exact mul_nonneg (mul_nonneg hwgt (div_nonneg hK.le hlf.le)) hn.le
  have hbase := @hpaid hZ s θ w σ freq analyticv height mesh hcard hM hm hsη hsupper hsb₁ hsb₂
    hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow
    (frequencyLoss Z 32 ξ+reserve) ξ hMmin hreserve hξ hMcap' hslot haff
  have hchain := @hbase Label inferInstance chains hk hprime'
  have hgeom := hchain geom (fun _=>if second then ψ₂⁻¹ else χ) hP hPN
  have hprofile := hgeom p hp₁ hp₂
  have hseedPaid := hprofile (fun n=>(datum n).seed) hE₂ hs
  have hprojector := hseedPaid Ds hDs hcap
  exact hprojector P columnWeight hcolumnWeight

set_option maxHeartbeats 200000 in
theorem actual_geometry_error_normalized_from_concrete_paid_columns {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(B ap bp Bmask L lo hi Mcap εold loss : ℝ)(ηseed : Character)
    (bs εwidth εpad Mmin window pad εshell : ℝ)(N : ℕ)(Cs L₂ εproj Cg : ℝ)
    (Sp : Finset (ℕ×ℕ))(degree : ℕ)(η₀ : Character)(Q : Ideal O)(Z : ℝ)
    (hCg : 0<Cg)(hap : 0<ap)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hpaid : geometryErrorConcretePaidColumnsSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z) :
    geometryErrorNormalizedDynamicSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z := by
  classical
  intro hZ s θ w σ freq height mesh hcard hM hm hsη hsupper hsb₁ hsb₂
    hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow ξ hMmin hξ hMcap' hslot haff
    cell amp reserve hreserve reflected R seed t₀ bin first prime i hp hcop Bp υ v₀ hw₁ hw₂ ψ hυ hf₁
    hprime Label _ index datum hne hinj second alloc chains hP hPN p hp₁ hp₂ a ha hlower
    hW₁ hW₂ windowProfile χ₀ P weight hwgt hcap tₑ u box hbox error
  let geom : (n : Label)→Geometry s (chains n) Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ bs (fixedFactor:ℝ) (Fintype.card α) := fun n=>geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve bs t₀
    (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁
  let analyticv := v₀+2*Real.pi*(u-(if second then -tₑ else tₑ))
  let Ds := fun n=>(datum n).block.divisors.filter Squarefree
  have hDs : ∀n D,D∈Ds n→Squarefree D := fun _ _ hD=>(Finset.mem_filter.mp hD).2
  have hk (n : Label) : (chains n).k=1 ∨ (chains n).k=6 ∨ (chains n).k=7 := by
    change errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7
    fin_cases i <;> norm_num [errorIndex]
  have hprime' (n : Label) : 3*amp/4≤Real.logb Z (normValue (chains n).p) := hprime
  have hE₂ (n : Label) : Supported (chains n).E₂ := by
    cases second with
    | false => exact (datum n).hC
    | true => exact (datum n).hD
  have hs (n : Label) : (datum n).seed∣(chains n).E₂ := by
    have hg := actual_geometry_error_seed_gates reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
    cases second with
    | false => exact hg.1
    | true => exact hg.2
  let source := geometryErrorChild reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀
  let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i
  let columnWeight : Label→ℝ := fun n=>weight*(K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive
  have hcolumnWeight : ∀n,0≤columnWeight n := by
    intro n
    have hK : 0<K := actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i
    have hlf : 0<lowerFactor N a ap := lowerFactor_pos N a ap ha hap
    have hn : 0<normalizer (datum n).C (datum n).D (datum n).inactive :=
      normalizer_pos (datum n).C (datum n).D (datum n).hC (datum n).inactive
    exact mul_nonneg (mul_nonneg hwgt (div_nonneg hK.le hlf.le)) hn.le
  let coefficient : Label→ℝ := fun n=>(56/(P.card:ℝ))*columnWeight n*16*((chains n).k+1:ℝ)/volume (chains n).extracted
  let src := fun (χ ψ₂ : RayCharacter)(n : Label)=>withHeight (chains n).extracted
    ((geom n).τ (if second then ψ₂⁻¹ else χ)) analyticv
  let rows := fun (χ ψ₂ : RayCharacter)(n : Label)=>partRows false (chains n).υ
    (if second then ψ₂⁻¹ else χ) (internalQ Q η₀) fixedBadMask
    (geom n).C (geom n).D (geom n).U (geom n).radius
  let cheight := fun (χ ψ₂ : RayCharacter)(n : Label)=>
    (56/(P.card:ℝ))*columnWeight n*16*((chains n).k+1:ℝ)/volume (src χ ψ₂ n)
  have hpayRaw (χ ψ₂ : RayCharacter) :
      (∑n : Label,cheight χ ψ₂ n*localErrorCost (chains n).p ((chains n).k-1)*
        (∑D∈Ds n,∑z∈rows χ ψ₂ n,‖normalizedColumn (src χ ψ₂ n)
          (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2))≤
      Cg*(p.control Sp)^2*(1+|analyticv|+height)^degree*Z^(εproj+3*L₂*εshell)*
        ∑n : Label,cheight χ ψ₂ n*
          Z^(errorRemoval (chains n).p Z (chains n).k-errorMoving (chains n).p Z (chains n).k)*
          ((chains n).E₂.absNorm:ℝ)^(εshell-1)*
          Z^((geom n).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (chains n).k+
            εold+loss*(Fintype.card α:ℝ)+(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+(3/4)*mesh+pad) := by
    exact @hpaid hZ s θ w σ freq height mesh hcard hM hm hsη hsupper hsb₁ hsb₂
      hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow ξ hMmin hξ hMcap' hslot haff
      reserve hreserve reflected R seed t₀ bin first prime i hp hcop Bp υ v₀ hw₁ hw₂ ψ hυ hf₁
      hprime Label inferInstance index hne hinj second hP hPN p hp₁ hp₂ a ha hlower
      hW₁ hW₂ windowProfile χ₀ P weight hwgt hcap tₑ u box hbox χ ψ₂
  have hpay (χ ψ₂ : RayCharacter) :
      (∑n : Label,coefficient n*localErrorCost (chains n).p ((chains n).k-1)*
        (∑D∈Ds n,∑z∈rows χ ψ₂ n,‖normalizedColumn (src χ ψ₂ n)
          (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2))≤
      Cg*(p.control Sp)^2*(1+|analyticv|+height)^degree*Z^(εproj+3*L₂*εshell)*
        ∑n : Label,coefficient n*
          Z^(errorRemoval (chains n).p Z (chains n).k-errorMoving (chains n).p Z (chains n).k)*
          ((chains n).E₂.absNorm:ℝ)^(εshell-1)*
          Z^((geom n).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (chains n).k+
            εold+loss*(Fintype.card α:ℝ)+(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+(3/4)*mesh+pad) := by
    exact error_height_volume_sum_transport
      (fun n : Label=>(chains n).extracted)
      (fun n=>(geom n).τ (if second then ψ₂⁻¹ else χ)) analyticv
      (fun n=>(56/(P.card:ℝ))*columnWeight n*16*((chains n).k+1:ℝ))
      (fun n=>localErrorCost (chains n).p ((chains n).k-1))
      (fun n=>∑D∈Ds n,∑z∈partRows false (chains n).υ (if second then ψ₂⁻¹ else χ)
        (internalQ Q η₀) fixedBadMask (geom n).C (geom n).D (geom n).U (geom n).radius,
        ‖normalizedColumn (withHeight (chains n).extracted ((geom n).τ (if second then ψ₂⁻¹ else χ)) analyticv)
          (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2)
      (fun n=>Z^(errorRemoval (chains n).p Z (chains n).k-errorMoving (chains n).p Z (chains n).k))
      (fun n=>((chains n).E₂.absNorm:ℝ)^(εshell-1))
      (fun n=>Z^((geom n).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (chains n).k+
        εold+loss*(Fintype.card α:ℝ)+(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+(3/4)*mesh+pad))
      (hpayRaw χ ψ₂)
  have hnorm := actual_geometry_error_normalized_to_datum_columns reflected s R seed
    Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂
    P weight windowProfile index χ₀ (internalQ Q η₀) second tₑ u
    N a ap ha hap hcard hlower hW₁ hW₂ hwgt hQ72

  have hc (n : Label) :
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
  have hcolumn (χ ψ₂ : RayCharacter)(n : Label)(D : Ideal O) :
      (if second then
        ∑z∈partRows false (datum n).input.η ψ₂⁻¹ (internalQ Q η₀) fixedBadMask
          (datum n).C (datum n).D (datum n).inactive (datum n).radius,
          ‖normalizedColumn (withHeight (datum n).input ((datum n).τ ψ₂⁻¹)
            ((datum n).input.t+2*Real.pi*(u-(-tₑ))))
            (datum n).D (datum n).hD (datum n).R (datum n).seed D z‖^2
      else
        ∑z∈partRows false (datum n).input.η χ (internalQ Q η₀) fixedBadMask
          (datum n).C (datum n).D (datum n).inactive (datum n).radius,
          ‖normalizedColumn (withHeight (datum n).input ((datum n).τ χ)
            ((datum n).input.t+2*Real.pi*(u-tₑ)))
            (datum n).C (datum n).hC (datum n).R (datum n).seed D z‖^2)=
      ∑z∈partRows false (chains n).υ (if second then ψ₂⁻¹ else χ) (internalQ Q η₀) fixedBadMask
        (geom n).C (geom n).D (geom n).U (geom n).radius,
        ‖normalizedColumn (withHeight (chains n).extracted ((geom n).τ (if second then ψ₂⁻¹ else χ))
          analyticv) (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2 := by
    exact actual_geometry_error_admitted_columns_eq reflected s R seed Z Mrow amp ξ reserve bs t₀
      (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ hp hcop ψ hυ hf₁
      (index n) (hne n) second (internalQ Q η₀) hQ72 (if second then ψ₂⁻¹ else χ) χ ψ₂ D tₑ u
  let rawCoefficient : Label→ℝ := fun n=>errorNormalizedCoefficient P weight (volume source) prime i*
    (K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive
  let paidCoefficient : Label→ℝ := fun n=>coefficient n*localErrorCost (chains n).p ((chains n).k-1)
  let rawColumn : RayCharacter→RayCharacter→Label→Ideal O→ℝ := fun χ ψ₂ n D=>
      (if second then
        ∑z∈partRows false (datum n).input.η ψ₂⁻¹ (internalQ Q η₀) fixedBadMask
          (datum n).C (datum n).D (datum n).inactive (datum n).radius,
          ‖normalizedColumn (withHeight (datum n).input ((datum n).τ ψ₂⁻¹)
            ((datum n).input.t+2*Real.pi*(u-(-tₑ))))
            (datum n).D (datum n).hD (datum n).R (datum n).seed D z‖^2
      else
        ∑z∈partRows false (datum n).input.η χ (internalQ Q η₀) fixedBadMask
          (datum n).C (datum n).D (datum n).inactive (datum n).radius,
          ‖normalizedColumn (withHeight (datum n).input ((datum n).τ χ)
            ((datum n).input.t+2*Real.pi*(u-tₑ)))
            (datum n).C (datum n).hC (datum n).R (datum n).seed D z‖^2)
  let paidColumn : RayCharacter→RayCharacter→Label→Ideal O→ℝ := fun χ ψ₂ n D=>
      ∑z∈partRows false (chains n).υ (if second then ψ₂⁻¹ else χ) (internalQ Q η₀) fixedBadMask
        (geom n).C (geom n).D (geom n).U (geom n).radius,
        ‖normalizedColumn (withHeight (chains n).extracted ((geom n).τ (if second then ψ₂⁻¹ else χ))
          analyticv) (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2
  let scalarBudget := Cg*(p.control Sp)^2*(1+|analyticv|+height)^degree*Z^(εproj+3*L₂*εshell)*
    ∑n : Label,coefficient n*
      Z^(errorRemoval (chains n).p Z (chains n).k-errorMoving (chains n).p Z (chains n).k)*
      ((chains n).E₂.absNorm:ℝ)^(εshell-1)*
      Z^((geom n).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (chains n).k+
        εold+loss*(Fintype.card α:ℝ)+(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+(3/4)*mesh+pad)
  have htransport :
      (∑χ : RayCharacter,∑ψ₂ : RayCharacter,∑n : Label,rawCoefficient n*∑D∈Ds n,rawColumn χ ψ₂ n D)≤
        ((Fintype.card RayCharacter:ℝ)^2)*scalarBudget := by
    exact error_normalized_ray_transport (Ds:=Ds) (rawCoefficient:=rawCoefficient)
      (paidCoefficient:=paidCoefficient) (raw:=rawColumn) (paid:=paidColumn) (E:=scalarBudget)
      hc (fun χ ψ₂ n D _=>hcolumn χ ψ₂ n D) hpay

  have hraw := hnorm.trans htransport


  let cost:=fun n : Label=>geometryErrorColumnScalar reflected s R seed Z Mrow amp ξ reserve bs t₀
    (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁
    P weight (lowerFactor N a ap) error εshell
  have hscalar : (∑n : Label,cost n)≤
      ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lowerFactor N a ap)*
        ((box.card:ℝ)*∑l∈actualSecondLabels source
          ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val)*(Ideal.span {prime})^(errorIndex i+1))
          first.1.val.2.1.val,
          extractedErrorLabelScalar reflected second
            (geometryFirstLabel s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val)
            l Z Mrow amp (frequencyLoss Z 32 ξ) reserve error εshell (volume s) (volume source)
            prime (errorIndex i+1)) := by
    exact actual_geometry_error_indexed_scalar_payment reflected s R seed Z Mrow amp ξ reserve bs t₀
      (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ hp hcop ψ hυ hf₁ index hne hinj
      second P weight (lowerFactor N a ap) error εshell hwgt (lowerFactor_pos N a ap ha hap) box hbox
  exact error_scaled_label_payment hraw cost
    (by
      intro n
      dsimp (config := {zetaDelta := false}) only [cost,geometryErrorColumnScalar,error]
      exact error_scalar_reassoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    hscalar (by
      have hCg : 0<Cg:=hCg
      positivity)

theorem actual_geometry_error_normalized_pointwise {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(B ap bp Bmask L lo hi Mcap εold loss : ℝ)(ηseed : Character)
    (bs εwidth εpad Mmin window pad εshell : ℝ)(N : ℕ)(Cs L₂ εproj Cg : ℝ)
    (Sp : Finset (ℕ×ℕ))(degree : ℕ)(η₀ : Character)(Q : Ideal O)(Z : ℝ)
    (hCg : 0<Cg)(hap : 0<ap)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hpaid : geometryErrorProjectorPaidSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z) :
    geometryErrorNormalizedDynamicSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z := by
  exact actual_geometry_error_normalized_from_concrete_paid_columns
    M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell
    N Cs L₂ εproj Cg Sp degree η₀ Q Z hCg hap hQ72
    (actual_geometry_error_projector_to_concrete_paid_columns
      M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell
      N Cs L₂ εproj Cg Sp degree η₀ Q Z hCg hap hQ72 hpaid)


set_option maxHeartbeats 200000 in
set_option linter.defProp false in
/-- Literal ordinary normalized error sums from the genuine paid columns.
The two ray sums pay their fixed finite cardinality, with the first key intact. -/
theorem actual_geometry_error_projector_spec_family {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hL : 0≤L) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hloss : 0<loss) (hmargin : 0<margin) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤window) (hpad : 0<pad) (heshell : 0<εshell)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1≤Cs)(hL₂ : 0≤L₂)(heproj : 0<εproj) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
      Q≤M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
      ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop, 1<Z ∧
        geometryErrorProjectorPaidSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss
          ηseed bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z := by
  have hJ : 0<(fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  simpa only [geometryErrorProjectorPaidSpec] using
    (actual_paid_error_complete_projector_family.{u,v} (α:=α)
      M H hH W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
      hBmask hL hMcap hεold hloss hmargin hbeta ηseed bs (fixedFactor:ℝ) εwidth εpad Mmin
      window pad εshell hwindow hpad heshell hbs hJ hew hep hmin N Cs L₂ εproj hCs hL₂ heproj)


theorem actual_geometry_error_paid_normalized_labels {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hL : 0≤L) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hloss : 0<loss) (hmargin : 0<margin) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤window) (hpad : 0<pad) (heshell : 0<εshell)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1≤Cs)(hL₂ : 0≤L₂)(heproj : 0<εproj) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
      Q≤M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
      ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop, 1<Z ∧
        geometryErrorNormalizedDynamicSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss
          ηseed bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z := by
  obtain ⟨degree,Sp,hfamily⟩ := actual_geometry_error_projector_spec_family.{u,v} (α:=α)
    M H hH W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
    hBmask hL hMcap hεold hloss hmargin hbeta ηseed bs εwidth εpad Mmin
    window pad εshell hwindow hpad heshell hbs hew hep hmin N Cs L₂ εproj hCs hL₂ heproj
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hfamily η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hz
  exact ⟨hz.1,actual_geometry_error_normalized_pointwise.{u,v} (α:=α)
    M H hH W B ap bp Bmask L lo hi Mcap εold loss ηseed bs εwidth εpad Mmin window pad εshell
    N Cs L₂ εproj Cg Sp degree η₀ Q Z hCg hap hQ72 hz.2⟩



end
end OAI.SevenEighths.Cycle62InitialMass





#print axioms OAI.SevenEighths.Cycle62InitialMass.second_normalized_effective_sigma
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_scalar_label_cost_nonneg
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_indexed_positive_disintegration
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_indexed_scalar_payment
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_indexed_normalized_to_datum_columns
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_indexed_given_datum_normalized_to_columns
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_normalized_to_datum_columns
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_admitted_columns_eq
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_projector_to_concrete_paid_columns
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_normalized_from_concrete_paid_columns
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_normalized_pointwise
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_projector_spec_family
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_paid_normalized_labels
