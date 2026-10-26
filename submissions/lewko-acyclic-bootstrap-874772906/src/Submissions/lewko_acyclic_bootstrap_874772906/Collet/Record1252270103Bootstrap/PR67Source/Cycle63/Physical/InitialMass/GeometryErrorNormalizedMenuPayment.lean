import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorFullNormalizedPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorAdmission
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorNormalizedFullFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondNormalizedRestriction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
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
open Cycle63FinalNatural Cycle63Moment Cycle63FinalError Cycle63FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget CenteredMomentLogDyadic
local instance errorNormalizedMenuSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := errorNormalizedFullFamilySumDecidableEq

theorem geometryErrorRawNormalizedSum_sigma {α : Type*}[Fintype α][DecidableEq α]
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
    {Menu : Type*}[Fintype Menu]{Blocks : Menu→Type*}[∀j,Fintype (Blocks j)]
    (index : Sigma Blocks→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N
      hZ bin q prime i Bp υ v₀)(χ₀ : Sigma Blocks→RayCharacter)
    (Q : Ideal O) (side : Bool) (tₑ u : ℝ) :
    geometryErrorRawNormalizedSum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q prime i Bp υ v₀ hw₁ hw₂ P weight windowProfile index χ₀ Q side tₑ u=
    ∑j : Menu,geometryErrorRawNormalizedSum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q prime i Bp υ v₀ hw₁ hw₂ P weight windowProfile (fun n : Blocks j=>index ⟨j,n⟩) (fun n=>χ₀ ⟨j,n⟩) Q side tₑ u := by
  simp only [geometryErrorRawNormalizedSum,second_normalized_sum_labels,
    Fintype.sum_sigma,secondEffectiveWeight]

variable [Cycle63.AffineLedger] in
/-- The paid normalized label bound of one extracted error source, summed over a finite
menu of block families. Its analytic factor carries the radial deficit `unit - Mrow`. -/
def geometryErrorNormalizedMenuLabelsConclusion {α : Type*}[Fintype α][DecidableEq α]
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
    {Menu : Type v}[Fintype Menu]{Blocks : Menu→Type v}[∀j,Fintype (Blocks j)]
    (index : Sigma Blocks→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N
      hZ bin q prime i Bp υ v₀)(χ₀ : Sigma Blocks→RayCharacter)
    (Q : Ideal O) (side : Bool) (tₑ u : ℝ) (Ncap : ℕ)(a ap Cg control height εproj L₂ εshell unit error : ℝ)
    (degree : ℕ)(box : Finset (Fin 4→ℤ)) : Prop :=
  let source:=geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q prime i Bp υ v₀
  let R₂:=(R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {prime})^(errorIndex i+1)
  let first:=geometryFirstLabel s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  let analyticv:=v₀+2*Real.pi*(u-(if side then -tₑ else tₑ))
  (∑j : Menu,geometryErrorRawNormalizedSum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q prime i Bp υ v₀
    hw₁ hw₂ P weight windowProfile (fun n : Blocks j=>index ⟨j,n⟩) (fun n=>χ₀ ⟨j,n⟩) Q side tₑ u)≤
    (((Fintype.card RayCharacter:ℝ)^2)*(Cg*control^2*(1+|analyticv|+height)^degree*
      Z^(εproj+3*L₂*εshell+(unit-Mrow))))*
    (((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lowerFactor Ncap a ap)*
      ((box.card:ℝ)*∑l∈actualSecondLabels source R₂ q.1.val.2.1.val,
        extractedErrorLabelScalar reflected side first l Z unit Mrow amp (frequencyLoss Z 32 ξ) reserve
          error εshell (volume s) (volume source) prime (errorIndex i+1)))

set_option linter.defProp false in
variable [Cycle63.AffineLedger] in
def geometryErrorNormalizedMenuDynamicSpec {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(B ap bp Bmask L lo hi Mcap εold loss : ℝ)
    (bs εwidth εpad Mmin window pad εshell : ℝ)(N : ℕ)(Cs L₂ εproj Cg : ℝ)
    (Sp : Finset (ℕ×ℕ))(degree : ℕ)(η₀ : Character)(Q : Ideal O)(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ)(height mesh : ℝ)
    (_hcard : Fintype.card α≤N)(_hM : ∀j,s.M j≤Cs)
    (_hm : Matches M H hH s η₀ θ w σ freq W B Z)
    (_hsupper : s.upper≤bs)(_hsb₁ : s.b₁=bp)(_hsb₂ : s.b₂=bp)
    (_hw : ∀j,0≤w j)(_hwL : ∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold)
    (_hmesh : 0≤ mesh)(_hwm : ∀j,w j≤ mesh)(_hσlo : ∀j,lo≤σ j)(_hσhi : ∀j,σ j≤hi)
    (_hheight : 0≤height)(_hfreq : ∀j,|freq j|≤height)
    (_hOrig : ∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^L)
    (_hwin : ∀j,logWindow (s.lo j) (s.hi j)≤window)
    (unit Mrow ξ : ℝ)(_hMmin : Mmin≤unit)(_hξ : 0≤ξ)
    (_hMcap' : unit+εwidth*unit+ξ/2≤Mcap)
    (_hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit)
    (_hslot : Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit)
    (_haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit),
  let cell := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
  let amp := unit*Cycle63.AffineLedger.amp cell
  ∀(reserve : ℝ)(_hreserve : 0≤frequencyLoss Z 32 ξ+reserve)
    (reflected : Bool)(R seed : Ideal O)(t₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (prime : O)(i : Fin 3)(hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first).slots j→ IsCoprime (Ideal.span {prime}) I)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first)).pools ((Ideal.span {prime})^(errorIndex i+1)))
    (υ : Character)(v₀ : ℝ)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(ψ : RayCharacter)
    (_hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) ψ)
      fixedBadMask prime (errorMovingExponent (errorIndex i)))
    (_hf₁ : frozenCoefficient first.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) R s.ν s.W s.P≠0)
    (_hprime : Cycle63.AffineLedger.primeFraction*amp≤Real.logb Z (normValue prime)),
  ∀{Menu : Type v}[Fintype Menu]{Blocks : Menu→Type v}[∀j,Fintype (Blocks j)],
  let Label:=Sigma Blocks
  ∀(index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀),
  let datum := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
  ∀(hne : ∀n : Label,(datum n).block.value ballProfile≠0)(_hinj : Function.Injective index)(second : Bool),
  let alloc := fun n=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second
  let chains := fun n=>geometryErrorChain reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀ hp hcop
    (if second then (datum n).D else (datum n).C) (datum n).R (alloc n)

  ∀(_hP : ∀n,(chains n).R₂*(chains n).E₂≠0)
    (_hPN : ∀n,(((chains n).R₂*(chains n).E₂).absNorm:ℝ)≤Z^Bmask)
    (p : Profiles ap bp)(_hp₁ : s.W₁=p.profile 0)(_hp₂ : s.W₂=p.profile 1)
    (a : ℝ)(_ha : 0<a)(_hlower : a≤ s.lower)
    (_hW₁ : ∀x,s.W₁ x≠0→ap≤x)(_hW₂ : ∀x,s.W₂ x≠0→ap≤x)
    (windowProfile : 𝓢(ℝ,ℂ))(χ₀ : Label→RayCharacter)
    (P : Finset (Ideal O))(weight : ℝ)(_hwgt : 0≤weight)
    (_hcap : ∀n D,D∈(datum n).block.divisors.filter Squarefree→(D.absNorm:ℝ)≤Z^L₂)
    (tₑ u : ℝ),
  ∀(box : Finset (Fin 4→ℤ))
    (_hbox : ∀n : Label,actualSecondDyad
      (geometryErrorChild reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀)
      ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val)*
          (Ideal.span {prime})^(errorIndex i+1)) first.1.val.2.1.val
      (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i)
      (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve bs (Fintype.card α) hZ bin first prime i)
      Z ξ (index n)∈box),
  let error:=εwidth*unit+ξ/2+εold+loss*(Fintype.card α:ℝ)+
    (frequencyLoss Z 32 ξ+reserve+εpad*unit)/6+Cycle63.Optimization.slotPrice*mesh+pad
  geometryErrorNormalizedMenuLabelsConclusion reflected s R seed Z Mrow amp ξ reserve bs t₀
    (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ P weight windowProfile
    (Menu:=Menu) (Blocks:=Blocks) index χ₀ (internalQ Q η₀) second tₑ u N a ap Cg (p.control Sp) height
    εproj L₂ εshell unit error degree box

variable [Cycle63.AffineLedger] in
theorem actual_geometry_error_normalized_menu_pointwise {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(B ap bp Bmask L lo hi Mcap εold loss : ℝ)
    (bs εwidth εpad Mmin window pad εshell : ℝ)(N : ℕ)(Cs L₂ εproj Cg : ℝ)
    (Sp : Finset (ℕ×ℕ))(degree : ℕ)(η₀ : Character)(Q : Ideal O)(Z : ℝ)
    (hpaid : @geometryErrorNormalizedDynamicSpec.{u,v} inferInstance α inferInstance inferInstance M inferInstance H hH W B ap bp Bmask L lo hi Mcap εold loss bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z) :
    @geometryErrorNormalizedMenuDynamicSpec.{u,v} inferInstance α inferInstance inferInstance M inferInstance H hH W B ap bp Bmask L lo hi Mcap εold loss bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z := by
  classical
  intro hZ s θ w σ freq height mesh hcard hM hm hsupper hsb₁ hsb₂
    hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin unit Mrow ξ hMmin hξ hMcap' hfit hslot haff
    cell amp reserve hreserve reflected R seed t₀ bin first prime i hp hcop Bp υ v₀ hw₁ hw₂ ψ hυ hf₁
    hprime Menu _ Blocks _ Label index datum hne hinj second alloc chains hP hPN p hp₁ hp₂ a ha hlower
    hW₁ hW₂ windowProfile χ₀ P weight hwgt hcap tₑ u box hbox error
  unfold geometryErrorNormalizedMenuLabelsConclusion
  apply LE.le.trans (geometryErrorRawNormalizedSum_sigma reflected s R seed Z Mrow amp ξ reserve bs t₀
    (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ P weight windowProfile
    (Menu:=Menu) (Blocks:=Blocks) index χ₀ (internalQ Q η₀) second tₑ u).symm.le
  exact @hpaid hZ s θ w σ freq height mesh hcard hM hm hsupper hsb₁ hsb₂
    hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin unit Mrow ξ hMmin hξ hMcap' hfit hslot haff
    reserve hreserve reflected R seed t₀ bin first prime i hp hcop Bp υ v₀ hw₁ hw₂ ψ hυ hf₁
    hprime Label inferInstance index hne hinj second hP hPN p hp₁ hp₂ a ha hlower hW₁ hW₂
    windowProfile χ₀ P weight hwgt hcap tₑ u box hbox

variable [Cycle63.AffineLedger] in
theorem actual_geometry_error_paid_normalized_menu {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hL : 0≤L) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hloss : 0<loss) (hmargin : 0< margin) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤window) (hpad : 0<pad) (heshell : 0<εshell)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1≤Cs)(hL₂ : 0≤L₂)(heproj : 0<εproj) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
      Q≤M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
      ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop, 1<Z ∧
        geometryErrorNormalizedMenuDynamicSpec.{u,v} (α:=α) M H hH W B ap bp Bmask L lo hi Mcap εold loss
          bs εwidth εpad Mmin window pad εshell N Cs L₂ εproj Cg Sp degree η₀ Q Z := by
  obtain ⟨degree,Sp,hfamily⟩ := actual_geometry_error_paid_normalized_labels.{u,v} (α:=α)
    M H hH W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
    hBmask hL hMcap hεold hloss hmargin hbeta bs εwidth εpad Mmin window pad εshell
    hwindow hpad heshell hbs hew hep hmin N Cs L₂ εproj hCs hL₂ heproj
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hfamily η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hz
  exact ⟨hz.1,actual_geometry_error_normalized_menu_pointwise.{u,v} (α:=α)
    M H hH W B ap bp Bmask L lo hi Mcap εold loss bs εwidth εpad Mmin window pad εshell
    N Cs L₂ εproj Cg Sp degree η₀ Q Z hz.2⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
