/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainErrorMain
import Candidate.Uneven.MainErrorParameters
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Uneven.MainErrorNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell
import Candidate.Uneven.MainAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.MainErrorReconstruction
open OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Sil.Uneven.MainSource
variable {plane : Plane}
open OAI.SevenEighths.MainReconstruction
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
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O
local instance errorNormalizedClosureSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α : Type*} [Fintype α] [DecidableEq α]
section Selected
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (p : O) (i : Fin 3)
variable (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
variable (second : Bool)

/-- The allocation is fixed by the original nonzero physical block, before
its residual projector, either ray, or any external Mellin height. -/
noncomputable def geometryErrorSelectedAllocation :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    actualAllocations d.input.pools (if second then d.D else d.C) :=
  let nz : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ :=
    ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩⟩
  Classical.choose (actual_geometry_error_live_common_allocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ nz second)

theorem geometryErrorSelectedAllocation_nonzero :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    frozenCoefficient (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second).val
      (if second then d.D else d.C) d.R d.input.ν d.input.W d.input.P≠0 :=
  Classical.choose_spec (actual_geometry_error_live_common_allocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂
    ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩⟩ second)


variable (hp : p≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
      IsCoprime (Ideal.span {p}) I)
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm ≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

/-- Actual admission uses the live allocation supplied by the original
block; the inducing and full stored-pool coprimality gates stay explicit. -/
noncomputable def geometryErrorSelectedGeometry :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    Geometry s (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second))
      Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b (fixedFactor:ℝ) N :=
  geometryErrorActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hp hcop hw₁ hw₂ ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩⟩ second
    (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second) ψ hυ hf₁
    (geometryErrorSelectedAllocation_nonzero reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)

/-- Admission preserves the literal extracted frequency radius in both
first orientations; it does not replace the common source radius. -/
theorem geometryErrorSelectedGeometry_radius :
    (geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁).radius=
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).radius := by
  change errorRadius
    (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).D
       else (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).C)
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).R
      (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second))
    (geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
    (geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
    Z Mrow amp (frequencyLoss Z 32 ξ) reserve ξ b N=
      frequencyRadius (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
  exact actual_geometry_error_radius reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hp hcop _ _ _


/-- Both full physical zero-mode sums equal the columns of the admitted
geometry. The right ray stays inverse and its height shift stays negative. -/
theorem geometryErrorSelectedGeometry_complete_columns
    (Q : Ideal O)(hQ : Q ≤ Ideal.span {(72:O)})
    (χ₀ χ ψ₂ : RayCharacter)(L : Ideal O)(tₑ u : ℝ) :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
    let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
    let hE : Supported chain.E₂ := by
      cases second with
      | false => exact d.hC
      | true => exact d.hD
    (∑z∈partRows false d.input.η χ₀ Q fixedBadMask d.C d.D d.inactive d.radius,
      if second then
        ‖normalizedColumn (withHeight d.input (d.τ ψ₂⁻¹) (d.input.t+2*Real.pi*(u-(-tₑ))))
          d.D d.hD d.R d.seed L (-z)‖^2
      else
        ‖normalizedColumn (withHeight d.input (d.τ χ) (d.input.t+2*Real.pi*(u-tₑ)))
          d.C d.hC d.R d.seed L z‖^2)=
    ∑z∈partRows false chain.υ (if second then ψ₂⁻¹ else χ) Q fixedBadMask
      g.C g.D g.U g.radius,
      ‖normalizedColumn (withHeight chain.extracted (g.τ (if second then ψ₂⁻¹ else χ))
        (chain.extracted.t+2*Real.pi*(u-(if second then -tₑ else tₑ))))
        chain.E₂ hE chain.R₂ d.seed L z‖^2 := by
  intro d chain g hE
  apply (actual_error_complete_column_rows d.input d.τ d.C d.D d.hC d.hD d.inactive
    d.R d.seed L Q d.radius hQ χ₀ χ ψ₂ second tₑ u).trans
  have hr := geometryErrorSelectedGeometry_radius reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
  change _=∑z∈partRows false chain.υ (if second then ψ₂⁻¹ else χ) Q fixedBadMask
    g.C g.D g.U g.radius,_
  rw [show g.radius=d.radius from hr]
  cases second <;> rfl


end Selected

/-- Fixed degree and profile control set of the genuine paid error theorem,
chosen before the original source, its heights, or either block family. -/
def actual_geometry_error_column_parameters {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hBmask : 0 ≤ Bmask) (hL : 0 ≤ L) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hloss : 0 < loss) (hmargin : 0 < margin) (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ plane.incumbent)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0 ≤ window) (hpad : 0 < pad) (heshell : 0 < εshell)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1 ≤ Cs)(hL₂ : 0 ≤ L₂)(heproj : 0 < εproj) :=
  let hJ : 0 < (fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  let uniform := actual_paid_error_complete_projector_family.{u,v} (plane:=plane) (α:=α)
    M H hH W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
    hBmask hL hMcap hεold hloss hmargin hbeta hκbeta ηseed bs (fixedFactor:ℝ) εwidth εpad Mmin
    window pad εshell hwindow hpad heshell hbs hJ hew hep hmin N Cs L₂ εproj hCs hL₂ heproj
  PProd.mk (Classical.choose uniform) (Classical.choose (Classical.choose_spec uniform))


set_option linter.defProp false in
/-- Complete ordinary columns for the literal extracted block family.
The original nonzero gate chooses allocations before either ray or projector. -/
def actual_geometry_error_complete_selected_columns {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hBmask : 0 ≤ Bmask) (hL : 0 ≤ L) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hloss : 0 < loss) (hmargin : 0 < margin) (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ plane.incumbent)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0 ≤ window) (hpad : 0 < pad) (heshell : 0 < εshell)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1 ≤ Cs)(hL₂ : 0 ≤ L₂)(heproj : 0 < εproj) :=
  let hJ : 0 < (fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  let uniform := actual_paid_error_complete_projector_family (α:=α)
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
          (w σ freq : α→ℝ)(v height mesh : ℝ)
          hcard hM hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin
          (Mrow ξ : ℝ) hMmin hξ hMcap' hslot haff=>
        let cell := Sil.Uneven.MainSource.widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
        let amp := Mrow*Sil.Uneven.MainSource.amp plane cell
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
        fun (χ : Label→RayCharacter) hP hPN (p : Profiles ap bp) hp₁ hp₂
          (Ds : Label→Finset (Ideal O)) hDs hcap (P : Finset (Ideal O))(weight : Label→ℝ) hwgt=>
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
        hz.2 hZ s θ w σ freq v height mesh hcard hM hm hsη hsupper hsb₁ hsb₂
          hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow
          (frequencyLoss Z 32 ξ+reserve) ξ hMmin hreserve hξ hMcap' hslot haff
          chains hk hprime' geom χ hP hPN p hp₁ hp₂ (fun n=>(datum n).seed)
          hE₂ hs Ds hDs hcap P weight hwgt)))))


end
end OAI.SevenEighths.MainErrorReconstruction
