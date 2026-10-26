/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected first-column remainder sums after pool, allocation and label
counting. The only outstanding admissions are geometric and numerical. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialRemainderScalarSumNode
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFrozenOne
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialRemainderScalarNode
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalInitialGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily Cycle61InitialMass Cycle61Moment CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant
open CenteredMomentSourceInputTailUniform (plainControl)
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.Pool
open QRH.Record1252270103Source.MarkedMainRemainder
open QRH.Record1252270103Source.ExceptionalPrice
open ConcretePrimeRowBridge CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103Low QRH.Record1252270103Source.InitialPhysical
open Record1252270103Finite Record1252270103StepScalar
local notation "O"=>HeckeFamily.O


open QRH.Record1252270103Source.Low.InitialRemainder
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (Wslot : ℝ→ℂ) (hW : ContDiff ℝ ∞ Wslot)
variable (hsW : Function.support Wslot⊆Set.Icc (1:ℝ) 2)

theorem eventual_initial_remainder_sums_one (N : ℕ) (ell epsMass epsZero epsCount : ℝ)
    (hell : 0<ell) (hmass : 0<epsMass) (hzero : 0≤epsZero) (hcount : 0<epsCount) :
    ∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type}[Fintype ι][DecidableEq ι](hZ : 0<Z)(η η₀ : Character)(R₀ : Ideal O)
      (θ : ι→RayQuotient.Characters rayM H)(w v : ι→ℝ)(ht : ℝ)(p : Profiles (1/4) (9/4))
      (X₁ X₂ Y₁ Y₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)(hY₁ : 0<Y₁)(hY₂ : 0<Y₂)
      (hprod : Y₁*Y₂=X₁*X₂),
    let s:=initialInput rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v ht
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(K : ℚ)(n low : Source)(b width : ℝ), RealGeometry K n low b→
      0≤(n.allowance:ℝ)→0≤(n.L:ℝ)→(low.B:ℝ)≤1→width≤PhysicalLowGuard.step n→
      (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
        (length Z X₁) (length Z X₂) (∑i,w i) 1→
      b-(n.allowance:ℝ)-width≤∑i,w i→(∑i,w i)≤b→Fintype.card ι≤N→
    let a:=sourceAReal n low b
    let allowance:=(n.allowance:ℝ)
    let Cann:=initialCann N
    ∀(modifier : Tuple ι→ℂ)(R : Ideal O)(W : 𝓢(ℝ,ℂ))(ξ reserve loss saving : ℝ)(hK : 0<Z),
      frequencyLoss Z 32 ξ+reserve+2*epsMass+loss+epsZero≤2*allowance→
    ∀(P : Finset (Ideal O))(mesh BD Bsource : ℝ)(depth : ℕ),
      FixedCellPoolData P Z a ell mesh loss BD Bsource depth→
    ∀(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s modifier R 1 (Z) Z ξ hK bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R 1 (Z) Z ξ hK bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R 1 (Z) Z ξ hK bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^(4:ℝ))→
    let C:=fun j=>geometryColumnIdeal reflected s modifier R 1 (Z) Z ξ hK bin (column j)
    let label:=fun j=>FirstFamily.firstLabel s modifier R 1 (Z) Z ξ hK bin (column j)
    let Hmain:=fun j=>firstMainRadius reflected (Z) (volume s) Z ξ (3*a) reserve (label j)
    let radius:=fun j=>literalFirstRadius reflected (Z) (volume s) Z ξ reserve (label j)
    let H0:=fun j=>(geometryFirstSource s modifier R 1 (Z) Z ξ hK bin (column j).1).H0
    let scalar:=fun j=>balancedColumnScalar reflected s modifier R 1 (Z) Z ξ 1
      (Real.logb Z (volume s)) hK bin (fun q=>normPhase (coordinateBlock s modifier R 1 W (Z) Z ξ q)) (column j)
    let factor:=geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin
    (∀j,0≤radius j+6*a)→(∀j,radius j+6*a≤32)→
    ∀(alloc : ∀j,actualAllocations s.pools (C j))(τ : J→Character)(t : J→ℝ),
      (∀j,frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P≠0)→
    let amplitude:=fun j=>‖scalar j‖^2*
      (((bands (H0 j)).card:ℝ)*((actualAllocations s.pools (C j)).card:ℝ)^2/(P.card:ℝ)*
        ((radius j+6*a)/ell))*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2
    (∀j,sourceRadius (child s (C j) R (alloc j) (τ j) (t j))≤
      (Cann/((C j).absNorm:ℝ))*volume s) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) (p.profile 0) (p.profile 1))^2*
        Hmain j*(Cann/((C j).absNorm:ℝ))^(1+epsZero)*(volume s)^epsZero/
          ((column j).2.1.val.absNorm:ℝ))≤
      Czero*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*factor*
        Z^(-a-allowance+2*epsCount)) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) (p.profile 0) (p.profile 1))^2*
        Hmain j*(volume (child s (C j) R (alloc j) (τ j) (t j))/volume s)*Z^(-saving)/
          ((column j).2.1.val.absNorm:ℝ))≤
      Ctail*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*factor*
        Z^(-a-allowance-saving+2*epsCount)) := by
  obtain ⟨Cz,Ct,hCz,hCt,hbound⟩:=eventual_initial_remainder_sums rayM H hH Wslot hW hsW
    N ell epsMass epsZero epsCount hell hmass hzero hcount
  refine ⟨Cz,Ct,hCz,hCt,hbound.mono ?_⟩
  intro Z hz
  refine ⟨hz.1,?_⟩
  intro ι instι dec hZ η η₀ R₀ θ w v ht p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod s
    K n low b width hg he hL hB hw hadm hlo hhi hN a allowance Cann
    modifier R W ξ reserve loss saving hK herr P mesh BD Bsource depth hpool
    reflected bin J instJ
  have hh:=hz.2 hZ η η₀ R₀ θ w v ht p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    K n low b width hg he hL hB hw hadm hlo hhi hN modifier R W ξ reserve loss saving
    (Real.rpow_pos_of_pos hZ 1) herr P mesh BD Bsource depth hpool reflected bin J
  let Result (X:ℝ)(hX:0<X):Prop:=
      ∀(column : J→FirstColumnIndex (geometryFirstSource s modifier R 1 (X) Z ξ hX bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R 1 (X) Z ξ hX bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R 1 (X) Z ξ hX bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^(4:ℝ))→
    let C:=fun j=>geometryColumnIdeal reflected s modifier R 1 (X) Z ξ hX bin (column j)
    let label:=fun j=>FirstFamily.firstLabel s modifier R 1 (X) Z ξ hX bin (column j)
    let Hmain:=fun j=>firstMainRadius reflected (X) (volume s) Z ξ (3*a) reserve (label j)
    let radius:=fun j=>literalFirstRadius reflected (X) (volume s) Z ξ reserve (label j)
    let H0:=fun j=>(geometryFirstSource s modifier R 1 (X) Z ξ hX bin (column j).1).H0
    let scalar:=fun j=>balancedColumnScalar reflected s modifier R 1 (X) Z ξ 1
      (Real.logb Z (volume s)) hX bin (fun q=>normPhase (coordinateBlock s modifier R 1 W (X) Z ξ q)) (column j)
    let factor:=geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin
    (∀j,0≤radius j+6*a)→(∀j,radius j+6*a≤32)→
    ∀(alloc : ∀j,actualAllocations s.pools (C j))(τ : J→Character)(t : J→ℝ),
      (∀j,frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P≠0)→
    let amplitude:=fun j=>‖scalar j‖^2*
      (((bands (H0 j)).card:ℝ)*((actualAllocations s.pools (C j)).card:ℝ)^2/(P.card:ℝ)*
        ((radius j+6*a)/ell))*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2
    (∀j,sourceRadius (child s (C j) R (alloc j) (τ j) (t j))≤
      (Cann/((C j).absNorm:ℝ))*volume s) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) (p.profile 0) (p.profile 1))^2*
        Hmain j*(Cann/((C j).absNorm:ℝ))^(1+epsZero)*(volume s)^epsZero/
          ((column j).2.1.val.absNorm:ℝ))≤
      Cz*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*factor*
        Z^(-a-allowance+2*epsCount)) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) (p.profile 0) (p.profile 1))^2*
        Hmain j*(volume (child s (C j) R (alloc j) (τ j) (t j))/volume s)*Z^(-saving)/
          ((column j).2.1.val.absNorm:ℝ))≤
      Ct*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*factor*
        Z^(-a-allowance-saving+2*epsCount))
  exact positive_radius_transport Result (Real.rpow_one Z) (Real.rpow_pos_of_pos hZ 1) hK hh

end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.eventual_initial_remainder_sums_one
