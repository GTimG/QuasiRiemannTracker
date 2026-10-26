/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full first-key payment with the original frozen coefficient, child volume,
MAIN prefactor and Fourier scale; every residual projector remains summed. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFrozenSum

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open Record12518109Natural Record1252270103Finite Record1252270103StepScalar
open Record1252270103Second
open OAI.SevenEighths.Record1252270103Source.Collision
open High.CoupledFirst Admission Pool
local notation "O"=>HeckeFamily.O

theorem positive_radius_transport (P:(x:ℝ)→0<x→Prop) {x y:ℝ}
    (e:x=y)(hx:0<x)(hy:0<y)(h:P x hx):P y hy := by
  subst y
  exact h

theorem selected_frozen_first_sum_one (N : ℕ)(lo ap B Bseed εcount εcard ell lower radiusMax : ℝ)
    (hlo : 0<lo)(hap : 0<ap)(hB : 0≤B)(hBseed : 0≤Bseed)(hcount : 0<εcount)
    (hcard : 0<εcard)(hell : 0<ell)(hlower : 0<lower)(hmax : 0≤radiusMax) :
    ∃Ctotal : ℝ,0<Ctotal ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι)
      (A₁ A₂ Dmark Kmark R seed : Ideal O)(F : Ideal O→ℂ)(W : 𝓢(ℝ,ℂ))
      (K : ℚ)(n low : Source)(b ξ reserve poolLoss plainError : ℝ),
      RealGeometry K n low b→Fintype.card ι≤N→lo≤s.lower→
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      (∀x,s.W₁ x≠0→ap≤x)→(∀x,s.W₂ x≠0→ap≤x)→
      Real.logb Z (volume s)≤sourceTReal n b+b+plainError→
      plainError+5*(frequencyLoss Z 32 ξ+reserve)/6+(εcard+poolLoss+ξ/12)≤sourceAReal n low b→
    let modifier:=markedSourceModifier A₁ A₂ Dmark Kmark F
    ∀(hZ : 1<Z)(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s modifier R seed Z Z ξ
        (zero_lt_one.trans hZ) bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R seed Z Z ξ
        (zero_lt_one.trans hZ) bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R seed Z Z ξ
        (zero_lt_one.trans hZ) bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^Bseed)→
    let label:=fun j=>FirstFamily.firstLabel s modifier R seed Z Z ξ
      (zero_lt_one.trans hZ) bin (column j)
    let C:=fun j=>if reflected then (label j).1.2 else (label j).1.1
    let scalar:=fun j=>balancedColumnScalar reflected s modifier R seed Z Z ξ 1
      (Real.logb Z (volume s)) (zero_lt_one.trans hZ) bin
      (fun q=>normPhase (coordinateBlock s modifier R seed W Z Z ξ q)) (column j)
    let amp:=sourceAReal n low b
    let Hmain:=fun j=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (label j)
    let Rmain:=fun j=>frequencyRadius
      (firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (label j)) Z ξ
    ∀(alloc:∀j,actualAllocations s.pools (C j))(τ:J→Character)(t H0 radius:J→ℝ)
      (P:Finset (Ideal O))(mesh BD Bsource:ℝ)(depth:ℕ),
      FixedCellPoolData P Z amp ell mesh poolLoss BD Bsource depth→
      (∀j,0<H0 j)→(∀j,0≤radius j+6*amp)→(∀j,radius j+6*amp≤radiusMax)→
    let extra:=fun j=>((bands (H0 j)).card:ℝ)*((actualAllocations s.pools (C j)).card:ℝ)^2/
      (P.card:ℝ)*((radius j+6*amp)/ell)
    (∑j,(‖scalar j‖^2*extra j*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2/volume s)*
      (Hmain j/lower)*(max 1 (Z^(49/100-(K:ℝ)*b)/((C j).absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*
      volume (child s (C j) R (alloc j) (τ j) (t j))*(4*Rmain j)^(1/6:ℝ)/
      ((column j).2.1.val.absNorm:ℝ))≤
      Ctotal*forcedProfileCost s*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^(-(n.highFee:ℝ)-4*amp+2*εcount)/(seed.absNorm:ℝ) := by
  obtain ⟨Cpaid,hC,hp⟩:=selected_frozen_first_sum N lo ap B Bseed εcount εcard ell lower radiusMax
    hlo hap hB hBseed hcount hcard hell hlower hmax
  refine ⟨Cpaid,hC,hp.mono ?_⟩
  intro Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst dec s A₁ A₂ Dmark Kmark R seed F W K n low b ξ reserve poolLoss plainError
    hg hN hslower hs hs0 hz₁ hz₂ hsource hs₁ hs₂ hlog herr modifier hZ reflected bin J instJ
  have hh:=hz.2 s A₁ A₂ Dmark Kmark R seed F W K n low b ξ reserve poolLoss plainError
    hg hN hslower hs hs0 hz₁ hz₂ hsource hs₁ hs₂ hlog herr hZ reflected bin J
  let P (X:ℝ)(hX:0<X):Prop:=
      ∀(column : J→FirstColumnIndex (geometryFirstSource s modifier R seed X Z ξ
        hX bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R seed X Z ξ
        hX bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R seed X Z ξ
        hX bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^Bseed)→
    let label:=fun j=>FirstFamily.firstLabel s modifier R seed X Z ξ
      hX bin (column j)
    let C:=fun j=>if reflected then (label j).1.2 else (label j).1.1
    let scalar:=fun j=>balancedColumnScalar reflected s modifier R seed X Z ξ 1
      (Real.logb Z (volume s)) hX bin
      (fun q=>normPhase (coordinateBlock s modifier R seed W X Z ξ q)) (column j)
    let amp:=sourceAReal n low b
    let Hmain:=fun j=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (label j)
    let Rmain:=fun j=>frequencyRadius
      (firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (label j)) Z ξ
    ∀(alloc:∀j,actualAllocations s.pools (C j))(τ:J→Character)(t H0 radius:J→ℝ)
      (P:Finset (Ideal O))(mesh BD Bsource:ℝ)(depth:ℕ),
      FixedCellPoolData P Z amp ell mesh poolLoss BD Bsource depth→
      (∀j,0<H0 j)→(∀j,0≤radius j+6*amp)→(∀j,radius j+6*amp≤radiusMax)→
    let extra:=fun j=>((bands (H0 j)).card:ℝ)*((actualAllocations s.pools (C j)).card:ℝ)^2/
      (P.card:ℝ)*((radius j+6*amp)/ell)
    (∑j,(‖scalar j‖^2*extra j*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2/volume s)*
      (Hmain j/lower)*(max 1 (Z^(49/100-(K:ℝ)*b)/((C j).absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*
      volume (child s (C j) R (alloc j) (τ j) (t j))*(4*Rmain j)^(1/6:ℝ)/
      ((column j).2.1.val.absNorm:ℝ))≤
      Cpaid*forcedProfileCost s*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^(-(n.highFee:ℝ)-4*amp+2*εcount)/(seed.absNorm:ℝ)
  exact positive_radius_transport P (Real.rpow_one Z)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) (zero_lt_one.trans hZ) hh

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.positive_radius_transport
#print axioms QRH.Record1252270103Source.ExceptionalPrice.selected_frozen_first_sum_one
