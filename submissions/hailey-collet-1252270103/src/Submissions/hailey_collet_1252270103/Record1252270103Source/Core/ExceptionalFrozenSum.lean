/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full first-key payment with the original frozen coefficient, child volume,
MAIN prefactor and Fourier scale; every residual projector remains summed. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFirstFrozen

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

theorem selected_frozen_first_sum (N : ℕ)(lo ap B Bseed εcount εcard ell lower radiusMax : ℝ)
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
      (column : J→FirstColumnIndex (geometryFirstSource s modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^Bseed)→
    let label:=fun j=>FirstFamily.firstLabel s modifier R seed (Z^1) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j)
    let C:=fun j=>if reflected then (label j).1.2 else (label j).1.1
    let scalar:=fun j=>balancedColumnScalar reflected s modifier R seed (Z^1) Z ξ 1
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin
      (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^1) Z ξ q)) (column j)
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
  obtain ⟨A,hA,hpref⟩:=uniform_first_main_prefactor N B εcard ell lower radiusMax hB hcard hell hlower hmax
  obtain ⟨C,hC,hcountZ⟩:=selected_first_radical_sum N lo ap B Bseed εcount hlo hap hB hBseed hcount
  let fixed:ℝ:=(4:ℝ)^(1/6:ℝ)*((2:ℝ)^N)^(1/3:ℝ)
  have hfixed : 0<fixed := by dsimp only [fixed];positivity
  refine ⟨C*A*fixed,by positivity,?_⟩
  filter_upwards [hcountZ] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst dec s A₁ A₂ Dmark Kmark R seed F W K n low b ξ reserve poolLoss plainError hg
    hN hslower hs hs0 hz₁ hz₂ hsource hs₁ hs₂ hlog herr modifier hZ reflected bin J instJ
    column hinj hlive hcap label Cfirst scalar amp Hmain Rmain alloc τ t H0 radius P mesh BD Bsource
    depth hpool hH0 hr0 hr extra
  let G:=forcedProfileCost s*A*fixed
  have hG : 0≤G := mul_nonneg (mul_nonneg (forcedProfileCost_nonneg s) hA.le) hfixed.le
  have point(j:J) :
      (‖scalar j‖^2*extra j*‖frozenCoefficient (alloc j).val (Cfirst j) R s.ν s.W s.P‖^2/volume s)*
        (Hmain j/lower)*(max 1 (Z^(49/100-(K:ℝ)*b)/((Cfirst j).absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*
        volume (child s (Cfirst j) R (alloc j) (τ j) (t j))*(4*Rmain j)^(1/6:ℝ)/
        ((column j).2.1.val.absNorm:ℝ)≤
      G*(balancedFirstHighMass reflected s modifier R seed W 1 Z ξ 0
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j)*
        firstRadialFactor reflected (label j) Z (volume s) (49/100-(K:ℝ)*b) amp ξ reserve
          (εcard+poolLoss+ξ/12)/((column j).2.1.val.absNorm:ℝ)) := by
    have hsup:=FirstFamily.label_supported s modifier R seed (Z^1) Z ξ _ bin (column j)
    have hc : Cfirst j≠0 := by cases reflected <;> first | exact hsup.1.1 | exact hsup.2.1.1
    have hn:=FirstFamily.label_common_bounds s modifier R seed (Z^1) Z ξ _ bin hs hz₁ hz₂ (column j)
    have hnc : ((Cfirst j).absNorm:ℝ)≤Z^B := by
      cases reflected
      · exact hn.2.2.1.trans hsource
      · exact hn.2.2.2.trans hsource
    have he0 : 0≤extra j := by
      dsimp only [extra]
      exact mul_nonneg
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
        (div_nonneg (hr0 j) hell.le)
    have he:=hpref s hN (Cfirst j) P Z amp mesh poolLoss BD Bsource depth hc hnc hpool
      (H0 j) (radius j) (hH0 j) (hr0 j) (hr j)
    have hh:=frozen_first_payment s reflected (label j) hsup.1 hsup.2.1 R (alloc j) (τ j) (t j)
      (scalar j) N Z (49/100-(K:ℝ)*b) amp ξ reserve (extra j) lower A (εcard+poolLoss)
      (zero_lt_one.trans hZ) he0 hlower hA.le (by convert he using 1 <;> congr 1 <;> ring)
    have hd:=div_le_div_of_nonneg_right hh (Nat.cast_nonneg ((column j).2.1.val.absNorm))
    have hmass : balancedFirstHighMass reflected s modifier R seed W 1 Z ξ 0
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j)=
        ‖scalar j‖^2/((Cfirst j).absNorm:ℝ) := by
      unfold High.CoupledFirst.balancedFirstHighMass
      change ‖scalar j‖^2*((Cfirst j).absNorm:ℝ)^((0:ℝ)-1)=_
      norm_num [Real.rpow_neg_one,div_eq_mul_inv]
    rw [hmass]
    convert hd using 1 <;> dsimp only [G,fixed] <;> ring
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun j _=>point j)
  rw [←Finset.mul_sum] at hsum
  have hh:=hz.2 s A₁ A₂ Dmark Kmark R seed F W K n low b ξ reserve (εcard+poolLoss+ξ/12)
    plainError hg hN hslower hs hs0 hz₁ hz₂ hsource hs₁ hs₂ hlog herr
    hZ reflected bin J column hinj hlive hcap
  have hb:=hsum.trans (mul_le_mul_of_nonneg_left hh hG)
  convert hb using 1 <;> dsimp only [G,fixed,amp] <;> ring

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.selected_frozen_first_sum
