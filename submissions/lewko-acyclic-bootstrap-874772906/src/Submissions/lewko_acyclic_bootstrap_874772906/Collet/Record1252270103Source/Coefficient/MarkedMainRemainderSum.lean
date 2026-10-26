/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Selected marked MAIN remainder sums, with literal allocation factors and
actual modified first-label counting. The new node's scalar price stays explicit. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMainRemainderCount
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMainRemainderCost
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalHighMass
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.MarkedMainRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSourceInputTailUniform (plainControl)
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
open Record12518109Natural (balancedGeometrySide)
local notation "O"=>HeckeFamily.O

def zeroAllocationFactor {ι : Type*}[Fintype ι] (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t Cann εzero : ℝ) (W₁ W₂ : 𝓢(ℝ,ℂ)) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)^2*‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
    (4*plainControl (child s C R B τ t) W₁ W₂)^2*(Cann/(C.absNorm:ℝ))^(1+εzero)

def tailAllocationFactor {ι : Type*}[Fintype ι] (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W₁ W₂ : 𝓢(ℝ,ℂ)) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)^2*‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
    (2*plainControl (child s C R B τ t) W₁ W₂)^2*(volume (child s C R B τ t)/volume s)

lemma scalar_power_payment (Z mass factor extra side weight power target : ℝ)
    (hZ : 0<Z) (hf : 0≤factor) (hw : 0≤weight)
    (hm : mass≤factor*Z^extra/Z^side)
    (hp : weight*Z^(extra+power-side)≤Z^target) :
    mass*weight*Z^power≤factor*Z^target := by
  calc
    _≤(factor*Z^extra/Z^side)*weight*Z^power := by gcongr
    _=factor*(weight*Z^(extra+power-side)) := by
      rw [Real.rpow_sub hZ,Real.rpow_add hZ]
      ring
    _≤factor*Z^target := mul_le_mul_of_nonneg_left hp hf

/-- `weight` is the retained band count times the pool reciprocal and
MAIN prefactor; zero power is log_Z(Hmain*T^epsilonZero), and tail power is
log_Z(Hmain)-saving. Only these scalar inequalities remain for the new node;
the original coefficient, both allocation cards and all arithmetic counting
are discharged here. No old beta-range estimate or energy premise is used. -/
theorem selected_remainder_sums (N : ℕ) (Cs bs Cann lo ap B L εmass εzero εcount : ℝ)
    (hCs : 1≤Cs) (hbs : 1≤bs) (hCann : 0<Cann) (hlo : 0<lo) (hap : 0<ap)
    (hB : 0≤B) (hL : 0≤L) (hmass : 0<εmass) (hzero : 0≤εzero) (hcount : 0<εcount) :
    ∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι)(modifier : Tuple ι→ℂ)(R seed : Ideal O)
      (W W₁ W₂ : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0<Z^D),
      Fintype.card ι≤N→(∀i,s.M i≤Cs)→s.upper≤bs→lo≤s.lower→
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      (∀x,s.W₁ x≠0→ap≤x)→(∀x,s.W₂ x≠0→ap≤x)→
    ∀(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^L)→
    let C:=fun j=>geometryColumnIdeal reflected s modifier R seed (Z^D) Z ξ hK bin (column j)
    let scalar:=fun j=>balancedColumnScalar reflected s modifier R seed (Z^D) Z ξ D
      (Real.logb Z (volume s)) hK bin (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^D) Z ξ q)) (column j)
    let side:=fun j=>balancedGeometrySide reflected (Real.logb Z (volume s))
      (geometryExponents s modifier R seed (Z^D) Z ξ (column j).1.val)
    let radical:=fun j=>geometryExponents s modifier R seed (Z^D) Z ξ (column j).1.val 2
    let factor:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
    ∀(alloc : ∀j,actualAllocations s.pools (C j))(τ : J→Character)(t weight pzero ptail : J→ℝ)(Ezero Etail : ℝ),
      (∀j,frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P≠0)→(∀j,0≤weight j)→
      (∀j,weight j*Z^(B*εmass+pzero j-side j)≤Z^(Ezero-radical j))→
      (∀j,weight j*Z^(B*εmass+ptail j-side j)≤Z^(Etail-radical j))→
      ((∑j,‖scalar j‖^2*zeroAllocationFactor s (C j) R (alloc j) (τ j) (t j) Cann εzero W₁ W₂*
        weight j*Z^(pzero j)/((column j).2.1.val.absNorm:ℝ))≤
        Czero*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*factor*
          Z^(Ezero+2*εcount)/(seed.absNorm:ℝ)) ∧
      ((∑j,‖scalar j‖^2*tailAllocationFactor s (C j) R (alloc j) (τ j) (t j) W₁ W₂*
        weight j*Z^(ptail j)/((column j).2.1.val.absNorm:ℝ))≤
        Ctail*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*factor*
          Z^(Etail+2*εcount)/(seed.absNorm:ℝ)) := by
  obtain ⟨Cz,Ct,hCz,hCt,halloc⟩:=selected_allocation_remainder_bounds N Cs bs Cann εmass εzero hCs hbs hCann hmass hzero
  obtain ⟨Cc,hCc,hc⟩:=eventual_selected_modified_payment B L εcount hB hL hcount
  refine ⟨Cc*Cz,Cc*Ct,by positivity,by positivity,?_⟩
  filter_upwards [hc] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s modifier R seed W W₁ W₂ D ξ hK hN hM hu hlo' hs hs0 hz₁ hz₂ hsource hs₁ hs₂
    reflected bin J _ column hinj hlive hcap C scalar side radical factor alloc τ t weight pzero ptail Ezero Etail hf hw hpz hpt
  let profile:=(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2
  have hfactor:0≤factor:=(geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hC (j:J):C j≠0 := by
    cases reflected
    · exact (geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin (column j).1).hC.1
    · exact (geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin (column j).1).hD.1
  have ha (j:J):=halloc s hN hM hu W₁ W₂ (C j) R (hC j) (alloc j) (τ j) (t j) (hf j)
  have hm (j:J):=actual_balanced_uniform_high_mass reflected N lo ap hlo hap s modifier R seed W D Z ξ B εmass
    hz.1 hK hmass.le hN hlo' hs hz₁ hz₂ hsource hs₁ hs₂ bin (column j)
  have hpay (power:J→ℝ) (E:ℝ) (hp:∀j,weight j*Z^(B*εmass+power j-side j)≤Z^(E-radical j)) (j:J) :
      balancedFirstHighMass reflected s modifier R seed W D Z ξ εmass hK bin (column j)*weight j*Z^(power j)≤factor*Z^(E-radical j) :=
    scalar_power_payment Z _ factor (B*εmass) (side j) (weight j) (power j) (E-radical j)
      (zero_lt_one.trans hz.1) hfactor (hw j) (hm j) (hp j)
  have point (F:J→ℝ) (Cf:ℝ) (hCf:0≤Cf)
      (hF:∀j,F j≤Cf*profile*((C j).absNorm:ℝ)^(εmass-1))
      (power:J→ℝ)(E:ℝ)(hp:∀j,weight j*Z^(B*εmass+power j-side j)≤Z^(E-radical j)) (j:J) :
      ‖scalar j‖^2*F j*weight j*Z^(power j)/((column j).2.1.val.absNorm:ℝ)≤
        (Cf*profile*factor)*Z^(E-radical j)/((column j).2.1.val.absNorm:ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hh:=mul_le_mul_of_nonneg_left (hF j) (sq_nonneg (‖scalar j‖))
    have hh':=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (hw j))
      (Real.rpow_nonneg (zero_lt_one.trans hz.1).le (power j))
    have he:‖scalar j‖^2*(Cf*profile*((C j).absNorm:ℝ)^(εmass-1))*weight j*Z^(power j)=
        Cf*profile*(balancedFirstHighMass reflected s modifier R seed W D Z ξ εmass hK bin (column j)*weight j*Z^(power j)) := by
      dsimp only [balancedFirstHighMass,scalar,C,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    rw [he] at hh'
    exact hh'.trans ((mul_le_mul_of_nonneg_left (hpay power E hp j) (mul_nonneg hCf (sq_nonneg _))).trans_eq (by ring))
  constructor
  · have hb:=hz.2 s modifier R seed (Z^D) ξ hK bin hs hs0 hz₁ hz₂ hsource J column hinj hlive hcap
      (Cz*profile*factor) Ezero
      (fun j=>‖scalar j‖^2*zeroAllocationFactor s (C j) R (alloc j) (τ j) (t j) Cann εzero W₁ W₂*
        weight j*Z^(pzero j)/((column j).2.1.val.absNorm:ℝ))
      (mul_nonneg (mul_nonneg hCz.le (sq_nonneg _)) hfactor)
      (point _ Cz hCz.le (fun j=>(ha j).1) pzero Ezero hpz)
    exact hb.trans_eq (by dsimp only [profile];ring)
  · have hb:=hz.2 s modifier R seed (Z^D) ξ hK bin hs hs0 hz₁ hz₂ hsource J column hinj hlive hcap
      (Ct*profile*factor) Etail
      (fun j=>‖scalar j‖^2*tailAllocationFactor s (C j) R (alloc j) (τ j) (t j) W₁ W₂*
        weight j*Z^(ptail j)/((column j).2.1.val.absNorm:ℝ))
      (mul_nonneg (mul_nonneg hCt.le (sq_nonneg _)) hfactor)
      (point _ Ct hCt.le (fun j=>(ha j).2) ptail Etail hpt)
    exact hb.trans_eq (by dsimp only [profile];ring)

end
end QRH.Record1252270103Source.MarkedMainRemainder
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.scalar_power_payment
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.selected_remainder_sums
