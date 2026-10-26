/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal selected two-stage weights enter the same balanced first mass and
second allocation coefficient used by the checked cofactor suppliers. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedMass
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMainPrefactor
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowPaid
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstSourceReduction Cycle61InitialMass Cycle61Moment Record1252270103Second
open OAI.SevenEighths.Record1252270103Source
open Admission.SelectedHighCofactorFamily Admission.SelectedHighCofactorCoordinates
local notation "O"=>HeckeFamily.O
local instance selectedMassDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

open Filter Record12518109Natural CenteredMomentOriginalCommonHarmonic
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical
theorem eventual_selected_paid_weight (N:ℕ)(lo ap errv:ℝ)
    (hlo:0<lo)(hap:0<ap)(herrv:0<errv):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α:Type}[Fintype α],
    ∀(s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))
    (D ξ amp reserve ε:ℝ)(hZ:1<Z)(hK:0<Z^D)(hε:0≤ε)
    (bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
    (C₂ D₂:Ideal O)(hC₂:Supported C₂)(U:Finset (CommonIndex C₂ D₂))
    (sel:Selection s reflected second (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j) C₂ D₂ R)
    (extra lower ω:ℝ)(he:0≤extra)(hl:0<lower)
    (hω:ω≤
      (‖CoupledFirst.balancedColumnScalar reflected s modifier R seed (Z^D) Z ξ D
        (Real.logb Z (volume s)) hK bin
        (fun q=>normPhase (CoupledFirst.coordinateBlock s modifier R seed W (Z^D) Z ξ q)) j‖^2*
      extra*‖frozenCoefficient sel.B₁.val
        (if reflected then (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j).1.2
          else (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j).1.1)
        R s.ν s.W s.P‖^2/volume s)*
      (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve
        (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j)/lower)*
      normalizer C₂ D₂ U),
    ∀(B err:ℝ), Fintype.card α≤N → lo≤s.lower → Squarefree seed →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
    let l:=Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U
      Z D (Real.logb Z (volume s)) amp ξ reserve err) errv
    selectedPaidWeight sel ω≤
      (extra*((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)^2*
        Z^amp/lower*forcedProfileCost s)*
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      (max 1 (forcedProfileCost s))^2 *
      Z^(B*ε+x 0-balancedGeometrySide reflected (Real.logb Z (volume s))
        (CoupledFirst.geometryExponents s modifier R seed (Z^D) Z ξ j.1.val)) := by
  filter_upwards [eventual_modified_normalized_cofactor N lo errv hlo herrv] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ s modifier R seed W D ξ amp reserve ε hZ hK hε bin reflected second j C₂ D₂ hC₂ U
    sel extra lower ω he hl hω B err hN hlower hs hz₁ hz₂ hsource hs₁ hs₂ l x
  let pref:=extra*((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)^2*
    Z^amp/lower*forcedProfileCost s
  let fac:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  let pc:=(max 1 (forcedProfileCost s))^2
  let side:=balancedGeometrySide reflected (Real.logb Z (volume s))
    (CoupledFirst.geometryExponents s modifier R seed (Z^D) Z ξ j.1.val)
  have hfac:0<fac:=geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)
  have hpref:0≤pref:=mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg he (sq_nonneg _))
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hl.le) (forcedProfileCost_nonneg s)
  have hpc:0≤pc:=sq_nonneg _
  have hb:=hz.2 s hN hlower modifier R seed (Z^D) ξ hK bin j reflected second
    sel.B₁ sel.τ₁ sel.t₁ sel.hf₁ D amp reserve err
    C₂ D₂ hC₂ U sel.B₂ sel.τ₂ sel.t₂ 0 0 0 0
  have hb0:0≤sel.raw U Z D amp ξ reserve:=by
    rw [show sel.raw U Z D amp ξ reserve=sel.denom*(sel.raw U Z D amp ξ reserve/sel.denom) from hb.2.2]
    exact mul_nonneg sel.denom_pos.le hb.1
  have hraw:sel.raw U Z D amp ξ reserve≤pc*Z^(x 0):=by
    calc
      _=sel.denom*(sel.raw U Z D amp ξ reserve/sel.denom):=hb.2.2
      _≤pc*Z^(x 0):=mul_le_mul sel.denom_le_original hb.2.1 hb.1 hpc
  have hm:=CoupledFirst.actual_balanced_uniform_high_mass reflected N lo ap hlo hap
    s modifier R seed W D Z ξ B ε hZ hK hε hN hlower hs hz₁ hz₂ hsource hs₁ hs₂ bin j
  have hweight:=actual_selected_paid_weight s modifier R seed W D Z ξ amp reserve ε
    (zero_lt_one.trans hZ) hK hε bin reflected second j C₂ D₂ hC₂ U sel extra lower ω he hl hω
  have hproduct:=mul_le_mul hm hraw hb0 (by positivity : 0≤fac*Z^(B*ε)/Z^side)
  apply hweight.trans
  have hh:=mul_le_mul_of_nonneg_left hproduct hpref
  change pref*CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ ε hK bin j*
      sel.raw U Z D amp ξ reserve≤pref*fac*pc*Z^(B*ε+x 0-side)
  calc
    _=pref*(CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ ε hK bin j*
      sel.raw U Z D amp ξ reserve):=by ring
    _≤pref*((fac*Z^(B*ε)/Z^side)*(pc*Z^(x 0))):=hh
    _=pref*fac*pc*Z^(B*ε+x 0-side):=by
      rw [Real.rpow_sub (zero_lt_one.trans hZ),Real.rpow_add (zero_lt_one.trans hZ)]
      ring

theorem uniform_selected_paid_weight (N:ℕ)(lo ap errv B₁ B₂ εpref ell lower radiusMax:ℝ)
    (hlo:0<lo)(hap:0<ap)(herrv:0<errv)(hB₁:0≤B₁)(hB₂:0≤B₂)(hεpref:0<εpref)
    (hell:0<ell)(hlower:0<lower)(hmax:0≤radiusMax):
    ∃C:ℝ,0<C ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α:Type}[Fintype α],
    ∀(s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))
    (D ξ amp reserve ε:ℝ)(hZ:1<Z)(hK:0<Z^D)(hε:0≤ε)
    (bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
    (C₂ D₂:Ideal O)(hC₂:Supported C₂)(U:Finset (CommonIndex C₂ D₂))
    (sel:Selection s reflected second (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j) C₂ D₂ R)
    (extra ω:ℝ)(he:0≤extra)
    (hω:ω≤
      (‖CoupledFirst.balancedColumnScalar reflected s modifier R seed (Z^D) Z ξ D
        (Real.logb Z (volume s)) hK bin
        (fun q=>normPhase (CoupledFirst.coordinateBlock s modifier R seed W (Z^D) Z ξ q)) j‖^2*
      extra*‖frozenCoefficient sel.B₁.val
        (if reflected then (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j).1.2
          else (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j).1.1)
        R s.ν s.W s.P‖^2/volume s)*
      (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve
        (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j)/lower)*
      normalizer C₂ D₂ U),
    ∀(B err:ℝ), Fintype.card α≤N → lo≤s.lower → Squarefree seed →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
    let l:=Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U
      Z D (Real.logb Z (volume s)) amp ξ reserve err) errv
    ∀(P:Finset (Ideal O))(mesh poolLoss BD Bsource:ℝ)(depth:ℕ)(H0 radius:ℝ),
      Pool.FixedCellPoolData P Z amp ell mesh poolLoss BD Bsource depth →
      0<H0 → 0≤radius+6*amp → radius+6*amp≤radiusMax →
      extra=((CenteredMomentFirstAnnularMajorant.bands H0).card:ℝ)*
        ((actualAllocations s.pools (if reflected then l.1.2 else l.1.1)).card:ℝ)^2/(P.card:ℝ)*
        ((radius+6*amp)/ell) →
      ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)≤Z^B₁ →
      ((if second then D₂ else C₂).absNorm:ℝ)≤Z^B₂ →
    selectedPaidWeight sel ω≤
      C*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      forcedProfileCost s*(max 1 (forcedProfileCost s))^2 *
      Z^(εpref+poolLoss+B*ε+x 0-balancedGeometrySide reflected (Real.logb Z (volume s))
        (CoupledFirst.geometryExponents s modifier R seed (Z^D) Z ξ j.1.val)) := by
  obtain ⟨C,hC,hpref⟩:=MarkedMainPrefactor.uniform_main_prefactor N B₁ B₂ εpref ell lower radiusMax
    hB₁ hB₂ hεpref hell hlower hmax
  refine ⟨C,hC,?_⟩
  filter_upwards [eventual_selected_paid_weight N lo ap errv hlo hap herrv] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ s modifier R seed W D ξ amp reserve ε hZ hK hε bin reflected second j C₂ D₂ hC₂ U
    sel extra ω he hω B err hN hslo hs hz₁ hz₂ hsource hs₁ hs₂ l x P mesh poolLoss BD Bsource depth
    H0 radius hpool hH0 hrad0 hrad hextra hc₁ hc₂
  have hn₁:Fintype.card (liveIndices sel.B₁.val)≤N:=
    (Fintype.card_le_of_injective (fun i:liveIndices sel.B₁.val=>i.val) Subtype.val_injective).trans hN
  have hp:=hpref s sel.firstInput hN hn₁
    (if reflected then l.1.2 else l.1.1) (if second then D₂ else C₂) P Z amp mesh poolLoss BD Bsource depth
    (CenteredMomentAmplificationChildSourceCaps.allocation_ne s _ sel.B₁)
    (CenteredMomentAmplificationChildSourceCaps.allocation_ne sel.firstInput _ sel.B₂)
    hc₁ hc₂ hpool H0 radius hH0 hrad0 hrad
  have hp':extra*((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)^2*
      Z^amp/lower≤C*Z^(εpref+poolLoss):=by
    rw [hextra]
    convert hp using 1 <;> ring
  have hb:=hz.2 s modifier R seed W D ξ amp reserve ε hZ hK hε bin reflected second j C₂ D₂ hC₂ U
    sel extra lower ω he hlower hω B err hN hslo hs hz₁ hz₂ hsource hs₁ hs₂
  let fac:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  let pc:=(max 1 (forcedProfileCost s))^2
  let side:=balancedGeometrySide reflected (Real.logb Z (volume s))
    (CoupledFirst.geometryExponents s modifier R seed (Z^D) Z ξ j.1.val)
  have hfac:0<fac:=geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)
  have hpc:0≤pc:=sq_nonneg _
  have hp'':(extra*((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)^2*
      Z^amp/lower*forcedProfileCost s)*fac*pc*Z^(B*ε+x 0-side)≤
      C*fac*forcedProfileCost s*pc*Z^(εpref+poolLoss+B*ε+x 0-side):=by
    have h:=mul_le_mul_of_nonneg_right hp'
      (mul_nonneg (mul_nonneg (mul_nonneg (forcedProfileCost_nonneg s) hfac.le) hpc)
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le (B*ε+x 0-side)))
    calc
      _=(extra*((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)^2*
          Z^amp/lower)*(forcedProfileCost s*fac*pc*Z^(B*ε+x 0-side)):=by ring
      _≤(C*Z^(εpref+poolLoss))*(forcedProfileCost s*fac*pc*Z^(B*ε+x 0-side)):=h
      _=C*fac*forcedProfileCost s*pc*Z^(εpref+poolLoss+B*ε+x 0-side):=by
        simp only [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_sub (zero_lt_one.trans hZ)]
        ring
  exact hb.trans hp''

end
end QRH.Record1252270103Source.Admission.SelectedLowPaid
#print axioms QRH.Record1252270103Source.Admission.SelectedLowPaid.eventual_selected_paid_weight
#print axioms QRH.Record1252270103Source.Admission.SelectedLowPaid.uniform_selected_paid_weight
