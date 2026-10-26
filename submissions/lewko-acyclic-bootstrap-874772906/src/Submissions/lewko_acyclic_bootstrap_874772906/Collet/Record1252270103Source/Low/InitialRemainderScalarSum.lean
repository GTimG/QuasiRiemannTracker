/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected first-column remainder sums after pool, allocation and label
counting. The only outstanding admissions are geometric and numerical. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.InitialRemainderScalar
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.ExceptionalInitialGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.InitialRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
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
local notation "O"=>HeckeFamily.O

theorem zero_power_identity (Z H V e : ℝ) (hZ : 1<Z) (hH : 0<H) (hV : 0<V) :
    Z^(Real.logb Z H+e*Real.logb Z V)=H*V^e := by
  rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hH,
    mul_comm e,Real.rpow_mul (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hV]

theorem tail_power_identity (Z H saving : ℝ) (hZ : 1<Z) (hH : 0<H) :
    Z^(Real.logb Z H-saving)=H*Z^(-saving) := by
  rw [sub_eq_add_neg,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hH]

private theorem zero_restore (k sc band card P rad f pc h q v d : ℝ) (hk : k≠0) :
    sc*(band*card/P*rad)*f*pc^2*h*q*v/d =
      k/16*(sc*(card*f*(4*pc)^2*q)*(band*P⁻¹*rad/k)*(h*v)/d) := by
  calc
    _=(k*k⁻¹)*(sc*(band*card/P*rad)*f*pc^2*h*q*v/d):=by rw [mul_inv_cancel₀ hk,one_mul]
    _=_:=by ring

private theorem tail_restore (k sc band card P rad f pc h q v d : ℝ) (hk : k≠0) :
    sc*(band*card/P*rad)*f*pc^2*h*q*v/d =
      k/4*(sc*(card*f*(2*pc)^2*q)*(band*P⁻¹*rad/k)*(h*v)/d) := by
  calc
    _=(k*k⁻¹)*(sc*(band*card/P*rad)*f*pc^2*h*q*v/d):=by rw [mul_inv_cancel₀ hk,one_mul]
    _=_:=by ring

/-- Constants precede all moving inputs, first and second profiles, selected
columns, allocations and heights. This pays the actual arithmetic sums. -/
theorem eventual_actual_remainder_sums (N : ℕ) (Cs Cann ell epsMass epsZero epsCount : ℝ)
    (hCs : 1≤Cs) (hCann : 0<Cann) (hell : 0<ell)
    (hmass : 0<epsMass) (hzero : 0≤epsZero) (hcount : 0<epsCount) :
    ∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι)(modifier : Tuple ι→ℂ)(R seed : Ideal O)
      (W W₁ W₂ : 𝓢(ℝ,ℂ))(ξ a reserve allowance loss saving : ℝ)(hK : 0<Z^(1:ℝ)),
      Fintype.card ι≤N→(∀i,s.M i≤Cs)→s.upper≤2→1≤s.lower→
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^(2:ℝ)→
      (∀x,s.W₁ x≠0→(1/4:ℝ)≤x)→(∀x,s.W₂ x≠0→(1/4:ℝ)≤x)→
      0≤a→0≤allowance→Real.logb Z (volume s)+6*a+3*allowance≤1→
      frequencyLoss Z 32 ξ+reserve+2*epsMass+loss+epsZero≤2*allowance→
    ∀(P : Finset (Ideal O))(mesh BD Bsource : ℝ)(depth : ℕ),
      FixedCellPoolData P Z a ell mesh loss BD Bsource depth→
    ∀(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s modifier R seed (Z^(1:ℝ)) Z ξ hK bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R seed (Z^(1:ℝ)) Z ξ hK bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^(4:ℝ))→
    let C:=fun j=>geometryColumnIdeal reflected s modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j)
    let label:=fun j=>FirstFamily.firstLabel s modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j)
    let Hmain:=fun j=>firstMainRadius reflected (Z^(1:ℝ)) (volume s) Z ξ (3*a) reserve (label j)
    let radius:=fun j=>literalFirstRadius reflected (Z^(1:ℝ)) (volume s) Z ξ reserve (label j)
    let H0:=fun j=>(geometryFirstSource s modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j).1).H0
    let scalar:=fun j=>balancedColumnScalar reflected s modifier R seed (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) hK bin (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^(1:ℝ)) Z ξ q)) (column j)
    let factor:=geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin
    (∀j,0≤radius j+6*a)→(∀j,radius j+6*a≤32)→
    ∀(alloc : ∀j,actualAllocations s.pools (C j))(τ : J→Character)(t : J→ℝ),
      (∀j,frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P≠0)→
    let amplitude:=fun j=>‖scalar j‖^2*
      (((bands (H0 j)).card:ℝ)*((actualAllocations s.pools (C j)).card:ℝ)^2/(P.card:ℝ)*
        ((radius j+6*a)/ell))*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) W₁ W₂)^2*
        Hmain j*(Cann/((C j).absNorm:ℝ))^(1+epsZero)*(volume s)^epsZero/
          ((column j).2.1.val.absNorm:ℝ))≤
      Czero*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*factor*
        Z^(-a-allowance+2*epsCount)/(seed.absNorm:ℝ)) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) W₁ W₂)^2*
        Hmain j*(volume (child s (C j) R (alloc j) (τ j) (t j))/volume s)*Z^(-saving)/
          ((column j).2.1.val.absNorm:ℝ))≤
      Ctail*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*factor*
        Z^(-a-allowance-saving+2*epsCount)/(seed.absNorm:ℝ)) := by
  obtain ⟨Cz,Ct,hCz,hCt,hbound⟩:=selected_remainder_sums N Cs 2 Cann 1 (1/4) 2 4
    epsMass epsZero epsCount hCs (by norm_num) hCann (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hmass hzero hcount
  have hcw:=weightConstant_pos ell hell
  refine ⟨weightConstant ell/16*Cz,weightConstant ell/4*Ct,by positivity,by positivity,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s modifier R seed W W₁ W₂ ξ a reserve allowance loss saving hK
    hN hM hu hlo hs hs0 hz₁ hz₂ hsource hs₁ hs₂ ha he hgap herr P mesh BD Bsource depth hpool
    reflected bin J _ column hinj hlive hcap C label Hmain radius H0 scalar factor hr0 hr
    alloc τ t hf amplitude
  have hH0 (j:J):0<H0 j := lt_trans zero_lt_one
    (actual_first_H0_and_frequency s modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j)).1
  let weight:=fun j=>mainWeight P ell (H0 j) (radius j) a/weightConstant ell
  have hw (j:J):0≤weight j ∧ weight j≤Z^(-a+loss):=
    normalized_pool_weight P Z a ell mesh loss BD Bsource depth hpool hell (H0 j) (radius j)
      (hH0 j) (hr0 j) (hr j)
  have hp (j:J):=actual_remainder_admissions reflected s modifier R seed Z ξ a reserve allowance
    2 epsMass epsZero loss saving (weight j) hz.1 hK bin (column j) ha he hzero hgap herr (hw j).2
  have hb:=hz.2 s modifier R seed W W₁ W₂ 1 ξ hK hN hM hu hlo hs hs0 hz₁ hz₂
    hsource hs₁ hs₂ reflected bin J column hinj hlive hcap alloc τ t weight
      (fun j=>Real.logb Z (Hmain j)+epsZero*Real.logb Z (volume s))
      (fun j=>Real.logb Z (Hmain j)-saving) (-a-allowance) (-a-allowance-saving)
      hf (fun j=>(hw j).1) (fun j=>(hp j).1) (fun j=>(hp j).2)
  have hH (j:J):0<Hmain j := by
    dsimp only [Hmain]
    rw [←literal_first_main_radius]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans hz.1) _
  have hcne:=ne_of_gt hcw
  constructor
  · have hh:=mul_le_mul_of_nonneg_left hb.1 (by positivity : 0≤weightConstant ell/16)
    refine (show _=weightConstant ell/16*(_) from ?_).trans_le (hh.trans_eq (by ring))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [zero_power_identity Z (Hmain j) (volume s) epsZero hz.1 (hH j) (volume_pos s)]
    dsimp only [amplitude,weight,mainWeight,zeroAllocationFactor]
    exact zero_restore _ _ _ _ _ _ _ _ _ _ _ _ hcne
  · have hh:=mul_le_mul_of_nonneg_left hb.2 (by positivity : 0≤weightConstant ell/4)
    refine (show _=weightConstant ell/4*(_) from ?_).trans_le (hh.trans_eq (by ring))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [tail_power_identity Z (Hmain j) saving hz.1 (hH j)]
    dsimp only [amplitude,weight,mainWeight,tailAllocationFactor]
    exact tail_restore _ _ _ _ _ _ _ _ _ _ _ _ hcne

end
end QRH.Record1252270103Source.Low.InitialRemainder
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.zero_power_identity
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.tail_power_identity
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.eventual_actual_remainder_sums
