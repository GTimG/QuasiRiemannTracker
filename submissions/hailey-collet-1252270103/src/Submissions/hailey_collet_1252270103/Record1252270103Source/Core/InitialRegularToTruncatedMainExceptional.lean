/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The first radial profile and the second ball profile are independent.
The actual MAIN correction is evaluated at the child column (frozen factor one).
The literal initial complementary family, with its first frozen coefficients,
is paid by the checked second radical sum and the original first MAIN scalar.
All constants precede the moving profiles, scales, widths and heights. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Contraction.SelectedMainExceptionalAggregate
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFrozenOne
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFirstErrors

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CompletedGauss RayFourExpansion CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentSecondInputCapacitySource CenteredMomentSecondWindowBudget
open CenteredMomentFirstSectors CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSourceRow CenteredMomentFirstPhysicalSource CenteredMomentSupport
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstCanonicalFamily
open Cycle61Moment Cycle61InitialMass Record12518109Natural
open Record1252270103Finite Record1252270103StepScalar Record1252270103Second
open QRH.Record1252270103Low OAI.SevenEighths.Record1252270103Source.Collision
open High.CoupledFirst Admission.FirstFamily Pool InitialPhysical InitialTruncated
open Low.SelectedExceptionalNormalized
open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
local notation "O"=>HeckeFamily.O
local notation "source"=>High.CoupledFirst.geometryFirstSource
local instance twoProfileJointDecidableEq {α:Type*}:DecidableEq α:=Classical.decEq _

theorem eventually_initial_main_joint {α:Type}[Fintype α]
    (N:ℕ)(hN:Fintype.card α≤N)(K:ℚ)(n low:Source)(b:ℝ)
    (hg:RealGeometry K n low b)(hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))(hcap:(n.cap:ℝ)≤1)
    (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)
    (hH:RayOrthogonality.globalUnits rayM≤H)
    (Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (η η₀:Character)(R₀:Ideal O)(hR:R₀≠0)
    (Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (ell mesh poolLoss ξ reserve width radiusMax:ℝ)(depth:ℕ)
    (hmesh:0≤mesh)(hgap:mesh<ell)(hell:ell<sourceAReal n low b)(hloss:0<poolLoss)
    (hξ:0<ξ)(hξ1:ξ≤1)(hreserve:0≤reserve)(hdepth:(2:ℝ)/ell≤depth)
    (hradius:0≤radiusMax)(he:0<(n.allowance:ℝ))
    (hξstep:ξ≤PhysicalLowGuard.step n)(hrstep:reserve≤PhysicalLowGuard.step n)
    (hwstep:width≤PhysicalLowGuard.step n)
    (W Wsecond:𝓢(ℝ,ℂ))(decay:ℕ)(ε εL δ epsMass epsCount epsCard:ℝ)
    (hε:0<ε)(hεL:0<εL)(hδ:0<δ)(hεm:0<epsMass)(hεc:0<epsCount)(hεa:0<epsCard)
    (hsmall:epsCard+poolLoss+ξ/12≤PhysicalLowGuard.step n):
    ∀Q:Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃Ctotal:ℝ,0<Ctotal ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{Label:Type}[Fintype Label],
    ∀(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t:ℝ)
      (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
      (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂),
    (∀i,0≤w i)→(∀i,w i≤mesh)→
    (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1→
    b-(n.allowance:ℝ)-width≤∑i,w i→(∑i,w i)≤b→
    1≤Y₂→Y₂≤X₁→Y₂≤X₂→Y₂=Z^(49/100-(K:ℝ)*b)→
    let s:=initialInput rayM H hH Wslot hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    let modifier:=markedSourceModifier 1 1 1 1 (fun _=>1)
    ∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
      (column:Label→FirstColumnIndex (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)),
    Function.Injective (fun j=>(firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column j),
      (column j).2.1.val))→
    ∀hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)
      (fun _=>logAnnulus),
    (∀l,((column l).2.1.val.absNorm:ℝ)≤Z^(4:ℝ))→
    let hseed:∀l,Squarefree (column l).2.1.val:=fun l=>
      live_projector_squarefree s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin
        (fun _=>logAnnulus) (column l) (hLive l)
    let C:=fun l=>columnIdeal reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let scalar:=fun l=>balancedColumnScalar reflected s modifier R₀ 1 Z Z ξ 1
      (Real.logb Z (volume s)) (zero_lt_one.trans hZ) bin
      (fun q=>normPhase (coordinateBlock s modifier R₀ 1 W Z Z ξ q)) (column l)
    let amp:=sourceAReal n low b
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    ∀(alloc:∀l,actualAllocations s.pools (C l))(ht H0 radius:Label→ℝ)(height:ℝ)
      (χ₀:Label→RayCharacter),0≤height→(∀l,‖ht l‖≤height)→
      (∀l,0<H0 l)→(∀l,0≤radius l+6*amp)→(∀l,radius l+6*amp≤radiusMax)→
    let extra:=fun l=>((bands (H0 l)).card:ℝ)*((actualAllocations s.pools (C l)).card:ℝ)^2/
      (P.card:ℝ)*((radius l+6*amp)/ell)
    let amplitude:=fun l=>‖scalar l‖^2*extra l*‖frozenCoefficient (alloc l).val (C l) R₀ s.ν s.W s.P‖^2
    let m:=fixedBadMask*idealGenerator R₀
    let τ:=fun l=>columnCharacter reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let labels:=fun l=>firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let Kmain:=fun l=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (labels l)
    let Tsec:=fun l=>firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (labels l)
    let f:=InitialRegularToTruncated.mainAllocatedFamily s Wsecond (p.profile 0) (p.profile 1) Z R₀ C (fun l=>(column l).2.1.val)
      alloc τ ht P hseed (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
      Kmain Tsec (fun _=>volume s) amplitude ξ
      (fun l=>first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve (zero_lt_one.trans hZ) (labels l)) χ₀ m
    ‖∑q,f.phase Q q*(f.block Q q).value Wsecond‖≤
      Ctotal*(p.control S)^2*(1+height)^degree*
        geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        Z^(-(n.highFee:ℝ)-4*amp+2*epsCount+epsMass+δ+4*εL+2*ε) := by
  have hL0:0≤(n.L:ℝ):=zero_le_one.trans hL
  have hel:0<ell:=hmesh.trans_lt hgap
  have hlower:=lowerFactor_pos N (1:ℝ) (1/4) (by norm_num) (by norm_num)
  obtain ⟨Cp,hCp,hpaid⟩:=selected_frozen_first_sum_one N 1 (1/4) 2 4 epsCount epsCard ell
    (lowerFactor N 1 (1/4)) radiusMax (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hεc hεa hel hlower hradius
  have hfull:=Contraction.SelectedMainExceptional.eventually_initial_family_uniform N hN
    (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hB hL hcap rayM H hH Wslot hW hsW η η₀ R₀ hR Sbad hbad
    (sourceAReal n low b) ell mesh poolLoss ξ reserve depth hmesh hgap hell hloss hξ.le hξ1
    hreserve hdepth Wsecond decay ε εL δ epsMass hε hεL hδ hεm
  intro Q hQ0 hQ hQ72
  obtain ⟨degree,S,Ce,hCe,hfull⟩:=hfull Q hQ0 hQ hQ72
  let Cprofile:=((initialSlotBound Wslot hW hsW)^N)^2*(2:ℝ)^N
  have hprofile:0<Cprofile:=by
    have hh:=initialSlotBound_ge_one Wslot hW hsW
    dsimp only [Cprofile]
    positivity
  refine ⟨degree,S,Ce*Cp*Cprofile,by positivity,?_⟩
  have hcapsEv:=eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hB hL hcap
  have hpoolEv:=eventually_fixed_cell_pool rayM H hH Sbad hbad (sourceAReal n low b) ell mesh poolLoss 12 2 depth
    hmesh hgap hell hloss
  have herrEv:=eventually_centered_error_guard n low ξ reserve (epsCard+poolLoss+ξ/12) width he hL0 hξ
    hξstep hreserve hrstep hsmall hwstep
  refine (hfull.and (hpaid.and (hcapsEv.and (hpoolEv.and herrEv)))).mono ?_
  rintro Z ⟨hz,hp,hcaps,hpool,herr⟩
  refine ⟨hz.1,?_⟩
  intro hZ Label instLabel θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hw hwm hadm hwlo hwhi hy₂ hl₁ hl₂ hY s modifier reflected bin column hinj hLive hseedcap
    hseed C scalar amp P alloc ht H0 radius height χ₀ hheight hht hH0 hr0 hr extra amplitude m τ labels Kmain Tsec f
  have hZ0:=zero_lt_one.trans hZ
  have hrad:=hcaps.2 hZ rayM H hH Wslot hW hsW η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hN hw hadm hy₂ hl₁ hl₂
  have hlog:=initial_log_volume_node_bound rayM H hH Wslot hW hsW Z hZ0 η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod n b width hZ hL0 hadm hwlo hwhi
  have hforce:= (initial_cost_bounds rayM H hH Wslot hW hsW Z hZ0 η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod N hN).2
  have ha (l:Label):0≤amplitude l:=by
    have he0:0≤extra l:=mul_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
      (div_nonneg (hr0 l) hel.le)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) he0) (sq_nonneg _)
  have hnorm:=hz.2 hZ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hw hwm hadm
    hy₂ hl₁ hl₂ reflected modifier bin column (fun _=>logAnnulus) hLive alloc ht amplitude χ₀ ha
  have hprice:=hp.2 s 1 1 1 1 R₀ 1 (fun _=>1) W K n low b ξ reserve poolLoss
    ((n.L:ℝ)*width) hg hN (by change (1:ℝ)≤1;exact le_rfl) (by simp) (by simp)
    (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
    hrad.2.1 (fun x hx=>(p.support 0 hx).1) (fun x hx=>(p.support 1 hx).1)
    hlog (herr.2 K b hg) hZ reflected bin
  have hsum:=hprice Label column hinj hLive hseedcap alloc τ ht H0 radius P mesh 12 2 depth
    hpool hH0 hr0 hr
  let price:Label→ℝ:=fun l=>(amplitude l/volume s)*(Kmain l/lowerFactor N 1 (1/4))*
    (max 1 (Y₂/((C l).absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*
    volume (f.input l)*(4*frequencyRadius (Tsec l) Z ξ)^(1/6:ℝ)/((column l).2.1.val.absNorm:ℝ)
  have hsum':(∑l,price l)≤Cp*forcedProfileCost s*
      geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
      Z^(-(n.highFee:ℝ)-4*amp+2*epsCount):=by
    rw [←hY] at hsum
    have hunit:((1:Ideal O).absNorm:ℝ)=1:=by simp
    simp only [hunit,div_one] at hsum
    convert hsum using 1 <;> rfl
  have hside:0≤geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin:=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hsum'':(∑l,price l)≤Cp*Cprofile*
      geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
      Z^(-(n.highFee:ℝ)-4*amp+2*epsCount):=by
    apply hsum'.trans
    gcongr
  have hterm (l:Label):0≤price l:=by
    have hh:=ha l
    have hv:=volume_pos s
    have hc:=volume_pos (f.input l)
    have hk:0<Kmain l:=first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve hZ0 (labels l)
    have hT:0≤Tsec l:=by
      change 0≤_ ^ 2 / Kmain l
      exact div_nonneg (sq_nonneg _) hk.le
    have hrad0:0≤4*frequencyRadius (Tsec l) Z ξ:=
      mul_nonneg (by norm_num) (mul_nonneg hT (Real.rpow_nonneg hZ0.le _))
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (div_nonneg hh hv.le) (div_nonneg hk.le hlower.le))
      (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) hc.le)
      (Real.rpow_nonneg hrad0 _)) (Nat.cast_nonneg _)
  have hpoint(l:Label):
      (amplitude l/volume s)*(Kmain l/lowerFactor N 1 (1/4))*volume (f.input l)*
        (4*frequencyRadius (Tsec l) Z ξ)^(1/6:ℝ)*
        (max 1 (Y₂/((C l).absNorm:ℝ)))^(-2*(499/1000:ℝ))*(1+‖ht l‖)^degree/
        ((column l).2.1.val.absNorm:ℝ)≤price l*(1+height)^degree:=by
    have hpow:(1+‖ht l‖)^degree≤(1+height)^degree:=
      pow_le_pow_left₀ (by positivity : 0≤1+‖ht l‖) (add_le_add (le_refl (1:ℝ)) (hht l)) degree
    convert mul_le_mul_of_nonneg_left hpow (hterm l) using 1 <;>
      dsimp only [price] <;> ring
  have hsumheight:=Finset.sum_le_sum (s:=Finset.univ) (fun l _=>hpoint l)
  rw [←Finset.sum_mul] at hsumheight
  have htotal:=hnorm.trans (mul_le_mul_of_nonneg_left
    (hsumheight.trans (mul_le_mul_of_nonneg_right hsum'' (by positivity)))
    (show 0≤Ce*(p.control S)^2*Z^(epsMass+δ+4*εL+2*ε) by positivity))
  convert htotal using 1
  rw [show -(n.highFee:ℝ)-4*amp+2*epsCount+epsMass+δ+4*εL+2*ε=
    (epsMass+δ+4*εL+2*ε)+(-(n.highFee:ℝ)-4*amp+2*epsCount) by ring,
    Real.rpow_add hZ0]
  ring

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.eventually_initial_main_joint
