/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal first MAIN selection is paid by the full kept and complementary
second norms and the actual zero/tail sums, at their original profiles. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedBalancedContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedMain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedSecond
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedMainExceptionalSaving
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialTruncatedControl
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedRemainderOne

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentSourceMass CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentLogDyadic
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentEnergyBandMonotonicity
open Cycle61InitialMass RayFourExpansion Record1252270103Finite Record1252270103StepScalar
open Record1252270103Second SecondSectorDatum
open QRH.Record1252270103Low High.CoupledFirst High.GlobalPhysical Admission.FirstFamily
open OAI.SevenEighths.Record1252270103Source.Collision
open Low.SelectedExceptionalNormalized Low.SelectedExceptionalInitialCaps Low.InitialRemainder
open Admission.SelectedSecondNatural InitialPhysical InitialTruncated ExceptionalPrice Pool
local notation "O" => HeckeFamily.O
local notation "source" => High.CoupledFirst.geometryFirstSource
local instance balancedInitialDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

private theorem control_payment (C U V G H X:ℝ)
    (hC:0≤C)(hU:0≤U)(hUV:U≤V)(hG:0≤G)(hH:0≤H)(hX:0≤X) :
    C*U^2*G*H*X≤C*V^2*G*H*X := by
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hU hUV 2) hC) hG) hH) hX

private theorem mixed_control_payment (C U V G H J X:ℝ)
    (hC:0≤C)(hU:0≤U)(hUV:U≤V)(hG:0≤G)(hH:0≤H)(hHJ:H≤J)(hX:0≤X) :
    C*U^2*H*G*X≤C*V^2*G*J*X := by
  have h:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU hUV 2) hC)
      hHJ hH (mul_nonneg hC (sq_nonneg V))) hG) hX
  convert h using 1 <;> ring

theorem balanced_of_regular (K:ℚ)(n low:Source)(b mesh ξ reserve width:ℝ)
    (hg:RealGeometry K n low b)(hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))(hc:(n.cap:ℝ)≤1)
    (hlow:(low.B:ℝ)≤1)(he:0<(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))
    (hm0:0≤mesh)(hm:mesh<sourceAReal n low b/2)
    (hx:0<ξ)(hx1:ξ≤1)(hxstep:ξ≤PhysicalLowGuard.step n)
    (hr0:0≤reserve)(hr1:reserve≤1)(hrstep:reserve≤PhysicalLowGuard.step n)
    (hw:width≤PhysicalLowGuard.step n)
    (hregular:RegularJointSupplier K n low b mesh ξ reserve width):
    BalancedInitialSupplier K n low b mesh ξ width := by
  intro α instα instDec rayM instRay H hH Wslot hW hsW bΦ hbΦ η η₀ Q hQr hQ0 hQtop hQ72 R₀ hR
  let N:=Fintype.card α
  let amp:=sourceAReal n low b
  let ell:=amp/2
  have ha:0<amp:=hg.a_pos
  have hel:0<ell:=by dsimp only [ell];positivity
  have helamp:ell<amp:=by dsimp only [ell];linarith
  have hL0:0≤(n.L:ℝ):=zero_le_one.trans hL
  obtain ⟨dr,Sr,hSr,Cr,τ,σ,hCr,hτ,hσ,hreg⟩:=hregular α rayM H hH Wslot hW hsW bΦ hbΦ
    η η₀ Q hQr hQ0 hQtop hQ72 R₀ hR
  obtain ⟨e,he0,heSmall,hePaid,heAmp,heσ,heRem⟩:=choose_losses n amp σ ξ he hL0 ha hσ hxstep
  obtain ⟨depth,hdepth⟩:=exists_nat_ge ((2:ℝ)/ell)
  let W:=initialRadialBump bΦ (by linarith)
  obtain ⟨de,Se,Ce,hCe,hex⟩:=eventually_initial_main_joint_saved N (le_refl _) K n low b hg hB hL hc
    rayM H hH Wslot hW hsW η η₀ R₀ hR fixedBadPrimes (Finset.Subset.refl _)
    ell mesh e ξ reserve width 32 depth hm0 hm helamp he0 hx hx1 hr0 hdepth (by norm_num)
    he hxstep hrstep hw W ballProfile 0 e e e e e e he0 he0 he0 he0 he0 he0 (by linarith only [heSmall]) hfee
    (by change 2*e+e+e+4*e+2*e≤3*amp;linarith only [hePaid]) (internalQ Q η₀) hQ0 hQtop hQ72
  obtain ⟨Csel,hCsel,hmain⟩:=eventual_selected_main (α:=α) ξ e hx.le he0
  obtain ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,hsecond⟩:=eventual_selected_second N 3 ξ 1 e (by norm_num) hx he0
  obtain ⟨Cz,Ct,hCz,hCt,hrem⟩:=eventual_initial_remainder_sums_one rayM H hH Wslot hW hsW N ell e e e hel he0 he0.le he0
  let S:=Sr∪Se∪{(0,0)}
  have hSrS:Sr⊆S:=fun x hx=>Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hSeS:Se⊆S:=fun x hx=>Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hS:(0,0)∈S:=Finset.mem_union_right _ (Finset.mem_singleton_self _)
  let Cz':=C₀*16*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Cz
  let Ct':=C₁*4*S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Ct
  let Ctotal:=max 1 (Csel*(Cz'+Cr+Ce+Ct'))
  have hCz':0≤Cz':=by dsimp only [Cz'];positivity
  have hCt':0≤Ct':=by dsimp only [Ct'];positivity
  refine ⟨max dr de,S,hS,Ctotal,τ,lt_of_lt_of_le zero_lt_one (le_max_left _ _),hτ,?_⟩
  have hcaps:=eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hB hL hc
  have hgeom:=eventually_initial_first_geometry N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) ξ amp reserve
    hB hL hc hx hx1 ha.le (by have := hg.a_small;dsimp only [amp];linarith) hr0 hr1
  have hpool:=eventually_fixed_cell_pool rayM H hH fixedBadPrimes (Finset.Subset.refl _)
    amp ell mesh e 12 2 depth hm0 hm helamp he0
  have hfreq:=eventually_frequency_loss 32 ξ (by norm_num) hx
  filter_upwards [hreg,hex,hmain,hsecond,hrem,hcaps,hgeom,hpool,hfreq,
    eventually_ge_atTop ((2:ℝ)^(2*N))] with Z hzreg hzex hzmain hzsecond hzrem hzcaps hzgeom hzpool hzfreq hNpow
  refine ⟨hzreg.1,?_⟩
  intro hZ θ w v t ht height hwp hwm hh hv hheight p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi
    Y₂ hy₂ hl₁ hl₂ Y₁ hY₂ hY₁ hprod s modifier Wlocal Nlocal reflected bin
  have hZ0:=zero_lt_one.trans hZ
  have hcaps0:=hzcaps.2 hZ rayM H hH Wslot hW hsW η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod (le_refl _) hwp hadm hy₂ hl₁ hl₂
  have hz₁:s.W₁ 0=0:=initial_plain_zero p (by norm_num) 0
  have hz₂:s.W₂ 0=0:=initial_plain_zero p (by norm_num) 1
  have hscales:∀i,1≤s.P i:=fun i=>Real.one_le_rpow hZ.le (hwp i)
  have hchildcap (j:FirstColumnIndex (source s modifier R₀ 1 Z Z ξ hZ0 bin))
      (B:actualAllocations s.pools (columnIdeal reflected s modifier R₀ 1 Z Z ξ hZ0 bin j)):
      sourceRadius (child s _ R₀ B (columnCharacter reflected s modifier R₀ 1 Z Z ξ hZ0 bin j) ht)≤Z^(2:ℝ):=
    (child_source_radius_le s _ R₀ B _ ht (fun _=>by norm_num [s,initialInput]) hscales
      (by norm_num [s,initialInput]) (by norm_num [s,initialInput])).trans hcaps0.2.1
  have hg0 (j:FirstColumnIndex (source s modifier R₀ 1 Z Z ξ hZ0 bin)):=
    hzgeom.2 hZ rayM H hH Wslot hW hsW η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hprod (le_refl _) hwp hadm hy₂ hl₁ hl₂ modifier reflected bin j
  obtain ⟨labels,column,hinj,hlive,alloc,hf,hfirst⟩:=hzmain.2 hZ s R₀ hz₁ hz₂ hcaps0.1 hcaps0.2.1
    hcaps0.2.2.2.1 W ht ell amp reserve _ hzpool.nonempty hzpool.prime
    (fun P hP=>hzpool.avoids_bad P hP) (by
      intro P hP i I hI
      exact hzpool.avoids_canonical_slot rayM H (w i) (hwm i) P hP I hI)
    hel hzpool.norm_lower hzpool.norm_upper hzpool.card_source
    reflected bin (fun j _=>(hg0 j).2.1) (fun j _=>(hg0 j).2.2.2.1)
    (fun j _ B _=>hchildcap j B)
  let common:=fun l:labels=>columnIdeal reflected s modifier R₀ 1 Z Z ξ hZ0 bin (column l)
  let chars:=fun l:labels=>columnCharacter reflected s modifier R₀ 1 Z Z ξ hZ0 bin (column l)
  let label:=fun l:labels=>firstLabel s modifier R₀ 1 Z Z ξ hZ0 bin (column l)
  let radius:=fun l:labels=>literalFirstRadius reflected Z (volume s) Z ξ reserve (label l)
  let H0:=fun l:labels=>(source s modifier R₀ 1 Z Z ξ hZ0 bin (column l).1).H0
  let Hmain:=fun l:labels=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (label l)
  let Tsec:=fun l:labels=>firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (label l)
  let scalar:=fun l:labels=>balancedColumnScalar reflected s modifier R₀ 1 Z Z ξ 1
    (Real.logb Z (volume s)) hZ0 bin (fun q=>normPhase (coordinateBlock s modifier R₀ 1 W Z Z ξ q)) (column l)
  let P:=CenteredMomentPrimePool.primePool rayM H fixedBadPrimes (1/2) 1 (Z^amp)
  let amplitude:=fun l:labels=>‖scalar l‖^2*
    (((bands (H0 l)).card:ℝ)*((actualAllocations s.pools (common l)).card:ℝ)^2/(P.card:ℝ)*
      ((radius l+6*amp)/ell))*‖frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P‖^2
  have hseed:∀l:labels,Squarefree (column l).2.1.val:=fun l=>
    live_projector_squarefree s modifier R₀ 1 Z Z ξ hZ0 bin (fun _=>logAnnulus) (column l) (hlive l)
  have hHmain:∀l:labels,0<Hmain l:=fun l=>first_main_radius_pos reflected Z (volume s) Z ξ
    (3*amp) reserve hZ0 (label l)
  have hcommon:∀l:labels,common l≠0:=by
    intro l
    have h:=label_supported s modifier R₀ 1 Z Z ξ hZ0 bin (column l)
    cases reflected
    · exact h.1.1
    · exact h.2.1.1
  have ha0:∀l:labels,0≤amplitude l:=by
    intro l
    have hrad:0≤radius l+6*amp:=(hg0 (column l)).2.1
    dsimp only [amplitude]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
      (div_nonneg hrad hel.le))) (sq_nonneg _)
  have hwidth:b-(n.allowance:ℝ)-width≤∑i,w i:=by linarith
  have herr:frequencyLoss Z 32 ξ+reserve+2*e+e+e≤2*(n.allowance:ℝ):=by
    have hfreq0:=hzfreq.2.2.le.trans hxstep
    linarith only [heRem,hfreq0,hrstep]
  have hrema:=hzrem.2 hZ0 η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    K n low b width hg he.le hL0 hlow hw hadm hwidth hwhi (le_refl _)
    modifier R₀ W ξ reserve e 1 hZ0 herr P mesh 12 2 depth hzpool
  have hrema':=hrema reflected bin labels column hinj hlive (fun l=>(hg0 (column l)).2.2.2.2.2.1)
    (fun l=>(hg0 (column l)).2.1) (fun l=>(hg0 (column l)).2.2.1) alloc chars (fun _=>ht) hf
  let Λ:=fun l:labels=>initialCann N/((common l).absNorm:ℝ)
  have hΛ:∀l,0<Λ l:=fun l=>div_pos (initialCann_pos N) (by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hcommon l)))
  have hVchild:∀l:labels,volume (child s (common l) R₀ (alloc l) (chars l) ht)≤Z^(3:ℝ):=by
    intro l
    have h:=ForcedCost.child_volume_ordinary_bound s (common l) R₀ (alloc l) (chars l) ht hscales
    have h' :volume s/ForcedCost.ordinaryNorm (alloc l).val≤volume s:=
      div_le_self (CenteredMomentAmplificationChildInput.volume_pos s).le (ForcedCost.ordinaryNorm_ge_one s (common l) (alloc l))
    exact (h.trans h').trans (hcaps0.2.2.2.1.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : (1:ℝ)≤3)))
  have hTsec:∀l:labels,Tsec l≤Z^(3:ℝ):=by
    intro l
    have h:=modified_main_frequency_cap reflected s modifier R₀ 1 Z Z ξ (3*amp) reserve N
      hZ0 hZ hx.le hx1 (by positivity) hr0 le_rfl hNpow bin (column l)
    have hp:0≤Tsec l:=by change 0≤_ ^ 2/Hmain l;exact div_nonneg (sq_nonneg _) (hHmain l).le
    exact (show Tsec l≤frequencyRadius (Tsec l) Z ξ from by
      unfold frequencyRadius
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hZ.le (by positivity :0≤ξ/2)) hp).trans h
  have hnom:∀l:labels,(volume (child s (common l) R₀ (alloc l) (chars l) ht))^2/Hmain l≤Tsec l:=by
    intro l
    exact actual_first_fourier_child s modifier R₀ 1 Z ξ amp reserve hZ N (le_refl _)
      (by norm_num [s,initialInput]) reflected bin (column l) (alloc l) (chars l) ht (hf l)
  let χ₀:labels→RayCharacter:=fun _=>1
  let f:=mainAllocatedFamily s ballProfile (p.profile 0) (p.profile 1) Z R₀ common
    (fun l=>(column l).2.1.val) alloc chars (fun _=>ht) P hseed hz₁ hz₂ Hmain Tsec
    (fun _=>volume s) amplitude ξ hHmain χ₀ (fixedBadMask*idealGenerator R₀)
  let zeroTerm:=fun l:labels=>C₀*(4*plainControl (f.input l) (p.profile 0) (p.profile 1))^2*
    S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Hmain l*(Λ l)^(1+e)*(volume s)^e/(column l).2.1.val.absNorm
  let tailTerm:=fun l:labels=>C₁*(2*plainControl (f.input l) (p.profile 0) (p.profile 1))^2*
    S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Hmain l*
      (volume (f.input l)/volume s)*Z^(-1:ℝ)/(column l).2.1.val.absNorm
  have hs:=hzsecond.2 (le_refl _) s R₀ common (fun l=>(column l).2.1.val) alloc chars ht P
    hzpool.nonempty hzpool.prime ell 2 hel hzpool.norm_lower hzpool.card_source
    (fun l=>hchildcap (column l) (alloc l)) (p.profile 0) (p.profile 1) rfl rfl hz₁ hz₂
    (p.support 0) (p.support 1) (fun _=>by norm_num [s,initialInput]) hseed
    (fun l=>(hg0 (column l)).2.2.2.2.2.1) Λ Hmain Tsec (volume s) hΛ (CenteredMomentAmplificationChildInput.volume_pos s) hrema'.1
    hHmain hVchild hTsec hnom amplitude ha0 χ₀ (fixedBadMask*idealGenerator R₀) (internalQ Q η₀)
  let G:=geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin
  have hr : regularJointNorm f (internalQ Q η₀)≤Cr*(p.control Sr)^2*G*(1+|ht|+height)^dr*Z^(-σ) :=hzreg.2 hZ θ w v t ht height hwp hwm hh hv hheight p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi
    hy₂ hl₁ hl₂ reflected bin column hinj hlive alloc hf χ₀
  have hcomp : ‖∑q:f.Carrier,f.phase (internalQ Q η₀) q*(f.block (internalQ Q η₀) q).value ballProfile‖≤Ce*(p.control Se)^2*(1+|ht|)^de*G*Z^(-amp) :=hzex.2 hZ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hwp hwm hadm hwidth hwhi
    hy₂ hl₁ hl₂ rfl reflected bin column hinj hlive (fun l=>(hg0 (column l)).2.2.2.2.2.1)
    alloc (fun _=>ht) H0 radius |ht| χ₀ (abs_nonneg _) (fun _=>(Real.norm_eq_abs ht).le)
    (fun l=>(hg0 (column l)).1) (fun l=>(hg0 (column l)).2.1) (fun l=>(hg0 (column l)).2.2.1)
  have hG:0≤G:=(geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hp0:=plain_profile_control p S hS
  have hpr:=profile_control_mono p hSrS
  have hpe:=profile_control_mono p hSeS
  have hzsum:(∑l,amplitude l*zeroTerm l)≤Cz'*(p.control S)^2*G*Z^(-amp-(n.allowance:ℝ)+2*e):=by
    have hid:(∑l,amplitude l*zeroTerm l)=(C₀*16*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
      ∑l,amplitude l*(plainControl (f.input l) (p.profile 0) (p.profile 1))^2*Hmain l*
        (Λ l)^(1+e)*(volume s)^e/(column l).2.1.val.absNorm:=by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro l _;dsimp only [zeroTerm];ring
    rw [hid]
    apply (mul_le_mul_of_nonneg_left hrema'.2.1 (by positivity)).trans
    have hp2:=pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp0 2
    convert mul_le_mul_of_nonneg_left hp2 (show 0≤C₀*16*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Cz*G*Z^(-amp-(n.allowance:ℝ)+2*e) by positivity) using 1 <;>
      dsimp only [Cz',G] <;> ring
  have htsum:(∑l,amplitude l*tailTerm l)≤Ct'*(p.control S)^2*G*Z^(-amp-(n.allowance:ℝ)-1+2*e):=by
    have hid:(∑l,amplitude l*tailTerm l)=(C₁*4*S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
      ∑l,amplitude l*(plainControl (f.input l) (p.profile 0) (p.profile 1))^2*Hmain l*
        (volume (f.input l)/volume s)*Z^(-1:ℝ)/(column l).2.1.val.absNorm:=by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro l _;dsimp only [tailTerm];ring
    rw [hid]
    apply (mul_le_mul_of_nonneg_left hrema'.2.2 (by positivity)).trans
    have hp2:=pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp0 2
    convert mul_le_mul_of_nonneg_left hp2 (show 0≤C₁*4*S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Ct*G*Z^(-amp-(n.allowance:ℝ)-1+2*e) by positivity) using 1 <;>
      dsimp only [Ct',G] <;> ring
  have hr':regularJointNorm f (internalQ Q η₀)≤Cr*(p.control S)^2*G*(1+|ht|+height)^dr*Z^(-σ):=by
    exact hr.trans (control_payment Cr _ _ G _ _ hCr.le (p.control_nonneg _) hpr hG (by positivity) (Real.rpow_nonneg hZ0.le _))
  have hc':‖∑q:f.Carrier,f.phase (internalQ Q η₀) q*(f.block (internalQ Q η₀) q).value ballProfile‖≤
      Ce*(p.control S)^2*G*(1+|ht|+height)^de*Z^(-amp):=by
    apply hcomp.trans
    have hp:(1+|ht|)^de≤(1+|ht|+height)^de:=pow_le_pow_left₀ (by positivity) (by linarith) _
    exact mixed_control_payment Ce _ _ G _ _ _ hCe.le (p.control_nonneg _) hpe hG
      (by positivity) hp (Real.rpow_nonneg hZ0.le _)
  have hbase:=hfirst.trans (mul_le_mul_of_nonneg_left hs (mul_nonneg hCsel.le (Real.rpow_nonneg hZ0.le _)))
  have htotal:=selected_four_payment Z e amp (n.allowance:ℝ) σ Csel Cz' Cr Ce Ct' (p.control S) G
    (1+|ht|+height) _ _ _ _ _ dr de hZ.le he0.le heAmp heσ he.le hCsel.le hCz' hCr.le hCe.le hCt' hG
    (by linarith [abs_nonneg ht]) hbase hzsum hr' hc' htsum
  apply htotal.trans
  gcongr
  exact le_max_right _ _

end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.balanced_of_regular
