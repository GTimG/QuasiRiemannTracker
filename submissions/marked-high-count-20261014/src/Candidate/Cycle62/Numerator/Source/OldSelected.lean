/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Numerator.Source.Parameters
import Candidate.Cycle62.Numerator.Source.OldPacket

/-! Actual source packet estimates with the original physical fourth moment
fully discharged. Remaining bin premises are finite count and prime-amplitude
inequalities, supplied by the certified source amplitude partition. -/
noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators Classical ContDiff
open Filter
namespace Cycle62.Numerator.Source
open Cycle25.Weighted Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle62.Arithmetic Cycle62.Numerator.OldFourth
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor Cycle25DetectorRowCount Cycle62DetectorCount
local notation "O" => HeckeFamily.O

lemma old_source_cutoff_le_base (b : ℝ) (hb : 0<b) :
    ∀ᶠ U:ℝ in atTop,1<U ∧ ∀d:ℝ,d0≤d → b*U^(y/d)≤U^(100:ℝ) := by
  have hev := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1)).eventually (eventually_ge_atTop b)
  filter_upwards [hev,eventually_gt_atTop (1:ℝ)] with U hbU hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdpos := d0_pos.trans_le hd
  have hym : y/d≤99 := by
    apply (div_le_iff₀ hdpos).mpr
    norm_num [d0,y] at *
    linarith
  calc
    _ ≤ U^1*U^(y/d) := mul_le_mul_of_nonneg_right hbU (Real.rpow_nonneg (by linarith) _)
    _ = U^(1+y/d) := (Real.rpow_add (by linarith : 0<U) (1:ℝ) (y/d)).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)

theorem old_source_packet_selected_bin (D : BaselineData)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200) (J : Finset (Fin D.N)) :
    ∃degree : ℕ,∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → d0≤d → d≤dMinus → U=Z^d →
      ∀(η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ)≤a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤height → |z.im|≤height →
      ∀(rows : Finset FreeRow),
      (∀u∈rows,U^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀(selected : ℕ→Finset (Fin D.N)) (P : rows→ℂ) (q R selLoss Ccount : ℝ),
      0≤q → q≤(2*a-1)/2 → 1≤Ccount → (rows.card:ℝ)≤Ccount*U^R →
      (∀i,‖P i‖≤U^(q*(Cycle62.Arithmetic.ell/d))) →
      (∀j∈Finset.range (coefficientBoxCount100 D.t+1),
        (∑s∈selected j,D.length s/d)≤ capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t)) →
      (∀j∈Finset.range (coefficientBoxCount100 D.t+1),∀i:rows,
        U^(q*capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t)-selLoss)≤
          ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖) →
      (∀j∈Finset.range (coefficientBoxCount100 D.t+1),∀i:rows,
        ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖≤U) →
      (∑i:rows,‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Cycle62.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
            (3*R+1+D.t+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
  obtain ⟨Cm,hCm,hpacket⟩ := old_actual_label_packet_bin_bound (ι:=J) D.t 1 2 1 D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*D.t+D.t≤1/2 := by have := D.t_small;linarith
  obtain ⟨degree,Cr,hCr,hmoment⟩ := baseline_old_active_box_fourth D F hbeta hkbeta F.W D.t D.t D.t 2
    D.t_pos D.t_pos D.t_pos (by norm_num) hsmall
  let Cr' : ℝ := max 1 Cr
  have hCr' : 1≤Cr' := le_max_left _ _
  let C : ℝ := ((coefficientBoxCount100 D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C];have := zero_lt_one.trans_le hCr';positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,old_source_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  dsimp only [BaselineData.toMomentData] at hmom
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase selected P q R selLoss Ccount hq hqtop hCc hcard hfull hcap hselected hcrude
  have hd0 : 0 < d := d0_pos.trans_le hd
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hmom.1
  have hscale (s : Fin D.N) : U^(D.length s/d)=Z^(D.length s) := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  let data (i : rows) : PhysicalReflectionData F.S F.exclusions.prime i.val :=
    Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime i.val (hrow i.val i.property))
  let Cu (i : rows) := (data i).combinedConductor
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0 < Ccond := by dsimp only [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  let Ts (s : J) := sourcePrimePool F Z s.val
  let hTs := fun s:J=>source_prime_pool_outside F Z s.val
  let Q (j : ℕ) (i : rows) := ∏s∈selected j,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z
  have hQprod (j : ℕ) (i : rows) :
      (∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(D.length s.val/d)) z) = Q j i := by
    calc
      _ = ∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (Z^(D.length s.val)) z := by
        apply Finset.prod_congr rfl
        intro s hs
        rw [hscale s.val]
      _ = _ := by
        exact Finset.prod_coe_sort (selected j)
          (fun s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z)
  have hwpos (s : Fin D.N) : 0 < D.length s/d := div_pos (D.slots_pos s) hd0
  have hwmax (s : Fin D.N) : D.length s/d≤Cycle25.sourceMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have ht := Cycle25.sourceMesh_pos D.t_pos
    have hs := hfine s
    have hdmin : (1/200:ℝ)≤d := hd
    nlinarith
  have hYp (s : J) : 1≤Z^(D.length s.val) := Real.one_le_rpow hZ.le (D.slots_pos s.val).le
  have hY : 0<U^(y/d) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(y/d)≤U^((coefficientBoxCount100 D.t:ℝ)*D.t) := by
    apply (hcutU.2 d hd).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hmom.1.le (box100_extent D.t_pos)
  obtain ⟨hrho,hrho1,hline,hleft,hmargin⟩ := source_packet_lines D a ha hatop
  have hmomentInput (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount100 D.t+1))
      (e : ∀i:rows,LabelPacketIndex F.S i.val Ts) :
      (∑i:rows,‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(y/d) ∧
        dilationBox U D.t (coefficientBoxCount100 D.t)
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
          (U^(y/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖Q j i‖^2) ≤
      (Cr'*(1+height)^degree)*U^(1+D.t+D.t) := by
    have hh := hmom.2 rows hrows data (fun i=>(labelPacketScale F.S i.val Ts (e i):ℝ))
      (fun i=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le F.S i.val Ts (e i)))
      d hd hdmax j hj (selected j) (fun s=>D.length s.val/d) (fun _=>z) height
      (fun s=>hwpos s.val) (fun s=>hwmax s.val) (fun _=>hz) hheight (fun _=>hzim)
      ((Finset.sum_coe_sort (selected j) (fun s=>D.length s/d)).le.trans (hcap j hj))
      (by
        intro i
        change ‖(∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(D.length s.val/d)) z)‖≤U
        rw [hQprod]
        exact hcrude j hj i)
    have hh' : _ ≤ (Cr'*(1+height)^degree)*U^(1+D.t+D.t) := hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
    
    convert hh' using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun qq : ℂ => ‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(y/d) ∧
      dilationBox U D.t (coefficientBoxCount100 D.t)
        (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
      then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
        (U^(y/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖qq‖^2) (hQprod j i).symm

  have hCM : 1≤Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket F.S F.exclusions (4*D.e) F.first η Ts hTs hdis
    (fun s Q hQ=>hη s.val Q hQ) Pbase (fun _=>F.W) (fun s=>Z^(D.length s.val)) hYp
    (fun _=>F.complex_support) (fun _ y=>source_complex_profile_norm D F y) x z a D.e ha
    (by linarith) D.e_pos D.e_small.le hx hz rows Subtype.val F.W 1 2 (U^(y/d))
    (by norm_num) F.complex_support (F.W.smooth ⊤) hY D.momentKappa d U D.t D.t (coefficientBoxCount100 D.t) Cu Ccond Q P
    R q (Cycle62.Arithmetic.ell/d) (2*a-1) selLoss (D.t+D.t) Ccount
    (Cr'*(1+height)^degree) D.momentKappa_lo ⟨hd,hdmax⟩ hmom.1.le D.t_pos.le D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i=>(data i).combined_pos.le)
    (fun i=>(data i).combined_le_radical) (fun i=>(hrows i.val i.property).2)
    (fun i=>hrow i.val i.property) hcut (by simpa using hcard) hselected hfull (by simpa only [add_assoc] using hmomentInput)
  apply hb.trans_eq
  dsimp only [C]
  have hp : U^(D.t+q*(Cycle62.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
      (3*R+1+D.t+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) =
      U^D.t*U^(q*(Cycle62.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
      (3*R+1+D.t+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hp]
  ring

end Cycle62.Numerator.Source

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/
