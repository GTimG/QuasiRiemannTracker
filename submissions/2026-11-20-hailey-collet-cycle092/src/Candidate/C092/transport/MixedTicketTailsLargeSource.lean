/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original error-label packet with the actual Q source fourth discharged.
Adapted from Collet/Gao SelectedBin; inherited OpenAI/Levy source credits remain. -/
import Candidate.C092.transport.PacketJoinActive
import Candidate.C092.transport.MixedTicketTailsLargeLabel
import Candidate.C092.transport.ActualGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Return.GenericData
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.PhysicalFront
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Cycle25.Weighted.Numerator Cycle25.Numerator
open QRH.Cycle092.PacketJoin
namespace QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
local notation "O" => HeckeFamily.O

private theorem q_source_packet_lines (D : BaselineData) (a : ℝ)
    (ha : (51/100:ℝ)≤a) (hatop : a≤7/8) :
    0≤(2*a-1)/2 ∧ (2*a-1)/2≤1 ∧
    1-a-6*D.e≤1/2-(2*a-1)/2 ∧ -(1/100:ℝ)≤1/2-(2*a-1)/2 ∧
    1+4*D.e≤(a+16*D.e)+(1/2-(2*a-1)/2) := by
  have he := D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

private theorem q_source_complex_profile_norm (D : BaselineData) (F : BaselineSourceData D) (r : ℝ) :
    ‖F.W r‖≤1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded r).1]
  exact (F.bounded r).2

private theorem q_source_cutoff_le_base (b : ℝ) (hb : 0≤b) :
    ∀ᶠ U : ℝ in atTop, 1<U ∧ ∀d : ℝ,(1/2:ℝ)≤d → b*U^(Geometry.y/d)≤U := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).eventually
    (eventually_ge_atTop b),eventually_gt_atTop (1:ℝ)] with U hbU hU
  refine ⟨hU,?_⟩
  intro d hd
  have hd0 : 0<d := by linarith
  have hy : Geometry.y/d≤19/20 := (div_le_iff₀ hd0).mpr (by
    linarith [ActualGeometry.WidenedCoreBounds.ly_coarse.2])
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul hbU
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (by positivity) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)]; norm_num

/-- Genuine physical label packet at the Q capacity, with the original countable
coefficient tuples and slot scales. The complete original fourth moment is
proved here. Only finite count and prime-amplitude inputs remain. -/
theorem q_large_label_packet_selected_bin
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (affineError : ℝ) (haff : 0<affineError) :
    ∃ mesh : ℝ,0 < mesh ∧ ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀j,D.length j≤ mesh/200) →
    (∀j,D.length j≤Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
    2*HeckeZeroSupremum.beta-1≤D.momentKappa →
    ∀ J : Finset (Fin D.N),
    ∃degree : ℕ,∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → (1/2:ℝ)≤ d → d≤ 7/8 → U=Z^d →
      ∀(η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ)≤ a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀(rows : Finset FreeRow),
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀ (data : ∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val) (vcut : ℝ),
      ∀(selected : ℕ→Finset (Fin D.N)) (P : rows→ℂ) (q R selLoss Ccount : ℝ),
      0≤ q → q≤(2*a-1)/2 → 1≤ Ccount → (rows.card:ℝ)≤ Ccount*U^R →
      (∀i,‖P i‖≤ U^(q*(Geometry.ell/d))) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),
        (∑s∈selected j,D.length s/d)≤ Physical.Selection.scheduledCapacity Geometry.y Cycle090.sourceCost d (2*((j:ℝ)*D.t+D.t+D.t))) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        U^(q*Physical.Selection.scheduledCapacity Geometry.y Cycle090.sourceCost d (2*((j:ℝ)*D.t+D.t+D.t))-selLoss)≤
          ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖) →
      (∀j∈Finset.range (coefficientBoxCount D.t+1),∀i:rows,
        ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖≤ U) →
      (∑i:rows,‖largeLabelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(Geometry.y/d)) (data i).combinedConductor (fixedConductorConstant F.S) U vcut*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(Geometry.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Geometry.ell/d)-q*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
            (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(2*D.t+D.t)/4-(2*a-1)*vcut/4) := by
  obtain ⟨mesh,hmesh,hactive⟩ := q_active_box_fourth hbeta affineError haff
  refine ⟨mesh,hmesh,?_⟩
  intro D F hfineAffine hfine hkbeta J
  obtain ⟨Cm,hCm,hpacket⟩ := label_packet_large_bound (ι:=J) D.t 1 2 1 D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*D.t+D.t≤1/2 := by have := D.t_small;linarith
  obtain ⟨degree,Cr,hCr,hmoment⟩ := hactive D.toMomentData F D.momentKappa D.momentKappa_lo D.momentKappa_hi hkbeta F.W D.t D.t D.t 2
    D.t_pos D.t_pos D.t_pos (by norm_num) hsmall
  let Cr' : ℝ := max 1 Cr
  have hCr' : 1≤ Cr' := le_max_left _ _
  let C : ℝ := ((coefficientBoxCount D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C];have := zero_lt_one.trans_le hCr';positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,q_source_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  dsimp only [QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData] at hmom
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase data vcut selected P q R selLoss Ccount hq hqtop hCc hcard hfull hcap hselected hcrude
  have hd0 : 0 < d := by linarith
  have hdhalf : (1/2:ℝ)≤ d := hd
  have hyr : (1/2:ℝ)≤Geometry.y/d ∧ Geometry.y/d≤19/20 := by
    constructor
    · apply (le_div_iff₀ hd0).mpr
      linarith [ActualGeometry.WidenedCoreBounds.ly_coarse.1]
    · apply (div_le_iff₀ hd0).mpr
      linarith [ActualGeometry.WidenedCoreBounds.ly_coarse.2]
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hmom.1
  have hscale (s : Fin D.N) : U^(D.length s/d)=Z^(D.length s) := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
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
  have hwmax (s : Fin D.N) : D.length s/d≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4) := by
    apply (div_le_iff₀ hd0).mpr
    have ht := Cycle25.Energy.commonMesh_pos 2 0 1 (D.t/4) (by norm_num) (by norm_num) (by have := D.t_pos; positivity)
    have hs := hfine s
    nlinarith
  have hYp (s : J) : 1≤ Z^(D.length s.val) := Real.one_le_rpow hZ.le (D.slots_pos s.val).le
  have hY : 0< U^(Geometry.y/d) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(Geometry.y/d)≤ U^((coefficientBoxCount D.t:ℝ)*D.t) := by
    apply (hcutU.2 d hdhalf).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hmom.1.le (coefficientBoxCount_extent D.t D.t_pos).1
  obtain ⟨hrho,hrho1,hline,hleft,hmargin⟩ := q_source_packet_lines D a ha hatop
  have hmomentInput (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount D.t+1))
      (e : ∀i:rows,LabelPacketIndex F.S i.val Ts) :
      (∑i:rows,‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(Geometry.y/d) ∧
        dilationBox U D.t (coefficientBoxCount D.t)
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
          (U^(Geometry.y/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖Q j i‖^2) ≤
      (Cr'*(1+height)^degree)*U^(1+D.t+affineError+D.t) := by
    have hh := hmom.2 rows hrows data (fun i=>(labelPacketScale F.S i.val Ts (e i):ℝ))
      (fun i=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le F.S i.val Ts (e i)))
      Geometry.y d hyr.1 hyr.2 j hj (selected j) (fun s=>D.length s.val/d) (fun _=>z) height
      (fun s=>hwpos s.val) (fun s=>by
        apply (div_le_iff₀ hd0).mpr
        have hlen := hfineAffine s.val
        nlinarith) (fun s=>hwmax s.val) (fun _=>hz) hheight (fun _=>hzim)
      ((Finset.sum_coe_sort (selected j) (fun s=>D.length s/d)).le.trans (hcap j hj))
      (by
        intro i
        change ‖(∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(D.length s.val/d)) z)‖≤ U
        rw [hQprod]
        exact hcrude j hj i)
    have hh' : _ ≤ (Cr'*(1+height)^degree)*U^(1+D.t+affineError+D.t) := hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
    
    convert hh' using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun qq : ℂ => ‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(Geometry.y/d) ∧
      dilationBox U D.t (coefficientBoxCount D.t)
        (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
      then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
        (U^(Geometry.y/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖qq‖^2) (hQprod j i).symm

  have hCM : 1≤ Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket F.S F.exclusions (4*D.e) F.first η Ts hTs hdis
    (fun s Q hQ=>hη s.val Q hQ) Pbase (fun _=>F.W) (fun s=>Z^(D.length s.val)) hYp
    (fun _=>F.complex_support) (fun _ y=>q_source_complex_profile_norm D F y) x z a D.e ha
    (by linarith) D.e_pos D.e_small.le hx hz rows Subtype.val F.W 1 2 (U^(Geometry.y/d))
    (by norm_num) F.complex_support (F.W.smooth ⊤) hY Cycle090.sourceCost d U D.t D.t (coefficientBoxCount D.t) Cu Ccond vcut Q P
    R q (Geometry.ell/d) (2*a-1) selLoss (D.t+affineError+D.t) Ccount
    (Cr'*(1+height)^degree) Cycle090.allowances_pos.1.le hmom.1 D.t_pos.le D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i=>(data i).combined_pos.le)
    (fun i=>(data i).combined_le_radical) (fun i=>(hrows i.val i.property).2)
    (fun i=>hrow i.val i.property) hcut (by simpa using hcard) hselected hfull (by
      intro j hj e
      have hh := hmomentInput j hj e
      rw [show 1+D.t+affineError+D.t=1+(D.t+affineError+D.t) by ring] at hh
      apply le_trans (Finset.sum_le_sum (fun i _=>?_)) hh
      by_cases ht : U^vcut ≤ max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale F.S i.val Ts (e i):ℝ))
      · simp only [ht,if_pos]
        exact le_rfl
      · simp only [ht,if_neg]
        split_ifs <;> simp <;> positivity)
  apply hb.trans_eq
  dsimp only [C]
  have hp : U^(D.t+q*(Geometry.ell/d)-q*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
      (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(2*D.t+D.t)/4-(2*a-1)*vcut/4) =
      U^D.t*U^(q*(Geometry.ell/d)-q*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
      (3*R+1+D.t+affineError+D.t)/4+selLoss/2+(2*a-1)*(2*D.t+D.t)/4-(2*a-1)*vcut/4) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hp]
  ring


end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.q_large_label_packet_selected_bin
