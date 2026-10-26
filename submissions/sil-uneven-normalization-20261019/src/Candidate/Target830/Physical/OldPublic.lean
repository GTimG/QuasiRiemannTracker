import Candidate.Cycle25.Numerator.Damping
import Candidate.Target830.Count.Feedback
import Candidate.Cycle25.Numerator.BoxGeometry
import Candidate.Cycle25.Energy.Physical.OriginalFourth
import Candidate.Target830.Physical.Active
import Candidate.Cycle25.Assembly.Mesh
import Candidate.Target830.Physical.Data

/- Original module: Candidate.Target830.Physical.OldGeometry. -/
section
/- Target830 genuine old-band physical reconstruction. Predecessor attribution retained. Apache-2.0. -/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace OAI.SevenEighths.Target830.Physical.OldFourth
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Count
open Cycle25.Numerator

def originalBaseCapacity (κ m : ℝ) : ℝ := (2*min m 1-1)/(6*κ)
def reflectedLength (m t : ℝ) : ℝ := max 0 (1-m+t)
lemma reflectedLength_nonneg (m t : ℝ) : 0≤ reflectedLength m t:=le_max_left _ _
lemma reflectedLength_le_of_support {m t e : ℝ} (he : 0≤ e) (ht : t≤ m+e) :
    reflectedLength m t≤1+e := by
  apply max_le <;> linarith

/-- Capacity in row-base units, including the original length cap at one. -/
def baseCapacity (κ d : ℝ) : ℝ := min 1 (2*y/d-1)/(6*κ)
def capOld (κ d t : ℝ) : ℝ := max 0 ((min 1 (2*y/d-1)-2*t)/(6*κ))
def coefficientBoxCount100 (xi : ℝ) : ℕ := ⌈100/xi⌉₊

lemma capped_plain_identity (m : ℝ) : min 1 (2*m-1)=2*min m 1-1 := by
  by_cases hm:m≤1
  · rw [min_eq_left hm,min_eq_right (by linarith : 2*m-1≤1)]
  · rw [min_eq_right (le_of_not_ge hm),min_eq_left (by linarith : 1≤2*m-1)]
    ring

lemma capOld_eq_selected {κ d t : ℝ} (hk : κ≠0) :
    capOld κ d t=selectedCapacity κ (originalBaseCapacity κ (y/d)) t := by
  unfold capOld selectedCapacity originalBaseCapacity
  rw [mul_div_assoc,capped_plain_identity]
  congr 1
  field_simp
  ring

lemma base_scaled {κ d : ℝ} (hd : 0< d) :
    d*baseCapacity κ d=OAI.SevenEighths.Target830.Count.oldCapacityAt κ d := by
  unfold baseCapacity OAI.SevenEighths.Target830.Count.oldCapacityAt
  rw [←mul_div_assoc,mul_min_of_nonneg _ _ hd.le]
  have he:d*(2*y/d-1)=2*y-d:=by
    field_simp [hd.ne']
  rw [mul_one,he]

lemma capOld_nonneg (κ d t : ℝ) : 0≤ capOld κ d t:=le_max_left _ _

lemma physical_y_range {d : ℝ} (hd : d0≤ d ∧ d≤ dMinus) : 1/2< y/d ∧ y/d≤99 := by
  have hp:0< d:=(show (0:ℝ)< d0 by norm_num [d0]).trans_le hd.1
  constructor
  · apply (lt_div_iff₀ hp).mpr
    norm_num [dMinus,y,h,ell,theta] at *
    linarith
  · apply (div_le_iff₀ hp).mpr
    norm_num [d0,y,h,ell,theta] at *
    linarith

lemma box100_extent {xi : ℝ} (hx : 0< xi) :
    100≤(coefficientBoxCount100 xi:ℝ)*xi := by
  have hh:=mul_le_mul_of_nonneg_right (Nat.le_ceil (100/xi)) hx.le
  simpa only [coefficientBoxCount100,div_mul_cancel₀ _ hx.ne'] using hh

/-- Genuine clipped reflected shortening, including original scales above U. -/
lemma reflected_capacity_or_empty {α : Type*} (T : Finset α) (width : T→ℝ)
    {κ d t slack : ℝ} (hk : 0< κ) (ht : 0≤ t) (hw : ∀i,0< width i)
    (hs : (∑i,width i)≤ capOld κ d (t+slack)) :
    2*(reflectedLength (y/d) t+slack)+6*κ*(∑i,width i)≤1 ∨ T=∅ := by
  let raw:=originalBaseCapacity κ (y/d)-(t+slack)/(3*κ)
  have hsel:(∑i,width i)≤ selectedCapacity κ (originalBaseCapacity κ (y/d)) (t+slack):=by
    simpa only [capOld_eq_selected hk.ne'] using hs
  by_cases hr:0≤ raw
  · left
    have he:selectedCapacity κ (originalBaseCapacity κ (y/d)) (t+slack)=raw:=max_eq_right hr
    rw [he] at hsel
    have hmul:=mul_le_mul_of_nonneg_left hsel (show 0≤6*κ by positivity)
    have hid:6*κ*raw=2*min (y/d) 1-1-2*(t+slack):=by
      dsimp [raw,originalBaseCapacity]
      field_simp
      ring
    rw [hid] at hmul
    by_cases hp:0≤1-y/d+t
    · rw [reflectedLength,max_eq_right hp]
      linarith [min_le_left (y/d) (1:ℝ)]
    · rw [reflectedLength,max_eq_left (le_of_not_ge hp)]
      linarith [min_le_right (y/d) (1:ℝ)]
  · right
    have he:selectedCapacity κ (originalBaseCapacity κ (y/d)) (t+slack)=0:=max_eq_left (le_of_not_ge hr)
    rw [he] at hsel
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hh:width ⟨i,hi⟩≤∑i,width i:=Finset.single_le_sum
      (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
    linarith [hw ⟨i,hi⟩]

/-- Strong physical coefficient damping pays the exact clipped capacity loss. -/
lemma capacity_damping {κ d t q delta : ℝ} (hk : 7/10≤ κ)
    (ht : 0≤ t) (hq : 0≤ q) (hqd : q≤ delta/2) :
    q*baseCapacity κ d/2+delta*t/4≤ delta*t/2+q*capOld κ d t/2 := by
  have hk0:0< κ:=by linarith
  have hd:0≤ delta:=by linarith
  have hc:baseCapacity κ d-capOld κ d t≤ t/(3*κ):=by
    have hm:=le_max_right 0 ((min 1 (2*y/d-1)-2*t)/(6*κ))
    change (min 1 (2*y/d-1)/(6*κ))-max 0 ((min 1 (2*y/d-1)-2*t)/(6*κ))≤ t/(3*κ)
    have he:(min 1 (2*y/d-1)-2*t)/(6*κ)=min 1 (2*y/d-1)/(6*κ)-t/(3*κ):=by field_simp;ring
    rw [he] at hm ⊢
    linarith
  have hpay:t/(3*κ)≤(2/3)*t:=by
    apply (div_le_iff₀ (show 0<3*κ by positivity)).mpr
    nlinarith
  have hmul:=mul_le_mul_of_nonneg_left (hc.trans hpay) hq
  have hqd':=mul_le_mul_of_nonneg_right hqd ht
  nlinarith

end OAI.SevenEighths.Target830.Physical.OldFourth

namespace OAI.SevenEighths.Target830.Physical.OldFourth
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Count

lemma capOld_le_supply {κ d t : ℝ} (hk : 7/10≤ κ)
    (hd : d0≤ d ∧ d≤ dMinus) (ht : 0≤ t) : capOld κ d t≤ ell/d := by
  have hdp:0< d:=(show (0:ℝ)< d0 by norm_num [d0]).trans_le hd.1
  have hkp:0< κ:=by linarith
  have hy:=physical_y_range hd
  have hbase:0≤ baseCapacity κ d:=by
    unfold baseCapacity
    apply div_nonneg
    · rw [mul_div_assoc]
      apply le_min <;> linarith
    · positivity
  have hcap:capOld κ d t≤ baseCapacity κ d:=by
    unfold capOld baseCapacity
    apply max_le hbase
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hmin:min d (2*y-d)≤ y:=by
    by_cases h:d≤ y
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  have htotal:OAI.SevenEighths.Target830.Count.oldCapacityAt κ d≤ ell:=by
    unfold OAI.SevenEighths.Target830.Count.oldCapacityAt
    apply (div_le_iff₀ (show 0<6*κ by positivity)).mpr
    have hyell:y≤ ell*(6*κ):=by
      norm_num [ell,y,h,theta]
      linarith
    exact hmin.trans hyell
  have hscaled:=base_scaled (κ:=κ) hdp
  apply hcap.trans
  apply (le_div_iff₀ hdp).mpr
  rw [mul_comm, hscaled]
  exact htotal

end OAI.SevenEighths.Target830.Physical.OldFourth

#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.reflectedLength_nonneg
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.reflectedLength_le_of_support
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.capped_plain_identity
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.capOld_eq_selected
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.base_scaled
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.capOld_nonneg
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.physical_y_range
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.box100_extent
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.reflected_capacity_or_empty
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.capacity_damping
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.capOld_le_supply
end

/- Original module: Candidate.Target830.Physical.OldActive. -/
section
/- Target830 genuine old-band physical reconstruction. Predecessor attribution retained. Apache-2.0. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Target830.Physical.OldFourth
open Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle25.Weighted.Numerator.PhysicalMoment
open OAI.SevenEighths.Target830.Physical
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentFiniteProfileExceptional
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Count
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma eventually_old_cutoff (b:ℝ) (hb:0≤ b) :
    ∀ᶠU:ℝ in atTop,1< U ∧ ∀d:ℝ,d0≤ d → b*U^(y/d)≤ U^(100:ℝ) := by
  have he:∀ᶠU:ℝ in atTop,b≤ U^(1:ℝ):=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hp:0< d:=(show (0:ℝ)< d0 by norm_num [d0]).trans_le hd
  have hy:y/d≤99:=by
    apply (div_le_iff₀ hp).mpr
    norm_num [y,d0,h,ell,theta] at *
    linarith
  calc
    _ ≤ U^(1:ℝ)*U^(99:ℝ):=mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U^(100:ℝ):=by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num

/-- The concrete masked fourth-moment premise needed by the actual packet/bin
bound. All constants precede every rowwise coefficient choice. -/
theorem old_active_box_fourth {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (kap:ℝ) (hkaplo:7/10≤ kap) (hkaphi:kap≤3/4)
    (hkapbeta:2*HeckeZeroSupremum.beta-1≤ kap) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hb:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,d0 ≤ d → d ≤ dMinus →
      ∀j∈Finset.range (coefficientBoxCount100 boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ capOld kap d ((j:ℝ)*boxWidth+boxWidth+annulusSlack) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(y/d)
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount100 boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,C,hC,hmoment⟩ := certified_original_numerator_fourth F kap hkaplo hkaphi hbeta hkapbeta
    G loss annulusSlack 1 b 1 hloss hann hb (by norm_num)
  have hbpow:∀ᶠU:ℝ in atTop,b≤ U^boxWidth:=
    (tendsto_rpow_atTop hbox).eventually (eventually_ge_atTop _)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_old_cutoff b hb.le,hbpow] with U hmom hcutoff hbpow
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN d hd hdmax j hj T width z height hw hwmax hz hh him hselected hQ
  dsimp only
  let Y := U^(y/d)
  let Ccond:ℝ := fixedConductorConstant F.S
  let Lc (i:rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i:rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount100 boxWidth) (max 1 (Lc i*N i))=j
  let m := reflectedLength (y/d) ((j:ℝ)*boxWidth+boxWidth)
  have hY : 0 < Y := Real.rpow_pos_of_pos hUp _
  have hCcond : 0 < Ccond := by
    dsimp [Ccond]
    exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  have hNu (i:rows) : 0 < rowNorm i.val :=
    (Real.rpow_pos_of_pos hUp _).trans_le (hrows i.val i.property).1
  have hL (i:rows) : Lc i ≤ 1 := by
    apply (div_le_one (mul_pos hCcond (hNu i))).mpr
    exact (data i).combined_le_row
  have hcut : b*Y ≤ U^((coefficientBoxCount100 boxWidth:ℝ)*boxWidth) := by
    apply (hcutoff.2 d hd).trans
    exact Real.rpow_le_rpow_of_exponent_le hU.le (box100_extent hbox)
  have hcombinedActive (i:rows) (hi:active i) :
      (data i).combinedConductor ≤ Ccond*U^m*(Y/N i) := by
    have hupper := active_dilation_upper U boxWidth (Lc i) (N i) b Y
      (coefficientBoxCount100 boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
    have hspec := (dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount100 boxWidth)
      (max 1 (Lc i*N i)) (le_max_left _ _) hupper).2
    rw [hi.2] at hspec
    have hb' : max 1 ((data i).combinedConductor*N i/(Ccond*rowNorm i.val)) ≤
        U^((j:ℝ)*boxWidth+boxWidth) := by
      have hprod : Lc i*N i = (data i).combinedConductor*N i/(Ccond*rowNorm i.val) := by
        dsimp only [Lc]
        ring
      have hexp : ((j:ℝ)+1)*boxWidth = (j:ℝ)*boxWidth+boxWidth := by ring
      rw [hprod,hexp] at hspec
      exact hspec
    have hc := combined_scale_of_dilation (data i).combinedConductor Ccond (rowNorm i.val)
      (N i) Y U (y/d) ((j:ℝ)*boxWidth+boxWidth)
      hCcond (hNu i) (hN i) hUp (hrows i.val i.property).2 rfl hb'
    have hraw:1-y/d+((j:ℝ)*boxWidth+boxWidth)≤ m:=by
      dsimp [m,reflectedLength]
      exact le_max_right (0:ℝ) _
    have hpow:=Real.rpow_le_rpow_of_exponent_le hU.le hraw
    exact hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hCcond.le) (div_pos hY (hN i)).le)
  let Nsafe (i:rows) := if active i then N i
    else fallbackCoefficientScale b Y Ccond (data i).combinedConductor U m
  have hsafe (i:rows) : 0 < Nsafe i ∧ Nsafe i ≤ b*Y ∧
      (data i).combinedConductor ≤ Ccond*U^m*(Y/Nsafe i) := by
    dsimp only [Nsafe]
    split_ifs with hi
    · exact ⟨hN i,hi.1,hcombinedActive i hi⟩
    · exact fallback_scale_admissible b Y Ccond (data i).combinedConductor U m
        hb hY hCcond (data i).combined_pos hUp
  by_cases hex:∃i:rows,active i
  swap
  · have hn:∀i:rows,¬active i:=fun i hi=> hex ⟨i,hi⟩
    change (∑i:rows,‖if active i then _ else 0‖^4*_)≤ _
    simp only [hn,ite_false,norm_zero,zero_pow (by norm_num:4≠0),zero_mul,Finset.sum_const_zero]
    positivity
  obtain ⟨i,hi⟩:=hex
  have hupper:=active_dilation_upper U boxWidth (Lc i) (N i) b Y
    (coefficientBoxCount100 boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
  have hlo:U^((j:ℝ)*boxWidth)≤ max 1 (Lc i*N i):=by
    have hh:=(dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount100 boxWidth)
      (max 1 (Lc i*N i)) (le_max_left _ _) hupper).1
    rw [hi.2] at hh
    exact hh
  have hys:0< y/d:=by
    have hp:=(show (0:ℝ)< d0 by norm_num [d0]).trans_le hd
    have hy:0< y:=by norm_num [y,h,ell,theta]
    exact div_pos hy hp
  have hmax:max 1 (Lc i*N i)≤ U^(y/d+boxWidth):=by
    apply max_le
    · exact Real.one_le_rpow hU.le (by positivity)
    · calc
        _ ≤ N i:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hL i) (hN i).le
        _ ≤ b*Y:=hi.1
        _ ≤ U^boxWidth*U^(y/d):=mul_le_mul_of_nonneg_right hbpow (by positivity)
        _ = _:=by rw [←Real.rpow_add hUp];congr 1;ring
  have hv:(j:ℝ)*boxWidth≤ y/d+boxWidth:=(Real.rpow_le_rpow_left_iff hU).mp (hlo.trans hmax)
  have hm:0≤ m:=reflectedLength_nonneg _ _
  have hmhi:m≤1+2*boxWidth:=reflectedLength_le_of_support (by positivity) (by linarith)
  have hmmax:m+annulusSlack≤2:=by linarith
  have hcapacity := reflected_capacity_or_empty T width (show 0< kap by linarith)
    (show 0≤(j:ℝ)*boxWidth+boxWidth by positivity) hw hselected
  have hQ' (i:rows) : ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
      (U^(width s)) (z s)‖ ≤ (1:ℝ)*U^(1:ℝ) := by simpa using hQ i
  have hbound := hmom.2 rows hrows data Nsafe Y m hY (fun i=>⟨(hsafe i).1,(hsafe i).2.1⟩)
    hm hmmax (fun i=>(hsafe i).2.2) T width z height (fun i=>(hw i).le) hwmax hz hh him
    (by simpa only [m] using hcapacity) hQ'
  apply (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>?_)).trans hbound
  change ‖if active i then _ else 0‖^4*_ ≤ _
  by_cases hi:active i
  · simp only [hi,ite_true,Nsafe,Y]
    exact le_rfl
  · simp only [hi,ite_false,norm_zero,zero_pow (by norm_num:4≠0),zero_mul]
    positivity

end OAI.SevenEighths.Target830.Physical.OldFourth
end

/- Adapted from Cycle25 actual physical coefficient-box restriction, Apache-2.0.
Cycle63 old band uses actual capped original/reflected lengths at new y. -/

#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.eventually_old_cutoff
#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.old_active_box_fourth
end

/- Original module: Candidate.Target830.Physical.OldPublic. -/
section
/- Target830 genuine old-band physical reconstruction. Predecessor attribution retained. Apache-2.0. -/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Target830.Physical.OldFourth
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open OAI.SevenEighths.Target830.Physical OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Count
open ProbeRowRadicalConductor
open Cycle25.Numerator Cycle25.Weighted.Numerator

/- Geometry-independent original/reflected physical reconstruction APIs. -/
export Cycle25.Weighted.Numerator.PhysicalMoment (certified_original_numerator_fourth)
export OAI.SevenEighths.Cycle25WeightedNumeratorPhysical
  (certified_actual_retained_fourth certified_retained_fixed_profile)

/-- Actual old-band source moment on new lengths and geometry; no affine premise. -/
theorem baseline_old_active_box_fourth (D : BaselineData) (F : BaselineSourceData D)
    (hb : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤ D.momentKappa)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hbcut:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,d0 ≤ d → d ≤ dMinus →
      ∀j∈Finset.range (coefficientBoxCount100 boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ capOld D.momentKappa d ((j:ℝ)*boxWidth+boxWidth+annulusSlack) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(y/d)
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount100 boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  exact old_active_box_fourth F D.momentKappa D.momentKappa_lo D.momentKappa_hi hκβ hb
    G loss boxWidth annulusSlack b hloss hbox hann hbcut hsmall

end OAI.SevenEighths.Target830.Physical.OldFourth

#print axioms OAI.SevenEighths.Target830.Physical.OldFourth.baseline_old_active_box_fourth
end
