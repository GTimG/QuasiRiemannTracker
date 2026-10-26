/- Repeated marks: fork of Collet's generic return module PhysicalDirect.OldActive (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Actual old-band physical reconstruction on new geometry, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.arvi_repeated_marks_20261024.ReturnD.Schedule
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.OriginalFourth
import Submissions.arvi_repeated_marks_20261024.ReturnD.PhysicalDirect.Active
import Submissions.arvi_repeated_marks_20261024.ReturnD.PhysicalDirect.OldGeometry
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Mesh
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.OldFourth
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic OAI OAI.SevenEighths
open QRH.RepeatedMarks.Return.GenericArithmetic
open Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle25.Weighted.Numerator.PhysicalMoment
open QRH.Record12518109Count
open QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentFiniteProfileExceptional
open QRH.RepeatedMarks.Return.GenericArithmetic QRH.Record12518109Count
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
  have hp:0< d:=(show (0:ℝ)<d0 by norm_num [d0]).trans_le hd
  have hy:y/d≤99:=by
    apply (div_le_iff₀ hp).mpr
    have hdmin : (1/200:ℝ)≤d := hd
    linarith [Geometry.BoundsR.ly_coarse.2]
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
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,d0 ≤ d → d ≤ dm →
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
  · have hn:∀i:rows,¬active i:=fun i hi=>hex ⟨i,hi⟩
    change (∑i:rows,‖if active i then _ else 0‖^4*_)≤_
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
    have hp:=(show (0:ℝ)<d0 by norm_num [d0]).trans_le hd
    have hy:0< y:=by linarith [Geometry.BoundsR.ly_coarse.1,Geometry.BoundsR.ly_coarse.2]
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

end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.OldFourth
end

/- Adapted from Cycle25 actual physical coefficient-box restriction, Apache-2.0.
Cycle63 old band uses actual capped original/reflected lengths at new y. -/

