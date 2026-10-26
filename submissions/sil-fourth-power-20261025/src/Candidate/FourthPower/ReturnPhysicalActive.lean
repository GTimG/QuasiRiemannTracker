/- Copyright (c) 2026 Sil. Apache-2.0.
Actual original numerator and active coefficient-bin fourth moment, adapted
from PR69 PhysicalDirect/{Original,Active}, retaining Gao/OpenAI/Hailey Collet
provenance. Primitive reflection split, discarded tails and dilation-box
estimates are reused. Only the full-source inlet and actual geometry change.
 No old Geometry.Bounds/PhysicalSchedule instance.
-/
import Candidate.FourthPower.ReturnPhysicalRetained
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.Imported.NumeratorReflectionData
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.Discarded
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.BoxGeometry
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Mesh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Candidate.FourthPower.ReturnPhysicalActive
open ReturnCertificate ReturnPhysicalInput ReturnPhysicalSchedule ReturnPhysicalRetained

open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open QRH.Record12518109Count
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator.PhysicalTail Cycle25.Weighted.Numerator CenteredMomentRetainedWeightedSource
local notation "O" => HeckeFamily.O

theorem full_original_numerator_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bΦ mesh affineError : ℝ) (hAffineError : 0< affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bΦ mesh affineError U di control Ci)
    (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ)
    (hloss : 0< loss) (hxi : 0< xi) (hb : 0< b) (hCslot : 0< Cslot) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(data : ∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : rows→ℝ)(Y m : ℝ),
      0< Y → (∀i,0< N i ∧ N i ≤ b*Y) → 0 ≤ m → m+xi ≤ 2 →
      (∀i,(data i).combinedConductor ≤ (fixedConductorConstant F.S:ℝ)*U^m*(Y/N i)) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 ≤ width i) →
      (∀i,width i≤ mesh) →
      (∀i,width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      ((∃d t:ℝ,ds≤ d ∧ d≤ dplus ∧
        0≤ t ∧ t≤ shiftCutoff ∧ m+xi=shiftedPlain d t ∧
        (∑i,width i)≤ shiftedWidth d t) ∨
        (2*(m+xi)+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ Cslot*U^q) →
      (∑i:rows,‖HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0‖^4*
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) := by
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0< Ccond := by dsimp [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  obtain ⟨degree,Cr,hCr,hret⟩ := full_retained_fixed_profile F κ hκlo hκhi hbeta hκbeta
    bΦ mesh affineError hAffineError hsΦ di control Ci hCi hinput G loss Ccond Ccond xi
    hloss hCcond hCcond hxi
  obtain ⟨Ct,hCt,htail⟩ := subtype_discarded_fourth_negligible (xi/2) 0 q b Ccond Cslot
    (by positivity) hb hCcond hCslot G
  refine ⟨degree,8*(Cr+Ct),by positivity,?_⟩
  filter_upwards [hret] with U hret
  have hU := hret.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N Y m hY hN hm hmmax hcombined T width z height hw hwmesh hwmax hz hheight hzim hcap hQ
  let τ (i:rows) := (data i).presentation
  let ψ (i:rows) := (data i).primitive
  let R (i:rows) := retainedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let tail (i:rows) := discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let Q (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let P (i:rows) := HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
  have hc (i:rows) : (data i).combinedConductor ≤ Ccond*U :=
    (data i).combined_le_row.trans (mul_le_mul_of_nonneg_left (hrows i.val i.property).2 hCcond.le)
  have hred (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U :=
    (data i).redundant_le_combined.trans (hc i)
  have hr := hret.2 rows hrows τ ψ (fun i=>Y/N i) m (fun i=>(data i).element_eq)
    (fun i=>div_pos hY (hN i).1) hm hmmax hred hcombined T width z height
    hw hwmesh hwmax hz hheight hzim hcap
  have ht := htail rows τ ψ N Q Y U hY hU.le hN (fun u hu=>(hrows u hu).2) hc hQ
  simp only [show (xi/2)/2=xi/4 by ring,neg_zero,Real.rpow_zero,mul_one] at ht
  have hsplit (i:rows) : P i=(data i).phase*(R i+tail i) :=
    (data i).split G (Y/N i) (U^(xi/4)) (div_pos hY (hN i).1)
  have hh := original_split_weighted_fourth Finset.univ P R tail (fun i=>(data i).phase) Q
    (fun _=>1) (Cr*(1+height)^degree*U^(1+D.t+affineError+loss)) Ct
    (fun _ _=>le_rfl) (fun i _=>(data i).phase_norm) (fun i _=>hsplit i)
    (by simpa only [Complex.ofReal_one,div_one] using hr) ht
  simp only [Complex.ofReal_one,div_one] at hh
  have hH : 1 ≤ (1+height)^degree := one_le_pow₀ (by linarith)
  have hpow : 1 ≤ U^(1+D.t+affineError+loss) := Real.one_le_rpow hU.le (by linarith [D.t_pos])
  have hcost : 1 ≤ (1+height)^degree*U^(1+D.t+affineError+loss) := one_le_mul_of_one_le_of_one_le hH hpow
  have hCt' := mul_le_mul_of_nonneg_left hcost hCt.le
  exact hh.trans (by nlinarith)


open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentFiniteProfileExceptional
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor

def fallbackCoefficientScale (b Y C Cu U m:ℝ) : ℝ := min (b*Y) (C*U^m*Y/Cu)

lemma fallback_scale_admissible (b Y C Cu U m:ℝ)
    (hb:0 < b) (hY:0 < Y) (hC:0 < C) (hCu:0 < Cu) (hU:0 < U) :
    0 < fallbackCoefficientScale b Y C Cu U m ∧
      fallbackCoefficientScale b Y C Cu U m ≤ b*Y ∧
      Cu ≤ C*U^m*(Y/fallbackCoefficientScale b Y C Cu U m) := by
  have hp : 0 < fallbackCoefficientScale b Y C Cu U m := by
    unfold fallbackCoefficientScale
    exact lt_min (mul_pos hb hY) (by positivity)
  refine ⟨hp,min_le_left _ _,?_⟩
  rw [←mul_div_assoc,le_div_iff₀ hp]
  have hh := (le_div_iff₀ hCu).mp (min_le_right (b*Y) (C*U^m*Y/Cu))
  simpa only [fallbackCoefficientScale,mul_comm Cu] using hh

/-- Actual new-geometry conductor interval; no older narrow ell guard. -/
private theorem actual_y_range {d : ℝ} (hd : ds ≤ d ∧ d ≤ dplus) :
    (1/2:ℝ) ≤ y/d ∧ y/d < 1 := by
  have hs : 0 < ds := by rw [joins_exact.1]; norm_num
  have hd0 : 0 < d := hs.trans_le hd.1
  constructor
  · apply (le_div_iff₀ hd0).2
    linarith [conductor_order.2.2.2.2]
  · apply (div_lt_one hd0).2
    exact conductor_order.2.1.trans_le hd.1

private theorem coefficient_box_geometry {d xi ann : ℝ}
    (hd : ds ≤ d ∧ d ≤ dplus) (hxi : 0 < xi) (_hann : 0 ≤ ann)
    (hsmall : 2*xi+ann ≤ 1/2) (j : ℕ)
    (hj : j ∈ Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ 1-y/d+(j:ℝ)*xi+xi ∧
      (1-y/d+(j:ℝ)*xi+xi)+ann ≤ 2 := by
  have hy := actual_y_range hd
  have hv := coefficient_box_index_range xi hxi j hj
  constructor <;> linarith

lemma eventually_new_cutoff_le_base (b:ℝ) (hb:0≤ b) :
    ∀ᶠU:ℝ in atTop,1< U ∧ ∀d:ℝ,ds≤ d → b*U^(y/d)≤ U := by
  have he:∀ᶠU:ℝ in atTop,b≤ U^(1/20:ℝ):=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hp : 0 < d := by
    have hs : 0 < ds := by rw [joins_exact.1]; norm_num
    exact hs.trans_le hd
  have hy:y/d≤19/20:=by
    apply (div_le_iff₀ hp).mpr
    have hds : (1/2:ℝ) < ds := by rw [joins_exact.1]; norm_num
    have hd' : 1/2 < d := hds.trans_le hd
    have hyhi : y < 466/1000 := by rw [parameters_exact.2.2.2]; norm_num
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ):=mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U:=by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num

/-- The concrete masked fourth-moment premise needed by the actual packet/bin
bound. All constants precede every rowwise coefficient choice. -/
theorem full_active_box_fourth {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (kap:ℝ) (hkaplo:7/10≤ kap) (hkaphi:kap≤3/4)
    (hkapbeta:2*HeckeZeroSupremum.beta-1≤ kap) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bΦ mesh affineError : ℝ) (hAffineError : 0< affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bΦ mesh affineError U di control Ci)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hb:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,ds ≤ d → d ≤ dplus →
      ∀j∈Finset.range (coefficientBoxCount boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ mesh) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ scheduledCapacity d (2*((j:ℝ)*boxWidth+boxWidth+annulusSlack)) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(y/d)
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) := by
  obtain ⟨degree,C,hC,hmoment⟩ := full_original_numerator_fourth F kap hkaplo hkaphi hbeta hkapbeta
    bΦ mesh affineError hAffineError hsΦ di control Ci hCi hinput G loss annulusSlack 1 b 1
    hloss hann hb (by norm_num)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_new_cutoff_le_base b hb.le] with U hmom hcutoff
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN d hd hdmax j hj T width z height hw hwmesh hwmax hz hh him hselected hQ
  dsimp only
  let Y := U^(y/d)
  let Ccond:ℝ := fixedConductorConstant F.S
  let Lc (i:rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i:rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
  let m := 1-y/d+(j:ℝ)*boxWidth+boxWidth
  have hY : 0 < Y := Real.rpow_pos_of_pos hUp _
  have hCcond : 0 < Ccond := by
    dsimp [Ccond]
    exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  have hNu (i:rows) : 0 < rowNorm i.val :=
    (Real.rpow_pos_of_pos hUp _).trans_le (hrows i.val i.property).1
  have hL (i:rows) : Lc i ≤ 1 := by
    apply (div_le_one (mul_pos hCcond (hNu i))).mpr
    exact (data i).combined_le_row
  have hcut : b*Y ≤ U^((coefficientBoxCount boxWidth:ℝ)*boxWidth) := by
    apply (hcutoff.2 d hd).trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le
      (coefficientBoxCount_extent boxWidth hbox).1
  have hcombinedActive (i:rows) (hi:active i) :
      (data i).combinedConductor ≤ Ccond*U^m*(Y/N i) := by
    have hupper := active_dilation_upper U boxWidth (Lc i) (N i) b Y
      (coefficientBoxCount boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
    have hspec := (dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount boxWidth)
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
    simpa only [m,add_assoc] using hc
  let Nsafe (i:rows) := if active i then N i
    else fallbackCoefficientScale b Y Ccond (data i).combinedConductor U m
  have hsafe (i:rows) : 0 < Nsafe i ∧ Nsafe i ≤ b*Y ∧
      (data i).combinedConductor ≤ Ccond*U^m*(Y/Nsafe i) := by
    dsimp only [Nsafe]
    split_ifs with hi
    · exact ⟨hN i,hi.1,hcombinedActive i hi⟩
    · exact fallback_scale_admissible b Y Ccond (data i).combinedConductor U m
        hb hY hCcond (data i).combined_pos hUp
  obtain ⟨hm,hmmax⟩ := coefficient_box_geometry ⟨hd,hdmax⟩ hbox hann.le hsmall j hj
  have hcapacity := scheduled_capacity_or_empty T width ⟨hd,hdmax⟩
    (show 0≤(j:ℝ)*boxWidth+boxWidth+annulusSlack by positivity) hkaphi hw hselected
  have hcapacity' :
      (∃d' t':ℝ,ds≤ d' ∧ d'≤ dplus ∧ 0≤ t' ∧ t'≤ shiftCutoff ∧
        m+annulusSlack=shiftedPlain d' t' ∧
        (∑s,width s)≤ shiftedWidth d' t') ∨
        (2*(m+annulusSlack)+6*kap*(∑s,width s)≤1 ∨ T=∅) := by
    have he:m+annulusSlack=shiftedPlain d ((j:ℝ)*boxWidth+boxWidth+annulusSlack):=by
      dsimp [m,shiftedPlain]
      ring
    rw [he]
    exact hcapacity
  have hQ' (i:rows) : ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
      (U^(width s)) (z s)‖ ≤ (1:ℝ)*U^(1:ℝ) := by simpa using hQ i
  have hbound := hmom.2 rows hrows data Nsafe Y m hY (fun i=>⟨(hsafe i).1,(hsafe i).2.1⟩)
    hm hmmax (fun i=>(hsafe i).2.2) T width z height (fun i=>(hw i).le) hwmesh hwmax hz hh him
    hcapacity' hQ'
  apply (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>?_)).trans hbound
  change ‖if active i then _ else 0‖^4*_ ≤ _
  by_cases hi:active i
  · simp only [hi,ite_true,Nsafe,Y]
    exact le_rfl
  · simp only [hi,ite_false,norm_zero,zero_pow (by norm_num:4≠0),zero_mul]
    positivity


end Candidate.FourthPower.ReturnPhysicalActive
