import Cycle25.Energy.Physical.OriginalFourth
import Cycle25.Numerator.BoxGeometry
import Cycle25.Assembly.Mesh

/-! Actual rowwise coefficient choices on one finite dilation box. Inactive
choices are replaced by a positive admissible scale before invoking the moment
bound, and their nonnegative contribution is subsequently discarded. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Cycle25.Numerator
open Cycle25.Weighted.Numerator Cycle25.Weighted.Numerator.PhysicalMoment
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

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

/-- The concrete masked fourth-moment premise needed by the actual packet/bin
bound. All constants precede every rowwise coefficient choice. -/
theorem certified_active_box_fourth {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (kap:ℝ) (hkaplo:7/10≤kap) (hkaphi:kap≤3/4)
    (hkapbeta:2*HeckeZeroSupremum.beta-1≤kap) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hb:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,(1/2:ℝ) ≤ d → d ≤ Cycle25.h+Cycle25.rowExtension →
      ∀j∈Finset.range (coefficientBoxCount boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ selectedCapacity kap ((2*(Cycle25.ly/d)-1)/(6*kap)-annulusSlack/(3*kap))
        ((j:ℝ)*boxWidth+boxWidth) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(Cycle25.ly/d)
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,C,hC,hmoment⟩ := certified_original_numerator_fourth F kap hkaplo hkaphi hbeta hkapbeta G loss annulusSlack 1 b 1
    hloss hann hb (by norm_num)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_physical_cutoff_le_base b hb.le] with U hmom hcutoff
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN d hd hdmax j hj T width z height hw hwmax hz hh him hselected hQ
  dsimp only
  let Y := U^(Cycle25.ly/d)
  let Ccond:ℝ := fixedConductorConstant F.S
  let Lc (i:rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i:rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
  let m := 1-Cycle25.ly/d+(j:ℝ)*boxWidth+boxWidth
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
      (N i) Y U (Cycle25.ly/d) ((j:ℝ)*boxWidth+boxWidth)
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
  obtain ⟨hm,hmmax⟩ := physical_coefficient_box_geometry d boxWidth annulusSlack
    hd hdmax hbox hann.le hsmall j hj
  have hcapacity := physical_reflected_capacity_or_empty_subtype T width kap (Cycle25.ly/d)
    ((j:ℝ)*boxWidth) boxWidth annulusSlack (by linarith) hw hselected
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

end Cycle25.Numerator
end

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
