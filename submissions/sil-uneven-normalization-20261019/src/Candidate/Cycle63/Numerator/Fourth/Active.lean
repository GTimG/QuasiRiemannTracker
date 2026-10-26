import Candidate.Cycle63.Numerator.Capacity.Schedule
import Candidate.Cycle25.Numerator.BoxGeometry
import Candidate.Cycle63.Numerator.Fourth.Original
import Candidate.Cycle25.Assembly.Mesh

/- Original module: Candidate.Cycle63.Numerator.Fourth.Geometry. -/
section

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace Cycle63.Numerator.Fourth
open Cycle63.Arithmetic
open Cycle25.Numerator

lemma physical_y_range {d : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus) :
    1/2≤ y/d ∧ y/d<1 := by
  have hs:=Physical.shiftBase_bounds hd
  have hp:=Physical.physical_d_pos hd.1
  refine ⟨by unfold Physical.shiftBase at hs;rw [mul_div_assoc] at hs;linarith,?_⟩
  apply (div_lt_one hp).mpr
  exact y_lt_half.trans (half_lt_dMinus.trans_le hd.1)

lemma coefficient_box_geometry {d xi slack : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus)
    (hx : 0<xi) (hs : 0≤ slack) (hsmall : 2*xi+slack≤1/2)
    (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount xi+1)) :
    0≤1-y/d+(j:ℝ)*xi+xi ∧ (1-y/d+(j:ℝ)*xi+xi)+slack≤2 := by
  have hy:=physical_y_range hd
  have hv:=coefficient_box_index_range xi hx j hj
  constructor <;> linarith

/-- A physical logarithmic conductor shift v enters the two-plain budget as
2v. This exact factor is retained in the public selected-capacity argument. -/
lemma scheduled_capacity_or_empty {α : Type*} (T : Finset α) (width : T→ℝ)
    {d t κ : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus) (ht : 0≤ t) (hk : κ≤3/4)
    (hw : ∀i,0<width i)
    (hselected : (∑i,width i)≤ Capacity.scheduledCapacity d (2*t)) :
    (∃d' t':ℝ,dMinus≤ d' ∧ d'≤ dPlus ∧ 0≤ t' ∧ t'≤ t0 ∧
      Physical.plainScale d t=Physical.plainScale d' t' ∧
      (∑i,width i)≤ Physical.affineCapacity d' t') ∨
      (2*Physical.plainScale d t+6*κ*(∑i,width i)≤1 ∨ T=∅) := by
  have hsum:0≤∑i,width i:=Finset.sum_nonneg (fun i _=>(hw i).le)
  by_cases hsmall:t≤ t0
  · left
    refine ⟨d,t,hd.1,hd.2,ht,hsmall,rfl,?_⟩
    simpa [Capacity.scheduledCapacity,show 2*t≤2*t0 by linarith] using hselected
  · right
    have hlarge:¬2*t≤2*t0:=by linarith
    have hselected':(∑i,width i)≤ Physical.oldCapacity (Physical.shiftBase d) t:=by
      simpa [Capacity.scheduledCapacity,hlarge] using hselected
    by_cases hraw:0≤(Physical.shiftBase d-2*t)/(9/2)
    · left
      have hs:(∑i,width i)≤(Physical.shiftBase d-2*t)/(9/2):=by
        simpa [Physical.oldCapacity,max_eq_right hraw] using hselected'
      have hbudget:2*Physical.plainScale d t+(9/2)*(∑i,width i)≤1:=by
        unfold Physical.plainScale Physical.shiftBase at *
        rw [mul_div_assoc] at hs
        linarith
      nlinarith
    · right
      have hs:(∑i,width i)≤0:=by
        simpa [Physical.oldCapacity,max_eq_left (le_of_not_ge hraw)] using hselected'
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hs':width ⟨i,hi⟩≤∑i,width i:=Finset.single_le_sum
        (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
      linarith [hw ⟨i,hi⟩]

end Cycle63.Numerator.Fourth
end

/- Original module: Candidate.Cycle63.Numerator.Fourth.Active. -/
section

/-! Actual rowwise coefficient choices on one finite dilation box. Inactive
choices are replaced by a positive admissible scale before invoking the moment
bound, and their nonnegative contribution is subsequently discarded. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Cycle63.Numerator.Fourth
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentFiniteProfileExceptional
open Cycle63.Arithmetic
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

lemma eventually_new_cutoff_le_base (b:ℝ) (hb:0≤ b) :
    ∀ᶠU:ℝ in atTop,1<U ∧ ∀d:ℝ,dMinus≤ d → b*U^(y/d)≤ U := by
  have he:∀ᶠU:ℝ in atTop,b≤ U^(1/20:ℝ):=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hp:=Physical.physical_d_pos hd
  have hy:y/d≤19/20:=by
    apply (div_le_iff₀ hp).mpr
    have hd':1/2<d:=half_lt_dMinus.trans_le hd
    norm_num [y] at *
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ):=mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U:=by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num

/-- The concrete masked fourth-moment premise needed by the actual packet/bin
bound. All constants precede every rowwise coefficient choice. -/
theorem affine_active_box_fourth {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (kap:ℝ) (hkaplo:7/10≤ kap) (hkaphi:kap≤3/4)
    (hkapbeta:2*HeckeZeroSupremum.beta-1≤ kap) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bΦ mesh affineError : ℝ) (hAffineError : 0<affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh affineError U di control Ci)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hb:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,dMinus ≤ d → d ≤ dPlus →
      ∀j∈Finset.range (coefficientBoxCount boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ mesh) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ Capacity.scheduledCapacity d (2*((j:ℝ)*boxWidth+boxWidth+annulusSlack)) →
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
  obtain ⟨degree,C,hC,hmoment⟩ := affine_original_numerator_fourth F kap hkaplo hkaphi hbeta hkapbeta
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
      (∃d' t':ℝ,dMinus≤ d' ∧ d'≤ dPlus ∧ 0≤ t' ∧ t'≤ t0 ∧
        m+annulusSlack=Physical.plainScale d' t' ∧
        (∑s,width s)≤ Physical.affineCapacity d' t') ∨
        (2*(m+annulusSlack)+6*kap*(∑s,width s)≤1 ∨ T=∅) := by
    have he:m+annulusSlack=Physical.plainScale d ((j:ℝ)*boxWidth+boxWidth+annulusSlack):=by
      dsimp [m,Physical.plainScale]
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

end Cycle63.Numerator.Fourth
end

/- Adapted from Cycle25 active physical box restriction, Apache-2.0.
The capacity argument keeps the exact factor two from conductor dilation. -/
end
