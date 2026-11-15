/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted from Sil's PhysicalDirect.OldActive and Hailey Collet's certified
original numerator fourth moment (Apache-2.0). The adaptation removes all
endpoint geometry and takes an empty selected product. Original physical
reflection data, masks and row-dependent coefficient scales are unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.OldActive

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Qrh.TwoSlot.AnchorZeroLoss
open Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle25.Weighted.Numerator.PhysicalMoment
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth
local notation "O" => HeckeFamily.O

/-- Unmarked fourth moments on every active coefficient box, uniformly for
all source exponents in (0,99]. No endpoint geometry, count estimate, selected
large-value event, or affine-source hypothesis occurs in this theorem. -/
theorem floor_active_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (kap : ℝ) (hkaplo : 7/10 ≤ kap) (hkaphi : kap ≤ 3/4)
    (hkapbeta : 2*HeckeZeroSupremum.beta-1 ≤ kap)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (G : 𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b : ℝ)
    (hloss : 0 < loss) (hbox : 0 < boxWidth) (hann : 0 < annulusSlack)
    (hb : 0 < b) (hsmall : 2*boxWidth+annulusSlack ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ data : ∀i:rows, PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀ N : rows → ℝ, (∀i,0 < N i) → ∀ v : ℝ, 0 < v → v ≤ 99 →
      ∀ j ∈ Finset.range (coefficientBoxCount100 boxWidth+1),
      let Y := U^v
      let Lc (i:rows) := (data i).combinedConductor/
        ((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows, ‖if N i ≤ b*Y ∧
        dilationBox U boxWidth (coefficientBoxCount100 boxWidth)
          (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val)
          false G (Y/N i) 0 0 else 0‖^4) ≤ C*U^(1+D.t+loss) := by
  obtain ⟨degree,C,hC,hmoment⟩ := certified_original_numerator_fourth F kap hkaplo hkaphi
    hbeta hkapbeta G loss annulusSlack 0 b 1 hloss hann hb (by norm_num)
  have hbpow : ∀ᶠ U:ℝ in atTop, b ≤ U^boxWidth :=
    (tendsto_rpow_atTop hbox).eventually (eventually_ge_atTop _)
  refine ⟨C,hC,?_⟩
  filter_upwards [hmoment,hbpow,eventually_ge_atTop b] with U hmom hbpow hbU
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN v hv hvhi j hj
  dsimp only
  let Y := U^v
  let Ccond:ℝ := fixedConductorConstant F.S
  let Lc (i:rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i:rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount100 boxWidth) (max 1 (Lc i*N i))=j
  let m := reflectedLength (v) ((j:ℝ)*boxWidth+boxWidth)
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
    have he : v ≤ (99:ℝ) := hvhi
    calc
      b*Y ≤ U^(1:ℝ)*U^(99:ℝ) := mul_le_mul (by simpa only [Real.rpow_one] using hbU)
        (Real.rpow_le_rpow_of_exponent_le hU.le he) (by positivity) (by positivity)
      _ = U^(100:ℝ) := by rw [← Real.rpow_add hUp]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU.le (by
        have hh := mul_le_mul_of_nonneg_right (Nat.le_ceil (100/boxWidth)) hbox.le
        simpa only [coefficientBoxCount100, div_mul_cancel₀ _ hbox.ne'] using hh)
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
      (N i) Y U (v) ((j:ℝ)*boxWidth+boxWidth)
      hCcond (hNu i) (hN i) hUp (hrows i.val i.property).2 rfl hb'
    have hraw:1-v+((j:ℝ)*boxWidth+boxWidth)≤ m:=by
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
    · have hCu : 0 < (data i).combinedConductor := (data i).combined_pos
      have hpos : 0 < min (b*Y) (Ccond*U^m*Y/(data i).combinedConductor) :=
        lt_min (mul_pos hb hY) (by positivity)
      refine ⟨hpos, min_le_left _ _, ?_⟩
      change (data i).combinedConductor ≤ Ccond*U^m*
        (Y/min (b*Y) (Ccond*U^m*Y/(data i).combinedConductor))
      rw [←mul_div_assoc, le_div_iff₀ hpos]
      have hh := (le_div_iff₀ (data i).combined_pos).mp
        (min_le_right (b*Y) (Ccond*U^m*Y/(data i).combinedConductor))
      simpa only [mul_comm (data i).combinedConductor] using hh
  by_cases hex:∃i:rows,active i
  swap
  · have hn:∀i:rows,¬active i:=fun i hi=>hex ⟨i,hi⟩
    change (∑i:rows,‖if active i then _ else 0‖^4)≤_
    simp only [hn,ite_false,norm_zero,zero_pow (by norm_num:4≠0),Finset.sum_const_zero]
    positivity
  obtain ⟨i,hi⟩:=hex
  have hupper:=active_dilation_upper U boxWidth (Lc i) (N i) b Y
    (coefficientBoxCount100 boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
  have hlo:U^((j:ℝ)*boxWidth)≤ max 1 (Lc i*N i):=by
    have hh:=(dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount100 boxWidth)
      (max 1 (Lc i*N i)) (le_max_left _ _) hupper).1
    rw [hi.2] at hh
    exact hh
  have hmax:max 1 (Lc i*N i)≤ U^(v+boxWidth):=by
    apply max_le
    · exact Real.one_le_rpow hU.le (by positivity)
    · calc
        _ ≤ N i:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hL i) (hN i).le
        _ ≤ b*Y:=hi.1
        _ ≤ U^boxWidth*U^(v):=mul_le_mul_of_nonneg_right hbpow (by positivity)
        _ = _:=by rw [←Real.rpow_add hUp];congr 1;ring
  have hjv:(j:ℝ)*boxWidth≤ v+boxWidth:=(Real.rpow_le_rpow_left_iff hU).mp (hlo.trans hmax)
  have hm : 0 ≤ m := le_max_left _ _
  have hmhi : m ≤ 1+2*boxWidth := by
    dsimp [m, reflectedLength]
    apply max_le <;> linarith
  have hmmax:m+annulusSlack≤2:=by linarith
  let T : Finset (Fin D.N) := ∅
  let width : T → ℝ := fun _ => 0
  let z : T → ℂ := fun _ => 0
  have hbound := hmom.2 rows hrows data Nsafe Y m hY
    (fun i=>⟨(hsafe i).1,(hsafe i).2.1⟩) hm hmmax
    (fun i=>(hsafe i).2.2) T width z 0
    (by intro i; exact Finset.notMem_empty i.val i.property |>.elim)
    (by intro i; exact Finset.notMem_empty i.val i.property |>.elim)
    (by intro i; exact Finset.notMem_empty i.val i.property |>.elim)
    le_rfl
    (by intro i; exact Finset.notMem_empty i.val i.property |>.elim)
    (Or.inr rfl) (by intro i; simp [T])
  simp only [T, Fintype.prod_empty, norm_one, one_pow, mul_one, add_zero] at hbound
  apply (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>?_)).trans hbound
  change ‖if active i then _ else 0‖^4 ≤ _
  by_cases hi:active i
  · simp only [hi,ite_true,Nsafe,Y]
    exact le_rfl
  · simp only [hi,ite_false,norm_zero,zero_pow (by norm_num:4≠0)]
    positivity

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.floor_active_fourth
