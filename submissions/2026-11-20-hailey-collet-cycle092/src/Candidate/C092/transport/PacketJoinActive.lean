/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Q source on the literal masked coefficient boxes. Adapted from Collet/Gao
PhysicalDirect.Active with the actual Q capacity, no old geometry/schedule. -/
import Candidate.C092.transport.DirectActualFourth
import Candidate.C092.transport.SelectedNonfloorPacket
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.BoxGeometry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Classical BigOperators SchwartzMap
open Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator Cycle25.Numerator
namespace QRH.Cycle092.PacketJoin
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


/-- The actual source proves the all-coefficient-choice moment required by the
label packet, after the original cutoff and max-one dilation are imposed. -/
theorem q_active_box_fourth
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (hAffineError : 0 < affineError) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ (D : Cycle25.Weighted.MomentData)
      (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
      (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
      (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ κ)
      (G : 𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b : ℝ),
      0 < loss → 0 < boxWidth → 0 < annulusSlack → 0 < b →
      2*boxWidth+annulusSlack ≤ 1/2 →
      ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u∈rows,U^(1/100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (data : ∀ i : rows, PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : rows → ℝ), (∀ i, 0 < N i) →
      ∀ y d : ℝ, (1/2 : ℝ) ≤ y/d → y/d ≤ 19/20 →
      ∀ j∈Finset.range (coefficientBoxCount boxWidth+1),
      ∀ (T : Finset (Fin D.N)) (width : T → ℝ) (z : T → ℂ) (height : ℝ),
      (∀ i,0 < width i) → (∀ i,width i ≤ mesh) →
      (∀ i,width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀ i,(z i).re=17/50) → 0 ≤ height → (∀ i,|(z i).im| ≤ height) →
      (∑ i,width i) ≤ Physical.Selection.scheduledCapacity y Cycle090.sourceCost d
        (2*((j:ℝ)*boxWidth+boxWidth+annulusSlack)) →
      (∀ i : rows,‖∏ s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(y/d)
      let Lc (i : rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑ i : rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏ s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) := by
  obtain ⟨mesh,hm,hmoment⟩ := DirectEnergy.q_original_numerator_fourth hβ affineError hAffineError
  refine ⟨mesh,hm,?_⟩
  intro D F κ hk hk' hkβ G loss boxWidth annulusSlack b hloss hbox hann hb hsmall
  obtain ⟨degree,C,hC,hmoment⟩ := hmoment D F κ hk hk' hkβ G loss annulusSlack 1 b 1
    hloss hann hb (by norm_num)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).eventually
    (eventually_ge_atTop b)] with U hmom hbU
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN y d hy hy' j hj T width z height hw hwmesh hwmax hz hh him hselected hQ
  dsimp only
  let Y := U^(y/d)
  let Ccond : ℝ := fixedConductorConstant F.S
  let Lc (i : rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i : rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
  let m := 1-y/d+(j:ℝ)*boxWidth+boxWidth
  have hY : 0 < Y := Real.rpow_pos_of_pos hUp _
  have hCcond : 0 < Ccond := by
    dsimp [Ccond]
    exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  have hNu (i : rows) : 0 < rowNorm i.val :=
    (Real.rpow_pos_of_pos hUp _).trans_le (hrows i.val i.property).1
  have hL (i : rows) : Lc i ≤ 1 :=
    (div_le_one (mul_pos hCcond (hNu i))).mpr (data i).combined_le_row
  have hcutoff : b*Y ≤ U := by
    calc
      _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul hbU
        (Real.rpow_le_rpow_of_exponent_le hU.le hy') (by positivity) (by positivity)
      _ = U := by rw [←Real.rpow_add hUp]; norm_num
  have hcut : b*Y ≤ U^((coefficientBoxCount boxWidth:ℝ)*boxWidth) := by
    apply hcutoff.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le
      (coefficientBoxCount_extent boxWidth hbox).1
  have hcombinedActive (i : rows) (hi : active i) :
      (data i).combinedConductor ≤ Ccond*U^m*(Y/N i) := by
    have hupper := active_dilation_upper U boxWidth (Lc i) (N i) b Y
      (coefficientBoxCount boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
    have hspec := (dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount boxWidth)
      (max 1 (Lc i*N i)) (le_max_left _ _) hupper).2
    rw [hi.2] at hspec
    have hb' : max 1 ((data i).combinedConductor*N i/(Ccond*rowNorm i.val)) ≤
        U^((j:ℝ)*boxWidth+boxWidth) := by
      have hprod : Lc i*N i = (data i).combinedConductor*N i/(Ccond*rowNorm i.val) := by
        dsimp only [Lc]; ring
      rw [hprod,show ((j:ℝ)+1)*boxWidth = (j:ℝ)*boxWidth+boxWidth by ring] at hspec
      exact hspec
    have hc := combined_scale_of_dilation (data i).combinedConductor Ccond (rowNorm i.val)
      (N i) Y U (y/d) ((j:ℝ)*boxWidth+boxWidth)
      hCcond (hNu i) (hN i) hUp (hrows i.val i.property).2 rfl hb'
    simpa only [m,add_assoc] using hc
  let Nsafe (i : rows) := if active i then N i
    else fallbackCoefficientScale b Y Ccond (data i).combinedConductor U m
  have hsafe (i : rows) : 0 < Nsafe i ∧ Nsafe i ≤ b*Y ∧
      (data i).combinedConductor ≤ Ccond*U^m*(Y/Nsafe i) := by
    dsimp only [Nsafe]
    split_ifs with hi
    · exact ⟨hN i,hi.1,hcombinedActive i hi⟩
    · exact fallback_scale_admissible b Y Ccond (data i).combinedConductor U m
        hb hY hCcond (data i).combined_pos hUp
  have hv := coefficient_box_index_range boxWidth hbox j hj
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hmmax : m+annulusSlack ≤ 2 := by dsimp [m]; linarith
  have hgate := Physical.Selection.selected_admissible_or_empty T width
    Cycle090.allowances_pos.1.le hw hselected
  have hcapacity : (((∑ i,width i) ≤ Cycle090.physicalCap ∧
      2*(m+annulusSlack)+(2+10*Cycle090.sourceCost)*(∑ i,width i) ≤ 1-Cycle090.sourceCost) ∨
      (2*(m+annulusSlack)+6*κ*(∑ i,width i) ≤ 1 ∨ T=∅)) := by
    rcases hgate with h | h
    · left
      refine ⟨h.2,?_⟩
      simpa only [Physical.Selection.plainScale,m,add_assoc] using h.1
    · exact Or.inr (Or.inr h)
  have hQ' (i : rows) : ‖∏ s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
      (U^(width s)) (z s)‖ ≤ (1:ℝ)*U^(1:ℝ) := by simpa using hQ i
  have hbound := hmom.2 rows hrows data Nsafe Y m hY (fun i=>⟨(hsafe i).1,(hsafe i).2.1⟩)
    hm hmmax (fun i=>(hsafe i).2.2) T width z height (fun i=>(hw i).le) hwmesh hwmax hz hh him
    hcapacity hQ'
  apply (Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>?_)).trans hbound
  change ‖if active i then _ else 0‖^4*_ ≤ _
  by_cases hi : active i
  · simp only [hi,ite_true,Nsafe,Y]
    exact le_rfl
  · simp only [hi,ite_false,norm_zero,zero_pow (by norm_num : 4≠0),zero_mul]
    positivity

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.q_active_box_fourth
