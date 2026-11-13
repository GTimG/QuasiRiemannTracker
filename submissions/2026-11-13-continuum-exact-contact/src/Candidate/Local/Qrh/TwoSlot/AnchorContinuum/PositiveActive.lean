/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Active dyadic fourth moment for the variable source. Adapted from PR137 Active
(Sil and predecessor authors, Apache-2.0). The max-one dilation, row masks and
fallback coefficient scales are retained. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSelection
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Active

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRowRadicalConductor
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open Cycle25.Weighted.Numerator Cycle25.Numerator
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

theorem eventually_cutoff_le_base (b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ U : ℝ in atTop, 1 < U ∧ ∀ d : ℝ, (3/4:ℝ) ≤ d → b*U^(Geometry.y/d) ≤ U := by
  have he : ∀ᶠ U : ℝ in atTop, b ≤ U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdpos : 0 < d := by linarith
  have hy : Geometry.y/d ≤ (19/20:ℝ) := by
    apply (div_le_iff₀ hdpos).mpr
    linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.ly_coarse.2]
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)]; norm_num

/-- The literal masked active-box fourth moment. The conductor range is stated
geometrically instead of read from a fixed-fee schedule. -/
theorem active_box_fourth_with_cost (A : ChosenData) {s : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1/1000000000) (kap : ℝ)
    (hklo : (7/10:ℝ) ≤ kap) (hkhi : kap ≤ (3/4:ℝ))
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ kap) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bPhi error : ℝ) (herror : 0 < error)
    (hsPhi : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0 < Ci)
    (hinput : ∀ᶠ U : ℝ in atTop,
      affineAtFace (PositiveSource.physicalFace s) A bPhi error U di control Ci)
    (G : 𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b : ℝ)
    (hloss : 0 < loss) (hbox : 0 < boxWidth) (hann : 0 < annulusSlack) (hb : 0 < b)
    (hsmall : 2*boxWidth+annulusSlack ≤ 1/2) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ data : ∀ i : rows, PhysicalReflectionData A.F.S A.F.exclusions.prime i.val,
      ∀ N : rows → ℝ, (∀ i, 0 < N i) → ∀ d : ℝ, (3/4:ℝ) ≤ d → d ≤ 2*Geometry.y →
      ∀ j ∈ Finset.range (coefficientBoxCount boxWidth+1),
      ∀ T : Finset (Fin A.D.N), ∀ width : T → ℝ, ∀ z : T → ℂ, ∀ height : ℝ,
      (∀ i, 0 < width i) → (∀ i, width i ≤ A.sourceMesh) →
      (∀ i, width i ≤ Cycle25.sourceMesh A.D.t) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      (∑ i, width i) ≤ Selection.scheduledCapacity s d
        (2*((j:ℝ)*boxWidth+boxWidth+annulusSlack)) →
      (∀ i : rows, ‖∏ k, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
        A.F.W 2 (U^(width k)) (z k)‖ ≤ U) →
      let Y := U^(Geometry.y/d)
      let Lc (i : rows) := (data i).combinedConductor/
        ((fixedConductorConstant A.F.S:ℝ)*rowNorm i.val)
      (∑ i : rows, ‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i)) = j
        then HeckeDyadic.polynomial (rowCharacter A.F.S A.F.exclusions.prime i.val)
          false G (Y/N i) 0 0 else 0‖^4 *
        ‖∏ k, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
          A.F.W 2 (U^(width k)) (z k)‖^2) ≤ C*(1+height)^degree*U^(1+A.D.t+error+loss) := by
  obtain ⟨degree,C,hC,hmoment⟩ := original_fourth_with_cost A hs hsmax kap hklo hkhi hbeta hkbeta
    bPhi error herror hsPhi di control Ci hCi hinput G loss annulusSlack 1 b 1
    hloss hann hb (by norm_num)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_cutoff_le_base b hb.le] with U hmom hcutoff
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN d hd hdmax j hj T width z height hw hwmesh hwmax hz hh him hselected hQ
  dsimp only
  let Y := U^(Geometry.y/d)
  let Ccond : ℝ := fixedConductorConstant A.F.S
  let Lc (i : rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i : rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i)) = j
  let m := 1-Geometry.y/d+(j:ℝ)*boxWidth+boxWidth
  have hY : 0 < Y := Real.rpow_pos_of_pos hUp _
  have hCcond : 0 < Ccond := by
    dsimp [Ccond]
    exact_mod_cast fixedConductorConstant_pos A.F.S A.F.exclusions.prime
  have hNu (i : rows) : 0 < rowNorm i.val :=
    (Real.rpow_pos_of_pos hUp _).trans_le (hrows i.val i.property).1
  have hL (i : rows) : Lc i ≤ 1 := by
    apply (div_le_one (mul_pos hCcond (hNu i))).mpr
    exact (data i).combined_le_row
  have hcut : b*Y ≤ U^((coefficientBoxCount boxWidth:ℝ)*boxWidth) := by
    apply (hcutoff.2 d hd).trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le
      (coefficientBoxCount_extent boxWidth hbox).1
  have hcombinedActive (i : rows) (hi : active i) :
      (data i).combinedConductor ≤ Ccond*U^m*(Y/N i) := by
    have hupper := active_dilation_upper U boxWidth (Lc i) (N i) b Y
      (coefficientBoxCount boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
    have hspec := (dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount boxWidth)
      (max 1 (Lc i*N i)) (le_max_left _ _) hupper).2
    rw [hi.2] at hspec
    have hprod : Lc i*N i = (data i).combinedConductor*N i/(Ccond*rowNorm i.val) := by
      dsimp only [Lc]
      ring
    have hexp : ((j:ℝ)+1)*boxWidth = (j:ℝ)*boxWidth+boxWidth := by ring
    rw [hprod,hexp] at hspec
    have hc := combined_scale_of_dilation (data i).combinedConductor Ccond (rowNorm i.val)
      (N i) Y U (Geometry.y/d) ((j:ℝ)*boxWidth+boxWidth)
      hCcond (hNu i) (hN i) hUp (hrows i.val i.property).2 rfl hspec
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
  have hdpos : 0 < d := by linarith
  have hylo : (1/2:ℝ) ≤ Geometry.y/d := (le_div_iff₀ hdpos).mpr (by linarith)
  have hyhi : Geometry.y/d < 1 := (div_lt_one hdpos).mpr (by
    linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.ly_coarse.2])
  have hv := coefficient_box_index_range boxWidth hbox j hj
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hmmax : m+annulusSlack ≤ 2 := by dsimp [m]; linarith
  have hcapacity := Selection.selected_admissible_or_empty T width hs hw hselected
  have hcapacity' :
      (2*(m+annulusSlack)+(2+10*s)*(∑ i, width i) ≤ 1-s ∧ (∑ i, width i) ≤ 3/40) ∨
        (2*(m+annulusSlack)+6*kap*(∑ i, width i) ≤ 1 ∨ T = ∅) := by
    rcases hcapacity with hc | he
    · left
      simpa only [Selection.plainScale,m,add_assoc] using hc
    · exact Or.inr (Or.inr he)
  have hQ' (i : rows) : ‖∏ k, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
      A.F.W 2 (U^(width k)) (z k)‖ ≤ (1:ℝ)*U^(1:ℝ) := by simpa using hQ i
  have hbound := hmom.2 rows hrows data Nsafe Y m hY (fun i => ⟨(hsafe i).1,(hsafe i).2.1⟩)
    hm hmmax (fun i => (hsafe i).2.2) T width z height (fun i => (hw i).le)
    hwmesh hwmax hz hh him hcapacity' hQ'
  apply (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ?_)).trans hbound
  change ‖if active i then _ else 0‖^4*_ ≤ _
  by_cases hi : active i
  · simp only [hi,ite_true,Nsafe,Y]
    exact le_rfl
  · simp only [hi,ite_false,norm_zero,zero_pow (by norm_num : 4 ≠ 0),zero_mul]
    positivity

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.active_box_fourth_with_cost
