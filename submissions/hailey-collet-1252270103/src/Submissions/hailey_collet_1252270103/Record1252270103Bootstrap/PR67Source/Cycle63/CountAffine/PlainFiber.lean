import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPlainFiberCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.CountAffine.ClosedForm
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Detector fiber count whose plain witness is controlled by the interior affine moment.
Adapted from the pinned OpenAI `plain_fiber_count` (Apache-2.0): only the moment invoked for
the selected slots changes. Released under Apache 2.0. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.Cycle63AffinePlainFiberCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

/-- A plain witness in the affine window is counted with the affine slot capacity. Selected
slot sets shorter than the window's lower width use the original moment instead. -/
theorem affine_plain_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→ Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b widths g : Slot→ℝ) (zs : Slot→ℂ)
    (mesh binWidth z κplain εm C height : ℝ) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤ mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (physical M H row W b widths zs U u s)=g s)
    (_hκ : 0≤κplain) (hκ1 : κplain≤3/4) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (_hmlo : Cycle63.CountAffine.windowBottom≤Real.logb U ((2 : ℝ)^K.val))
    (hmhi : Real.logb U ((2 : ℝ)^K.val)≤Cycle63.CountAffine.plainTop)
    (hcap1 : z≤Cycle63.Optimization.slotTop)
    (hcap2 : 2*Real.logb U ((2 : ℝ)^K.val)+Cycle63.Arithmetic.lambda*z≤Cycle63.Arithmetic.B)
    (haffine : ∀ selected : Finset Slot, selected⊆slots →
      Cycle63.Optimization.slotFloor≤∑ s∈selected,widths s → (∑ s∈selected,widths s)≤Cycle63.Optimization.slotTop →
      2*Real.logb U ((2 : ℝ)^K.val)+Cycle63.Arithmetic.lambda*(∑ s∈selected,widths s)≤
        Cycle63.Arithmetic.B →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤C*U^(1+εm))
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*(∑ s∈selected,widths s)≤1 →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(1-2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)-2*weightedMean slots widths g*z+
        4*ε+(2*a-1)*mesh+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_physical_product M H rows hne slots
    row W b widths g zs U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hs0 : 0≤∑ s∈selected,widths s := Finset.sum_nonneg (fun s hs => (hw s (hsub hs)).le)
  have hmom : ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular) (U^m) σ freq*
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular) (U^m) σ freq*
          (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤C*U^(1+εm) := by
    by_cases hlong : Cycle63.Optimization.slotFloor≤∑ s∈selected,widths s
    · have hl : Cycle63.Arithmetic.lambda*(∑ s∈selected,widths s)≤Cycle63.Arithmetic.lambda*z :=
        mul_le_mul_of_nonneg_left hlen Cycle63.Arithmetic.lambda_pos.le
      exact haffine selected hsub hlong (hlen.trans hcap1) (by linarith)
    · have hshort : (∑ s∈selected,widths s)<Cycle63.Optimization.slotFloor := lt_of_not_ge hlong
      have h6 : 6*κplain*(∑ s∈selected,widths s)≤(9/2)*Cycle63.Optimization.slotFloor := by
        have h1 : 6*κplain≤9/2 := by linarith
        have h2 := mul_le_mul h1 hshort.le hs0 (by norm_num)
        linarith
      have htop : 2*Real.logb U ((2 : ℝ)^K.val)≤2*Cycle63.CountAffine.plainTop := by
        have : Real.logb U ((2 : ℝ)^K.val)≤Cycle63.CountAffine.plainTop := by
          simpa [Cycle63.CountAffine.plainTop] using hmhi
        linarith
      exact hraw selected hsub (by linarith [Cycle63.Physical.small_slot_complement])
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s) hDp (by norm_num)
    positiveAnnular_support hE height hheight hfreq hmom
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤
      (192*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  have hc := HeckeDetectorRowCount.plain_count rows (fun u => χ u label)
    positiveAnnular (U^m) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s)
    U (2*a-1) m (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (192*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.2) hspike he'
  convert hc using 1; congr 2; ring

end SevenEighths.Cycle63AffinePlainFiberCount

end

end OAI

end Record1252270103Bootstrap.PR67
