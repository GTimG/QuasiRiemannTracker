/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from the OpenAI baseline `HeckeDetectorInverseFiberCount.inverse_fiber_count` and
`HeckeDetectorPlainFiberCount.plain_fiber_count` (Apache-2.0): the native capacity gates
`r + 2z < 1, 2r + 8z < 3` (inverse) and `2m + 6κz ≤ 1` (ordinary) are replaced by the bare
selected-width cap `∑ widths ≤ z`. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPlainFiberCount
import Submissions.hailey_collet_1252270103.Record12518109Gain.FiberPrimitives

/-!
# High.FiberCount

Marked detector counts of one detector fiber with an arbitrary moment source: if the marked
moment (inverse, resp. ordinary two-factor) holds for every selection of whole slots of total
width at most `z`, then the fiber has at most `C' U^(1 - ν r - e z + losses)` rows, where
`ν = 2a - 1` and `e = 2·(slot bin mean)` (the selection of the largest-amplitude whole slots,
`select_physical_product`). In the HIGH child `z = σ(w')` at the witness width `w'`, and the moment
comes from the anchor of an earlier stage (or the native source above `TOP`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
local notation "O" => HeckeFamily.O

/-- Whole-slot selection of width `≤ z` with the common lower amplitude, also when there are no
slots (`∑ widths = 0`, then `z = 0` and the empty selection). -/
theorem select_or_empty {Row Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (slots : Finset Slot)
    (Q : Row→Slot→ℂ) (w g : Slot→ℝ) (U δ mesh binWidth z : ℝ)
    (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<w s) (hwm : ∀ s∈slots,w s≤mesh)
    (hL : 0≤∑ s∈slots,w s) (hz : 0≤z) (hzL : z≤∑ s∈slots,w s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(w s)) (δ/2) binWidth (Q u s)=g s) :
    ∃ selected : Finset Slot,selected⊆slots ∧ (∑ s∈selected,w s)≤z ∧
      ∀ u∈rows,U^(2*weightedMean slots w g*z-δ*mesh)≤‖∏ s∈selected,Q u s‖^2 := by
  rcases lt_or_eq_of_le hL with hpos | hzero
  · obtain ⟨sel,hsub,-,hlen,hsp⟩ := Record12518109GainFiber.select_common_product rows hne slots
      Q w g U δ mesh binWidth z hU hδ hmesh hbin hw hwm hpos hz hzL hbins
    exact ⟨sel,hsub,hlen,hsp⟩
  · have hz0 : z=0 := le_antisymm (hzL.trans hzero.symm.le) hz
    refine ⟨∅,Finset.empty_subset _,by simp [hz0],fun u _ => ?_⟩
    rw [hz0, Finset.prod_empty, norm_one, one_pow, mul_zero, zero_sub]
    exact Real.rpow_le_one_of_one_le_of_nonpos hU.le (by nlinarith)


/-- Inverse marked count of one fiber, gated only by the selected width `≤ z`. -/
theorem gated_inverse_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (mesh binWidth z εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0≤∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (Q u s)=g s)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ selected : Finset Slot, selected⊆slots → (∑ s∈selected,widths s)≤z →
      ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) true
          ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
          (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*
            (∏ s∈selected,Q u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤(12*(1+height)*C)*
      U^(1-(2*a-1)*Real.logb U ((2 : ℝ)^J.val)-2*weightedMean slots widths g*z+
        2*ε+(2*a-1)*mesh+εm) := by
  let r := Real.logb U ((2 : ℝ)^J.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hlen,hspike⟩ := select_or_empty rows hne slots Q widths g U (2*a-1)
    mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.inverse_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label (inverseTest U tstar r) (U^r) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,Q u s) hDp (by norm_num)
    (HeckeDetectorDyadicActual.inverse_profile_support _ _) hE height hheight hfreq
    (hraw selected hsub hlen)
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) true (inverseTest U tstar r) (U^r) (witness u).zero.re
        (witness u).frequency*(∏ s∈selected,Q u s)‖^2≤
      (12*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  exact HeckeDetectorRowCount.inverse_count rows (fun u => χ u label)
    (inverseTest U tstar r) (U^r) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,Q u s)
    U (2*a-1) r (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (12*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.1) hspike he'

/-- Ordinary two-factor marked count of one fiber, gated only by the selected width `≤ z`. -/
theorem gated_plain_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (mesh binWidth z εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0≤∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (Q u s)=g s)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ selected : Finset Slot, selected⊆slots → (∑ s∈selected,widths s)≤z →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,Q u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(1-2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)-2*weightedMean slots widths g*z+
        4*ε+(2*a-1)*mesh+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hlen,hspike⟩ := select_or_empty rows hne slots Q widths g U (2*a-1)
    mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,Q u s) hDp (by norm_num)
    positiveAnnular_support hE height hheight hfreq (hraw selected hsub hlen)
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        (∏ s∈selected,Q u s)‖^2≤
      (192*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  have hc := HeckeDetectorRowCount.plain_count rows (fun u => χ u label)
    positiveAnnular (U^m) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,Q u s)
    U (2*a-1) m (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (192*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.2) hspike he'
  convert hc using 1; congr 2; ring

end
end Qrh.MarkedAnchor.High
