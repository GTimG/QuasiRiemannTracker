/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual marked plain Markov count with earlier ordinary capacity and width cap.
Generalized from Record12518109Gain.FiberPrimitives, whose original PR63
attribution is retained by the imported source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.FiberPrimitives

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Set
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open Record12518109GainFiber

theorem ordinary_plain_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (mesh binWidth z B lam h εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (Q u s)=g s)
    (hlam : 0≤lam) (hwidth : z≤h) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hcap : 2*Real.logb U ((2 : ℝ)^K.val)+lam*z≤B)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      (∑s∈selected,widths s)≤h →
      2*Real.logb U ((2 : ℝ)^K.val)+lam*(∑ s∈selected,widths s)≤B →
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
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_common_product rows hne slots
    Q widths g U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hcap' : 2*m+lam*(∑ s∈selected,widths s)≤B := by
    have hh := mul_le_mul_of_nonneg_left hlen hlam
    dsimp [m]
    linarith
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,Q u s) hDp (by norm_num)
    positiveAnnular_support hE height hheight hfreq (hraw selected hsub (hlen.trans hwidth) hcap')
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
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.ordinary_plain_fiber_count
