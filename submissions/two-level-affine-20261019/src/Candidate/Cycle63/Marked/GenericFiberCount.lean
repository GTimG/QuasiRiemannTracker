import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPlainFiberCount

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.Cycle63MarkedFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount

/-- A common amplitude family may include a rowwise height or fixed ray twist.
Only the common bins and supplied marked moments enter the counting argument. -/
theorem select_common_product {Row Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (slots : Finset Slot)
    (Q : Row→Slot→ℂ) (w g : Slot→ℝ) (U δ mesh binWidth z : ℝ)
    (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<w s) (hwm : ∀ s∈slots,w s≤ mesh)
    (hL : 0<∑ s∈slots,w s) (hz : 0≤z) (hzL : z≤∑ s∈slots,w s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(w s)) (δ/2) binWidth (Q u s)=g s) :
    ∃ selected : Finset Slot,selected⊆slots ∧ (∀ s∈selected,0<g s) ∧
      (∑ s∈selected,w s)≤z ∧
      ∀ u∈rows,U^(2*weightedMean slots w g*z-δ*mesh)≤‖∏ s∈selected,Q u s‖^2 := by
  obtain ⟨u0,hu0⟩ := hne
  have hg (s : Slot) (hs : s∈slots) : 0≤g s ∧ g s≤δ/2 := by
    rw [←hbins u0 hu0 s hs]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ (fun s hs=>(hw s hs).le) hL hg
  have hm : weightedMean slots w g*(∑ s∈slots,w s)≤∑ s∈slots,w s*g s := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := HeckePrimeAmplitudeBins.common_bin_selection
    slots w g U δ mesh binWidth (weightedMean slots w g) z hU hδ hmesh hbin
    hw hwm hg hq hqδ hz hzL hm
  exact ⟨selected,hsub,hpositive,hlen,fun u hu=>hspike (Q u) (hbins u hu)⟩

theorem inverse_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→ Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (mesh binWidth z εm C height : ℝ) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤ mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (Q u s)=g s)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hcap1 : Real.logb U ((2 : ℝ)^J.val)+2*z<1)
    (hcap2 : 2*Real.logb U ((2 : ℝ)^J.val)+8*z<3)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      Real.logb U ((2 : ℝ)^J.val)+2*(∑ s∈selected,widths s)<1 →
      2*Real.logb U ((2 : ℝ)^J.val)+8*(∑ s∈selected,widths s)<3 →
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
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_common_product rows hne slots
    Q widths g U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hcap1' : r+2*(∑ s∈selected,widths s)<1 := by dsimp [r]; linarith
  have hcap2' : 2*r+8*(∑ s∈selected,widths s)<3 := by dsimp [r]; linarith
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.inverse_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label (inverseTest U tstar r) (U^r) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,Q u s) hDp (by norm_num)
    (HeckeDetectorDyadicActual.inverse_profile_support _ _) hE height hheight hfreq
    (hraw selected hsub hcap1' hcap2')
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

theorem plain_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→ Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (mesh binWidth z κplain εm C height : ℝ) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤ mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (Q u s)=g s)
    (hκ : 0≤κplain) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hcap : 2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*z≤1)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*(∑ s∈selected,widths s)≤1 →
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
  have hcap' : 2*m+6*κplain*(∑ s∈selected,widths s)≤1 := by
    have hh := mul_le_mul_of_nonneg_left hlen (show 0≤6*κplain by positivity)
    dsimp [m]
    linarith
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,Q u s) hDp (by norm_num)
    positiveAnnular_support hE height hheight hfreq (hraw selected hsub hcap')
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

end SevenEighths.Cycle63MarkedFiber
end
end OAI
