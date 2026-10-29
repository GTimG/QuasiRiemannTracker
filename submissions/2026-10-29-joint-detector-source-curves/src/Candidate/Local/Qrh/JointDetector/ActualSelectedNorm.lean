/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.ActualSlotData
import Candidate.Local.Qrh.JointDetector.NaturalSelectedNormContract

/-! The original all-source operator inlet follows from the aggregate
natural-row norm. The actual original slots, natural roots and early mesh
are supplied by the proved concrete factory. No zero-count estimate enters. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentEnergyState
local notation "O" => ActualEisensteinCubic.O

/-- Preserve the early mesh and all original dictionary/state/height
quantifiers while replacing the aggregate norm by the literal operator inlet. -/
theorem actualSelectedSlotNorm_of_aggregate (hagg : NaturalAggregateSlotNorm) :
    NaturalCount.ActualSelectedSlotNorm := by
  intro Mmin Mcap smin loss P_requested hMmin hMc hsmin hloss hPreq
  let A : ℝ := Mcap+1
  let P : ℝ := detectorAuxiliarySourceCap P_requested A
  have hMcap : 0 < Mcap := hMmin.trans_le hMc
  have hA : 0 < A := by dsimp [A]; linarith
  have hP : 3*A+1 ≤ P := by
    dsimp [P,detectorAuxiliarySourceCap]
    simpa only [add_comm] using add_le_add_right (le_max_right P_requested (3*A)) (1:ℝ)
  obtain ⟨mesh₀,hm₀,haggregate⟩ := hagg A P loss hA hP hloss
  refine ⟨mesh₀,hm₀,?_⟩
  intro mesh hm α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨Cslot,hCslot,hslots⟩ := ActualSlotData.data_bounded W hW.continuous hWs
  obtain ⟨C,Z₀,hC,hbound⟩ := haggregate (Fintype.card α) Cslot smin hCslot hsmin
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop bΦ,
    eventually_gt_atTop (1:ℝ)] with Z hZZ₀ hΦZ hZ
  refine ⟨hZ,?_⟩
  intro j st hchar hpuncture hMlower hMupper T θ w σ v t height
    hw hwm hσlo hσhi hheight hv hs δ Y root cores hδ hYlo hYhi hcores
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hmpos : 0 ≤ mesh := by
    by_contra hh
    have hh' : mesh ≤ 0 := le_of_lt (lt_of_not_ge hh)
    have hs0 : (∑ k,w k) ≤ 0 := Finset.sum_nonpos (fun k _ => (hwm k).trans hh')
    linarith
  let d := ActualSlotData.data rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root
  have hd : d.Bounded Z mesh Cslot :=
    hslots α rayM H hH Z bΦ st η₀ T θ w σ v (fun _ => 0) t root mesh hZ hmpos hw hwm
      (fun k => ⟨hσlo k,hσhi k⟩)
  have hwidth : ∑ i,d.width i = ∑ k,w k :=
    ActualSlotData.data_width rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root
  have hresponse : ∀ u ∈ cores,Z^(δ*∑ i,d.width i) ≤ ∏ i,‖d.polynomial i u.val‖^2 := by
    intro u hu
    obtain ⟨hz,hprofile,hamp⟩ := (hcores u hu).2
    simpa only [d,ActualSlotData.data_width,ActualSlotData.data_mass] using hamp
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hZ.le (by positivity : 0 ≤ Mmin/20)).trans hYlo
  have hrow : st.rowWidth ≤ Mcap := by
    have hh : st.rowWidth ≤ st.width := by
      dsimp [NaturalState.width]
      linarith [st.character_nonneg]
    exact hh.trans hMupper
  have hYA : Y ≤ Z^A := by
    calc
      Y ≤ bΦ*Z^st.rowWidth := hYhi
      _ ≤ Z*Z^Mcap := mul_le_mul hΦZ
        (Real.rpow_le_rpow_of_exponent_le hZ.le hrow)
        (Real.rpow_nonneg hZpos.le _) hZpos.le
      _ = Z^(1:ℝ)*Z^Mcap := by rw [Real.rpow_one]
      _ = Z^(1+Mcap) := (Real.rpow_add hZpos _ _).symm
      _ = Z^A := by congr 1; dsimp [A]; ring
  refine ⟨mul_nonneg hC.le (Real.rpow_nonneg hZpos.le _),?_⟩
  intro X S hX hXP hS
  exact hbound Z mesh δ hZZ₀ hmpos hm hδ.1 hδ.2 d cores S Y X hd
    (by simpa only [hwidth] using hs) hresponse hY1 hYA (fun u hu => (hcores u hu).1)
    hX hXP hS

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.actualSelectedSlotNorm_of_aggregate
