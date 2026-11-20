/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early mesh and finite metadata for actual independent-pair source calls. -/
import Candidate.C092.transport.StrongPairLowMetadata
import Candidate.C092.transport.LowActualBankUniform

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

/-- Genuine native fourth quotas at every active continuation cap, with
an explicit whole-slot collar. No source outside its true cap is used. -/
theorem native_mean_pair_quotas {N Y l : ℝ}
    (hNlo : (7/20:ℝ) ≤ N) (hYlo : (7/20:ℝ) ≤ Y)
    (hN : N < 1/2) (hY : Y < 1/2) (hl0 : 0 ≤ l) (hlmean : l < (1-N-Y)/2) :
    ∃ q₁ q₂ mesh : ℝ,0 < mesh ∧ 0 ≤ q₁ ∧ q₁ < 3/20 ∧ q₁ < (1-2*N)/2 ∧
      0 ≤ q₂ ∧ q₂ < 3/20 ∧ q₂ < (1-2*Y)/2 ∧ l+mesh ≤ (q₁+q₂)/2 := by
  let gap : ℝ := (1-N-Y)/2-l
  let debit : ℝ := min (gap/2) (min ((1-2*N)/4) ((1-2*Y)/4))
  have hg : 0 < gap := by dsimp [gap]; linarith
  have hd : 0 < debit := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hdg : debit ≤ gap/2 := min_le_left _ _
  have hdN : debit ≤ (1-2*N)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdY : debit ≤ (1-2*Y)/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨(1-2*N)/2-debit,(1-2*Y)/2-debit,gap/4,by positivity,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [gap] at *
  all_goals linarith

/-- The genuine near-unit native mean source for an independent pair.
Its two fourths split the actual whole slots with their true native quotas. -/
theorem native_mean_pair_box (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {N Y l : ℝ} (hNlo : (7/20:ℝ) ≤ N) (hYlo : (7/20:ℝ) ≤ Y)
    (hN : N < 1/2) (hY : Y < 1/2) (hl0 : 0 ≤ l) (hlmean : l < (1-N-Y)/2) :
    PairUniformBox N Y l := by

  obtain ⟨q₁,q₂,ms,hms,hq₁,hcap₁,hmean₁,hq₂,hcap₂,hmean₂,hbudget⟩ :=
    native_mean_pair_quotas hNlo hYlo hN hY hl0 hlmean
  have hbox₁ := QRH.Cycle092.LowActual.native_mean_box hβ hN.le hN.le hq₁ hcap₁ (by linarith : q₁ < (1-N-N)/2)
  have hbox₂ := QRH.Cycle092.LowActual.native_mean_box hβ hY.le hY.le hq₂ hcap₂ (by linarith : q₂ < (1-Y-Y)/2)
  intro ε hε
  obtain ⟨m₁,hm₁,hsource₁⟩ := hbox₁ ε hε
  obtain ⟨m₂,hm₂,hsource₂⟩ := hbox₂ ε hε
  let mesh := min ms (min m₁ m₂)
  have hm : 0 < mesh := lt_min hms (lt_min hm₁ hm₂)
  have hms' : mesh ≤ ms := min_le_left _ _
  have hm₁' : mesh ≤ m₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hm₂' : mesh ≤ m₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨d₁,S₁,C₁,hC₁,hs₁⟩ := hsource₁ (Fin 2×Slot) rayM Hr hHr W hW hWs bΦ hbΦ
    η₁ η₀₁ Q₁ hQ₁ray hQ₁0 hQ₁top hQ₁72
  obtain ⟨d₂,S₂,C₂,hC₂,hs₂⟩ := hsource₂ (Fin 2×Slot) rayM Hr hHr W hW hWs bΦ hbΦ
    η₂ η₀₂ Q₂ hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨max d₁ d₂,S₁∪S₂,C₁+C₂+1,by positivity,?_⟩
  filter_upwards [hs₁,hs₂,eventually_gt_atTop (1:ℝ)] with Z hs₁ hs₂ hZ
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hmark₁ hmark₂
  obtain ⟨F,hFT,hF,hrest⟩ := partition_selected T w hms.le hq₁ hq₂ hw (fun i=>(hwm i).trans hms') hsum hbudget
  exact native_pair_at rayM Hr hHr (labelled_mesh_mono rayM Hr hHr hm₁' hs₁)
    (labelled_mesh_mono rayM Hr hHr hm₂' hs₂) hC₁.le hC₂.le T F hFT θ₁ θ₂ w σ₁ σ₂ v₁ v₂
    t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hΦs p X₁ X₂ hX₁ hX₂
    hZ hXN hXY hF hrest s mark hk₁ hk₂ hy (fun u hu i hi=>hmark₁ u hu i (hFT hi))
    (fun u hu i hi=>hmark₂ u hu i (Finset.mem_sdiff.mp hi).1)

#print axioms native_mean_pair_box
end
end QRH.Cycle092.StrongPair
