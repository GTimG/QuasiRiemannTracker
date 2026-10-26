/- Actual all-row masks and seed gates, before continuation/source choice.
Copyright (c) 2026 Zhongpai Gao. Native source caps by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedForest
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open ActualEisensteinCubic CompletedGauss CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonProfile RayFourExpansion CenteredMomentLogDyadic
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentFirstCanonicalFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState Cycle153RegionalLow

/-- The original native source-cap producer supplies the puncture, norm,
support and seed gates for EVERY literal selected row. This includes
rows which later take zero, direct, reflected or OLD branches. The
threshold precedes all inputs and labels; no continued child, energy,
recursive output, or separately postulated mask estimate is an input. -/
theorem eventual_actual_selected_all_row_masks (budget : ℕ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ {alpha : Type} [Fintype alpha] [DecidableEq alpha]
      (reflected second : Bool) (s : Input alpha) (R seed : Ideal O)
      (Mrow amp xi reserve firstHeight Rc : ℝ) (hZ : 1 < Z),
      Fintype.card alpha ≤ budget → Endpoints (9/4) (9/4) (9/4) s →
      Squarefree seed → R ≠ 0 → Rc ≤ 20 → (R.absNorm : ℝ) ≤ Z^Rc →
    ∀ (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0),
      sourceRadius s ≤ Z^(3:ℝ) → volume s ≤ Z^(3:ℝ) →
    ∀ (bin : ℤ×(Fin 5→ℤ)) {Label : Type} [Fintype Label]
      (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      (∀ l, frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        R s.ν s.W s.P ≠ 0) →
    ∀ r : NativeLowRows reflected s R seed Z Mrow amp xi reserve (9/4)
      firstHeight (Fintype.card alpha) hZ bin hz1 hz2 firstIndex,
    let datum := geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve (9/4)
      firstHeight (Fintype.card alpha) hZ bin (firstIndex r.val.1) hz1 hz2 r.val.2
    let E := if second then datum.D else datum.C
    let other := if second then datum.C else datum.D
    datum.R*E ≠ 0 ∧ ((datum.R*E).absNorm : ℝ) ≤ Z^(Rc+8) ∧
      ((datum.R*E).absNorm : ℝ) ≤ Z^(28:ℝ) ∧
      Supported other ∧ datum.seed ∣ other ∧ Supported E ∧ datum.seed ∣ E := by
  have hc := eventual_actual_geometry_main_high_source_caps budget (9/4) (9/4) (1:ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hc] with Z hz
  refine ⟨hz.1, ?_⟩
  intro alpha _ _ reflected second s R seed Mrow amp xi reserve firstHeight Rc hZ
    hcard hend hseed hR hRc hRcap hz1 hz2 hsource hvolume bin Label _ firstIndex hf r datum E other
  let original := mainLowSelectedOriginal reflected s R seed Z Mrow amp xi reserve (9/4)
    firstHeight (Fintype.card alpha) hZ bin hz1 hz2 firstIndex r
  have hnorms := hz.2 reflected s R seed Mrow amp xi reserve firstHeight hZ
    hcard hend hseed hz1 hz2 hsource hvolume bin 1 1 1 original.val (hf r.val.1)
  have hP : datum.R*E ≠ 0 :=
    actual_geometry_low_second_puncture reflected s R seed Z Mrow amp xi reserve (9/4)
      firstHeight (Fintype.card alpha) hZ bin (firstIndex r.val.1) hz1 hz2 r.val.2 hR second
  have hcolumn : ((geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin
      (firstIndex r.val.1).1.val).absNorm : ℝ) ≤ Z^(4:ℝ) := by
    cases reflected
    · exact hnorms.1
    · exact hnorms.2.1
  have hr : (datum.R.absNorm : ℝ) ≤ Z^(Rc+4) := by
    change ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin
      (firstIndex r.val.1).1.val).absNorm : ℝ) ≤ _
    rw [map_mul, Nat.cast_mul]
    calc
      _ ≤ Z^Rc*Z^(4:ℝ) := mul_le_mul hRcap hcolumn (Nat.cast_nonneg _)
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _ = Z^(Rc+4) := by rw [←Real.rpow_add (zero_lt_one.trans hZ)]
  have hPNc : ((datum.R*E).absNorm : ℝ) ≤ Z^(Rc+8) := by
    have he : (E.absNorm : ℝ) ≤ Z^(4:ℝ) := by
      cases second
      · exact hnorms.2.2.1
      · exact hnorms.2.2.2
    rw [map_mul, Nat.cast_mul]
    calc
      _ ≤ Z^(Rc+4)*Z^(4:ℝ) := mul_le_mul hr he (Nat.cast_nonneg _)
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _ = Z^(Rc+8) := by
        rw [←Real.rpow_add (zero_lt_one.trans hZ)]
        congr 1
        ring
  have hPN : ((datum.R*E).absNorm : ℝ) ≤ Z^(28:ℝ) :=
    hPNc.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hRc]))
  have hseedGates := actual_main_high_seed_gates reflected s R seed Z Mrow amp xi reserve
    (9/4) firstHeight (Fintype.card alpha) hZ bin hz1 hz2 1 1 1 original.val
  refine ⟨hP, hPNc, hPN, ?_, ?_, ?_, ?_⟩
  · cases second
    · exact datum.hD
    · exact datum.hC
  · cases second
    · exact hseedGates.2
    · exact hseedGates.1
  · cases second
    · exact datum.hC
    · exact datum.hD
  · cases second
    · exact hseedGates.1
    · exact hseedGates.2

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.eventual_actual_selected_all_row_masks
