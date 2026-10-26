import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.ChildBranchFacts
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.SecondLevelPosition
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelBridge
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The arithmetic conditions of the second step for a first-level LOW child of the unit width that is not in the old
region and not reflected into it. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open Cycle63 Cycle63.Optimization

/-- A first-level LOW child of the cell `b`, of the nominal width `ν`, widened by `δ`, with plain lengths `x₁, x₂`
and the slot length `z'` left by the fixed deletion, has the arithmetic conditions of the second step, with the total
length `lengthL` and the amplifier `ampL` of the parent of the second step. The child has the capacities of its
extraction: `x₁ + x₂ + 6 κ rem - ν` is at most the gap over the old region, six amplifiers and the padding `pad`, less
the extraction credit `Red`; and `x₁ + x₂ + rem` is at most the bound of the total length of the cell and the padding,
less the width reduction `v` and `Red`. It is not in the old region and not reflected into it (the plain lengths
differ by at most `6 κ z' + ξ + δR`), where `ξ + δR` is at most a hundredth of the least width of the second step.
Its capacity exceeds its unit by at most the overshoot `childOvershoot b` of the zero-extraction child of the cell and
the padding `pad`, which is at most `7/2500` (`hcO`). -/
theorem second_step_arithmetic_of_child {b ν δ x₁ x₂ z' rem pad omega ξ δR v Red lossFloor lengthL ampL : ℝ}
    (G : ℕ) (hG : 1000000 ≤ G)
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop)
    (hW2 : secondStepWidthFloor ≤ ν + δ) (hWu : ν + δ ≤ 1) (hδ : 0 ≤ δ)
    (hpad : 0 ≤ pad) (homega : 0 ≤ omega) (hmt : 0 ≤ (twoLevelSlope - 1) * cellMesh)
    (hz' : 0 ≤ z') (hrem : rem ≤ b) (hz'le : z' ≤ rem - fixedDeletion b)
    (hv : 0 ≤ v) (hRed : 0 ≤ Red) (hνdef : ν = 1 - v - 6 * firstAmp b - omega)
    (hN4 : x₁ + x₂ + 6 * slotPrice * rem - ν ≤ twoLevelOldGap b + 6 * firstAmp b + pad - Red)
    (hN4u : x₁ + x₂ + rem ≤ twoLevelTotalA b + pad - (v + Red))
    (hnotO : ν + δ < x₁ + x₂ + 6 * slotPrice * z')
    (hbal : |x₁ - x₂| ≤ 6 * slotPrice * z' + (ξ + δR))
    (hsmall : ξ + δR ≤ 1 / 100 * (2 / 5))
    (hsmallω : pad + omega + (twoLevelSlope - 1) * cellMesh ≤ 1 / 1000000)
    (hlen : x₁ + x₂ + z' + secondSlope / G ≤ lengthL)
    (hampL : secondAmp b + amplifierRatio slotPrice 1 secondJunction * (pad + omega) +
        amplifierRatio slotPrice 1 secondJunction * (1 + 6 * slotPrice) / G ≤ ampL)
    (hcO : childOvershoot b + pad ≤ 7 / 2500) :
    SecondStepArithmetic G lossFloor (ν + δ) x₁ x₂ z' (ν + δ) lengthL ampL lossFloor := by
  have hκ := slotPrice_bounds
  have hlam := secondSlope_bounds
  have hI := twoLevelIntercept_bounds
  have hK := secondAmplifierRatio_bounds
  have hW2' : 2 / 5 ≤ ν + δ := hW2
  have hG0 : (0 : ℝ) < G := by
    have : (1000000 : ℝ) ≤ G := by exact_mod_cast hG
    linarith
  have hg : (0 : ℝ) < 1 / G := by positivity
  have hg' : 1 / (G : ℝ) ≤ 1 / 1000000 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast hG
  have hWpos : 0 < ν + δ := by linarith
  have hWne : ν + δ ≠ 0 := hWpos.ne'
  have hfacts := child_branch_facts (κ := slotPrice) (lam₂ := secondSlope) (I := twoLevelIntercept) (b := b)
    (d0 := fixedDeletion b) (gN := twoLevelOldGap b) (ampN := firstAmp b) (totN := twoLevelTotalA b)
    (cO := childOvershoot b) (cR := childReserve b) (u := 1) (ν := ν) (W := ν + δ) (x₁ := x₁) (x₂ := x₂)
    (z' := z') (rem := rem) (del := fixedDeletion b) (pad := pad) (omega := omega) (ξ := ξ) (δR := δR) (v := v)
    (Red := Red) (mt := (twoLevelSlope - 1) * cellMesh) one_pos (by linarith) hWu (by linarith)
    (by linarith [hκ.1]) (by linarith [hlam.1]) (by linarith [hI.1]) (by linarith [hI.2]) hpad homega hmt hz'
    (childOvershoot_eq b) rfl (fixedDeletion_boundary b) (one_mul _).symm (by simpa using hrem) hz'le hv hRed
    (by simpa using hνdef) (by simpa using hN4) (by simpa using hN4u) hnotO hbal (by simpa using hsmall)
    (by simpa using hsmallω)
  have hfacts' : (childPosition (1 / (G : ℝ)) (x₁ / (ν + δ)) (x₂ / (ν + δ)) (z' / (ν + δ))).Facts := by
    have hω0 := hfacts.omega
    refine childPosition_facts (b := b) (M₁ := (ν + δ) / 1)
      (ω := (pad + omega) / 1 + (twoLevelSlope - 1) * cellMesh) (s := (ξ + δR) / (ν + δ)) hb hfacts.width hg hg'
      hfacts.slack hω0.1 hω0.2 hfacts.slot_nonneg hfacts.slot_cell hfacts.overshoot_pos hfacts.overshoot_le
      hfacts.reserve hfacts.balance hfacts.region
  refine ⟨rfl, hW2, hfacts', ?_, ?_, le_rfl, ?_⟩
  · -- the total length
    have h1 := childPosition_totalA_le (g := 1 / (G : ℝ)) (n₁ := x₁ / (ν + δ)) (n₂ := x₂ / (ν + δ))
      (ζ := z' / (ν + δ)) hg
    have h2 : (ν + δ) * (x₁ / (ν + δ) + x₂ / (ν + δ) + z' / (ν + δ) + secondSlope * (1 / G)) =
        x₁ + x₂ + z' + (ν + δ) * (secondSlope / G) := by
      field_simp
    have h3 : (ν + δ) * (secondSlope / G) ≤ secondSlope / G := by
      have : 0 ≤ secondSlope / (G : ℝ) := div_nonneg (by linarith [hlam.1]) hG0.le
      exact mul_le_of_le_one_left this hWu
    have h4 := mul_le_mul_of_nonneg_left h1 hWpos.le
    rw [h2] at h4
    linarith only [h4, h3, hlen]
  · -- the amplifier
    have h1 := childPosition_amp_le (g := 1 / (G : ℝ)) (n₁ := x₁ / (ν + δ)) (n₂ := x₂ / (ν + δ))
      (ζ := z' / (ν + δ)) hg
    set K := amplifierRatio slotPrice 1 secondJunction with hKdef
    have hK0 : 0 ≤ K := by linarith [hK.1]
    have hover : (x₁ / (ν + δ) + x₂ / (ν + δ) + 6 * slotPrice * (z' / (ν + δ)) - 1) * (ν + δ) ≤
        childOvershoot b + (pad + omega) := by
      simpa using child_overshoot_nomesh (κ := slotPrice) (cO := childOvershoot b) (gN := twoLevelOldGap b)
        (ampN := firstAmp b) (d0 := fixedDeletion b) (u := 1) (ν := ν) (W := ν + δ) (x₁ := x₁) (x₂ := x₂)
        (z' := z') (rem := rem) (del := fixedDeletion b) (pad := pad) (omega := omega) (Red := Red) one_pos hWpos
        (by linarith [hκ.1]) (childOvershoot_eq b) (one_mul _).symm (by simpa using hz'le) (by linarith) hRed
        homega (by simpa using hN4)
    have hα : 0 ≤ lowReserveWeight := by unfold lowReserveWeight allowanceUnit; norm_num
    have hα1 : (ν + δ) * lowReserveWeight ≤ lowReserveWeight := mul_le_of_le_one_left hα hWu
    have hgs : (ν + δ) * (K * ((1 + 6 * slotPrice) * (1 / G))) ≤ K * (1 + 6 * slotPrice) / G := by
      have h0 : 0 ≤ K * ((1 + 6 * slotPrice) * (1 / (G : ℝ))) := by
        have : 0 ≤ 1 + 6 * slotPrice := by linarith [hκ.1]
        positivity
      have h2 : K * ((1 + 6 * slotPrice) * (1 / (G : ℝ))) = K * (1 + 6 * slotPrice) / G := by
        field_simp
      rw [← h2]
      exact mul_le_of_le_one_left h0 hWu
    have hK1 := mul_le_mul_of_nonneg_left hover hK0
    have h5 := mul_le_mul_of_nonneg_left h1 hWpos.le
    have h6 : (ν + δ) * (K * (x₁ / (ν + δ) + x₂ / (ν + δ) + 6 * slotPrice * (z' / (ν + δ)) - 1 +
        (1 + 6 * slotPrice) * (1 / G)) + lowReserveWeight) =
        K * ((x₁ / (ν + δ) + x₂ / (ν + δ) + 6 * slotPrice * (z' / (ν + δ)) - 1) * (ν + δ)) +
          (ν + δ) * (K * ((1 + 6 * slotPrice) * (1 / G))) + (ν + δ) * lowReserveWeight := by
      ring
    rw [h6] at h5
    have h7 : secondAmp b = K * childOvershoot b + lowReserveWeight := rfl
    have h8 : K * (childOvershoot b + (pad + omega)) = K * childOvershoot b + K * (pad + omega) := by ring
    linarith only [h5, hK1, hα1, hgs, hampL, h7, h8]
  · -- the overshoot over the old region
    have h6 : 6 * slotPrice * z' ≤ 6 * slotPrice * (rem - fixedDeletion b) :=
      mul_le_mul_of_nonneg_left hz'le (by linarith [hκ.1])
    have hcOdef := childOvershoot_eq b
    linarith only [hN4, h6, hcOdef, hcO, hRed, hδ]

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
