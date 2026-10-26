/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.Geometry.PhysicalCoordinates
import Candidate.Research.RecursiveAffine.RegionalRoundedPosition
import Candidate.Research.RecursiveAffine.FixedStages

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Cycle153ReachableGeometry
noncomputable section
open Cycle153Geometry

/-- The inequalities actually seen before the indicated finite depth.
Future active-child inequalities are deliberately absent. Unused future
coordinates are zero-filled by the physical history constructor. -/
def PrefixRows (depth : ℕ) (x : Fin 14 → ℝ) : Prop :=
  ∀ i : Fin 48, i.val < 7*(depth+1) ∨ 35 ≤ i.val →
    -(1/1000000000000000 : ℝ) ≤ Coordinates.rows i x

def gateDepth (i : Fin 62) : ℕ :=
  if i.val < 16 then 1 else if i.val < 32 then 2 else if i.val < 48 then 3 else 4

/-- Every fixed dual uses only the physical prefix available at its depth. -/
theorem gate_prefix (i : Fin 62) :
    ∀ k, ((gates i).selected k).val < 7*(gateDepth i+1) ∨
      35 ≤ ((gates i).selected k).val := by
  fin_cases i
  all_goals simp only [gateDepth]
  all_goals norm_num only [Nat.reduceLT, ite_true, ite_false, Nat.reduceAdd, Nat.reduceMul]
  exact Certificate00.prefix_admissible
  exact Certificate01.prefix_admissible
  exact Certificate02.prefix_admissible
  exact Certificate03.prefix_admissible
  exact Certificate04.prefix_admissible
  exact Certificate05.prefix_admissible
  exact Certificate06.prefix_admissible
  exact Certificate07.prefix_admissible
  exact Certificate08.prefix_admissible
  exact Certificate09.prefix_admissible
  exact Certificate10.prefix_admissible
  exact Certificate11.prefix_admissible
  exact Certificate12.prefix_admissible
  exact Certificate13.prefix_admissible
  exact Certificate14.prefix_admissible
  exact Certificate15.prefix_admissible
  exact Certificate16.prefix_admissible
  exact Certificate17.prefix_admissible
  exact Certificate18.prefix_admissible
  exact Certificate19.prefix_admissible
  exact Certificate20.prefix_admissible
  exact Certificate21.prefix_admissible
  exact Certificate22.prefix_admissible
  exact Certificate23.prefix_admissible
  exact Certificate24.prefix_admissible
  exact Certificate25.prefix_admissible
  exact Certificate26.prefix_admissible
  exact Certificate27.prefix_admissible
  exact Certificate28.prefix_admissible
  exact Certificate29.prefix_admissible
  exact Certificate30.prefix_admissible
  exact Certificate31.prefix_admissible
  exact Certificate32.prefix_admissible
  exact Certificate33.prefix_admissible
  exact Certificate34.prefix_admissible
  exact Certificate35.prefix_admissible
  exact Certificate36.prefix_admissible
  exact Certificate37.prefix_admissible
  exact Certificate38.prefix_admissible
  exact Certificate39.prefix_admissible
  exact Certificate40.prefix_admissible
  exact Certificate41.prefix_admissible
  exact Certificate42.prefix_admissible
  exact Certificate43.prefix_admissible
  exact Certificate44.prefix_admissible
  exact Certificate45.prefix_admissible
  exact Certificate46.prefix_admissible
  exact Certificate47.prefix_admissible
  exact Certificate48.prefix_admissible
  exact Certificate49.prefix_admissible
  exact Certificate50.prefix_admissible
  exact Certificate51.prefix_admissible
  exact Certificate52.prefix_admissible
  exact Certificate53.prefix_admissible
  exact Certificate54.prefix_admissible
  exact Certificate55.prefix_admissible
  exact Certificate56.prefix_admissible
  exact Certificate57.prefix_admissible
  exact Certificate58.prefix_admissible
  exact Certificate59.prefix_admissible
  exact Certificate60.prefix_admissible
  exact Certificate61.prefix_admissible

theorem PrefixRows.mono {j k : ℕ} {x : Fin 14 → ℝ}
    (h : PrefixRows k x) (hjk : j ≤ k) : PrefixRows j x := by
  intro i hi
  apply h i
  rcases hi with hi | hi
  · exact Or.inl (by omega)
  · exact Or.inr hi

/-- Apply a numerical certificate only after the corresponding physical
prefix has been constructed. No inequalities on future daughters enter. -/
theorem prefix_gate {j : ℕ} {x : Fin 14 → ℝ}
    (h : PrefixRows j x) (i : Fin 62) (hij : gateDepth i ≤ j) :
    (1568511/1000000000000000 : ℝ) < Coordinates.objectives i x := by
  apply robust_for_physical_coordinates i x (1/1000000000000000) le_rfl
  intro k
  apply (h.mono hij) ((gates i).selected k)
  exact gate_prefix i k

/-- Failure of both genuine reflected old-region branches forces the
balanced plain window used by the next regional ledger. The two short
side gates are elementary length tests, not moment assumptions. -/
theorem no_reflection_balanced
    {n₁ n₂ U slots delta xi : ℝ}
    (h₁ : n₁+slots+delta ≤ U) (h₂ : n₂+slots+delta ≤ U)
    (hnot : ¬(max 0 (U-n₂+xi)+n₁+slots+delta ≤ U ∨
      max 0 (U-n₁+xi)+n₂+slots+delta ≤ U)) :
    |n₁-n₂| ≤ slots+delta+xi := by
  have hn₁ : U < max 0 (U-n₂+xi)+n₁+slots+delta :=
    lt_of_not_ge (fun h => hnot (Or.inl h))
  have hn₂ : U < max 0 (U-n₁+xi)+n₂+slots+delta :=
    lt_of_not_ge (fun h => hnot (Or.inr h))
  have hp₁ : 0 ≤ U-n₂+xi := by
    by_contra h
    rw [max_eq_left (le_of_not_ge h)] at hn₁
    linarith only [h₁,hn₁]
  have hp₂ : 0 ≤ U-n₁+xi := by
    by_contra h
    rw [max_eq_left (le_of_not_ge h)] at hn₂
    linarith only [h₂,hn₂]
  rw [max_eq_right hp₁] at hn₁
  rw [max_eq_right hp₂] at hn₂
  exact abs_le.mpr ⟨by linarith only [hn₁], by linarith only [hn₂]⟩

/-- The literal .397 continuation cutoff pays the reflected branch's
.0038 margin and .0001 slack in the NEXT unit. -/
theorem reflected_slack_next_unit {parent child : ℝ}
    (hparent : 0 ≤ parent) (hchild : (397/1000:ℝ)*parent ≤ child) :
    (19/5000:ℝ)*parent+(1/10000:ℝ)*parent ≤ child/100 := by
  linarith only [hparent,hchild]

theorem actual_unreflected_balance
    {n₁ n₂ parent child slots : ℝ}
    (hparent : 0 ≤ parent) (hchild : (397/1000:ℝ)*parent ≤ child)
    (h₁ : n₁+slots+(19/5000:ℝ)*parent ≤ child)
    (h₂ : n₂+slots+(19/5000:ℝ)*parent ≤ child)
    (hnot : ¬(max 0 (child-n₂+(1/10000:ℝ)*parent)+n₁+slots+
        (19/5000:ℝ)*parent ≤ child ∨
      max 0 (child-n₁+(1/10000:ℝ)*parent)+n₂+slots+
        (19/5000:ℝ)*parent ≤ child)) :
    |n₁-n₂| ≤ slots+child/100 := by
  have hb := no_reflection_balanced h₁ h₂ hnot
  have hs := reflected_slack_next_unit hparent hchild
  linarith only [hb,hs]

end
end OAI.SevenEighths.Cycle153ReachableGeometry
#print axioms OAI.SevenEighths.Cycle153ReachableGeometry.prefix_gate
#print axioms OAI.SevenEighths.Cycle153ReachableGeometry.actual_unreflected_balance
