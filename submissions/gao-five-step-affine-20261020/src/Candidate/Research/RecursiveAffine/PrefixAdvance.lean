/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableGeometry

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OAI.SevenEighths.Cycle153ReachableGeometry
noncomputable section
open Cycle153Geometry

/-- Append the actual next multiplier/reduction/slot-loss coordinates.
Every earlier physical coordinate is retained literally. -/
def extendCoordinates (x : Fin 14 → ℝ) (step : Fin 4) (V Red ell : ℝ) : Fin 14 → ℝ :=
  fun i => if i.val=step.val+1 then V else if i.val=step.val+5 then Red
    else if i.val=step.val+9 then ell else x i

/-- No branch condition on a future daughter is used to preserve the
already constructed physical prefix. -/
theorem earlier_rows_extend (x : Fin 14 → ℝ) (step : Fin 4) (V Red ell : ℝ)
    (i : Fin 48) (hi : i.val<7*(step.val+1)) :
    Coordinates.rows i (extendCoordinates x step V Red ell)=Coordinates.rows i x := by
  fin_cases step <;> fin_cases i <;> norm_num at hi
  all_goals simp [extendCoordinates,Coordinates.b, Coordinates.rootSlack, Coordinates.V0, Coordinates.Red0, Coordinates.ell0, Coordinates.V1, Coordinates.Red1, Coordinates.ell1, Coordinates.V2, Coordinates.Red2, Coordinates.ell2, Coordinates.V3, Coordinates.Red3, Coordinates.ell3, Coordinates.U0, Coordinates.A0, Coordinates.z0, Coordinates.capA0, Coordinates.gap0, Coordinates.a0, Coordinates.d0, Coordinates.U1, Coordinates.A1, Coordinates.z1, Coordinates.capA1, Coordinates.gap1, Coordinates.a1, Coordinates.d1, Coordinates.U2, Coordinates.A2, Coordinates.z2, Coordinates.capA2, Coordinates.gap2, Coordinates.a2, Coordinates.d2, Coordinates.U3, Coordinates.A3, Coordinates.z3, Coordinates.capA3, Coordinates.gap3, Coordinates.a3, Coordinates.d3, Coordinates.U4, Coordinates.A4, Coordinates.z4, Coordinates.capA4, Coordinates.gap4, Coordinates.a4, Coordinates.d4, Coordinates.row00, Coordinates.row01, Coordinates.row02, Coordinates.row03, Coordinates.row04, Coordinates.row05, Coordinates.row06, Coordinates.row07, Coordinates.row08, Coordinates.row09, Coordinates.row10, Coordinates.row11, Coordinates.row12, Coordinates.row13, Coordinates.row14, Coordinates.row15, Coordinates.row16, Coordinates.row17, Coordinates.row18, Coordinates.row19, Coordinates.row20, Coordinates.row21, Coordinates.row22, Coordinates.row23, Coordinates.row24, Coordinates.row25, Coordinates.row26, Coordinates.row27, Coordinates.row28, Coordinates.row29, Coordinates.row30, Coordinates.row31, Coordinates.row32, Coordinates.row33, Coordinates.row34, Coordinates.row35, Coordinates.row36, Coordinates.row37, Coordinates.row38, Coordinates.row39, Coordinates.row40, Coordinates.row41, Coordinates.row42, Coordinates.row43, Coordinates.row44, Coordinates.row45, Coordinates.row46, Coordinates.row47, Coordinates.rows]

/-- Updating a literal edge only replaces its own three variable rows;
every other variable bound is inherited from the already built prefix. -/
theorem variable_rows_extend (x : Fin 14 → ℝ) (step : Fin 4) (V Red ell E : ℝ)
    (hV : -E ≤ V) (hRed : -E ≤ Red) (hell : -E ≤ ell)
    (i : Fin 48) (hi : 35 ≤ i.val) (hold : -E ≤ Coordinates.rows i x) :
    -E ≤ Coordinates.rows i (extendCoordinates x step V Red ell) := by
  fin_cases step <;> fin_cases i <;> norm_num at hi
  all_goals simp_all [extendCoordinates, Coordinates.rows,
    Coordinates.row35,Coordinates.row36,Coordinates.row37,Coordinates.row38,
    Coordinates.row39,Coordinates.row40,Coordinates.row41,Coordinates.row42,
    Coordinates.row43,Coordinates.row44,Coordinates.row45,Coordinates.row46,Coordinates.row47,
    Coordinates.V0,Coordinates.V1,Coordinates.V2,Coordinates.V3,
    Coordinates.Red0,Coordinates.Red1,Coordinates.Red2,Coordinates.Red3,
    Coordinates.ell0,Coordinates.ell1,Coordinates.ell2,Coordinates.ell3,Coordinates.rootSlack]

/-- A continuing physical edge appends just its seven new scalar source
conditions. All previously paid constraints are preserved, and no future
active-node condition is requested. -/
theorem prefixRows_extend (x : Fin 14 → ℝ) (step : Fin 4) (V Red ell : ℝ)
    (hold : PrefixRows step.val x)
    (hV : -(1/1000000000000000:ℝ) ≤ V)
    (hRed : -(1/1000000000000000:ℝ) ≤ Red)
    (hell : -(1/1000000000000000:ℝ) ≤ ell)
    (hnew : ∀ i : Fin 48,7*(step.val+1) ≤ i.val → i.val<7*(step.val+2) →
      -(1/1000000000000000:ℝ) ≤ Coordinates.rows i (extendCoordinates x step V Red ell)) :
    PrefixRows (step.val+1) (extendCoordinates x step V Red ell) := by
  intro i hi
  by_cases hpast : i.val<7*(step.val+1)
  · rw [earlier_rows_extend x step V Red ell i hpast]
    exact hold i (Or.inl hpast)
  · rcases hi with hi | hi
    · exact hnew i (by omega) (by omega)
    · exact variable_rows_extend x step V Red ell (1/1000000000000000)
        hV hRed hell i hi (hold i (Or.inr hi))

end
end OAI.SevenEighths.Cycle153ReachableGeometry
#print axioms OAI.SevenEighths.Cycle153ReachableGeometry.earlier_rows_extend

#print axioms OAI.SevenEighths.Cycle153ReachableGeometry.prefixRows_extend
