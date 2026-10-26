/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualNodeCoordinates
import Candidate.Research.RecursiveAffine.PrefixAdvance

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open Cycle153Geometry Cycle153ReachableGeometry

def nextInner (j : Fin 4) (hj : j.val<3) : Fin 4 := ⟨j.val+1,by omega⟩

/-- The literal coordinate update has exactly the actual physical
width, capacity and surviving-slot recurrences. Past source data are
retained, not reselected or reconstructed from a bound. -/
theorem physical_next_models (j : Fin 4) (hj : j.val<3) (x : Fin 14 → ℝ)
    (V Red ell : ℝ) :
    let k := nextInner j hj
    let y := extendCoordinates x k V Red ell
    modelUnit k y=modelUnit j x-6*modelAmplification j x-V ∧
      modelLength k y=modelLength j x-pathDeletion j.val x-V-Red ∧
      modelSlots k y=modelSlots j x-pathDeletion j.val x-ell := by
  fin_cases j <;> norm_num at hj
  all_goals simp [nextInner,extendCoordinates,modelUnit,modelLength,modelSlots,
    modelAmplification,pathDeletion,pathStage,Coordinates.b, Coordinates.rootSlack, Coordinates.V0, Coordinates.V1, Coordinates.V2, Coordinates.V3, Coordinates.Red0, Coordinates.Red1, Coordinates.Red2, Coordinates.Red3, Coordinates.ell0, Coordinates.ell1, Coordinates.ell2, Coordinates.ell3, Coordinates.U0, Coordinates.U1, Coordinates.U2, Coordinates.U3, Coordinates.U4, Coordinates.A0, Coordinates.A1, Coordinates.A2, Coordinates.A3, Coordinates.A4, Coordinates.z0, Coordinates.z1, Coordinates.z2, Coordinates.z3, Coordinates.z4, Coordinates.capA0, Coordinates.capA1, Coordinates.capA2, Coordinates.capA3, Coordinates.capA4, Coordinates.gap0, Coordinates.gap1, Coordinates.gap2, Coordinates.gap3, Coordinates.gap4, Coordinates.a0, Coordinates.a1, Coordinates.a2, Coordinates.a3, Coordinates.a4, Coordinates.d0, Coordinates.d1, Coordinates.d2, Coordinates.d3, Coordinates.d4]

/-- Only this edge's new coordinate triple is appended. -/
theorem physical_next_prefix_preserved (j : Fin 4) (hj : j.val<3)
    (x : Fin 14 → ℝ) (V Red ell : ℝ) :
    ∀i,prefixCoordinate (j.val+1) i →
      extendCoordinates x (nextInner j hj) V Red ell i=x i := by
  intro i hi
  have h1 : i.val≠(nextInner j hj).val+1 := by
    dsimp only [prefixCoordinate,nextInner] at hi ⊢
    omega
  have h2 : i.val≠(nextInner j hj).val+5 := by
    dsimp only [prefixCoordinate,nextInner] at hi ⊢
    omega
  have h3 : i.val≠(nextInner j hj).val+9 := by
    dsimp only [prefixCoordinate,nextInner] at hi ⊢
    omega
  simp only [extendCoordinates,if_neg h1,if_neg h2,if_neg h3]

/-- Nonnegative physical reductions are an induction invariant. -/
theorem physical_next_nonnegative (x : Fin 14 → ℝ) (step : Fin 4)
    (V Red ell : ℝ)
    (hn : ∀i : Fin 48,35 ≤ i.val → 0 ≤ Coordinates.rows i x)
    (hV : 0 ≤ V) (hRed : 0 ≤ Red) (hell : 0 ≤ ell) :
    ∀i : Fin 48,35 ≤ i.val →
      0 ≤ Coordinates.rows i (extendCoordinates x step V Red ell) := by
  intro i hi
  simpa only [neg_zero] using
    variable_rows_extend x step V Red ell 0
      (by simpa only [neg_zero] using hV)
      (by simpa only [neg_zero] using hRed)
      (by simpa only [neg_zero] using hell) i hi
      (by simpa only [neg_zero] using hn i hi)

/-- The actual puncture-history sums gain precisely this same edge's
missing and reduction coordinates. -/
theorem physical_next_history (j : Fin 4) (hj : j.val<3) (x : Fin 14 → ℝ)
    (V Red ell : ℝ) :
    let k := nextInner j hj
    let y := extendCoordinates x k V Red ell
    modelMissing k y+modelReduction k y=modelMissing j x+modelReduction j x+V+Red := by
  fin_cases j <;> norm_num at hj
  all_goals simp [nextInner,extendCoordinates,modelMissing,modelReduction,
    Coordinates.historicalMissing1,Coordinates.historicalMissing2,Coordinates.historicalMissing3,
    Coordinates.historicalMissing4,Coordinates.historicalReduction1,Coordinates.historicalReduction2,
    Coordinates.historicalReduction3,Coordinates.historicalReduction4,
    Coordinates.V0,Coordinates.V1,Coordinates.V2,Coordinates.V3,
    Coordinates.Red0,Coordinates.Red1,Coordinates.Red2,Coordinates.Red3]
  all_goals ring

def sourceRowOffset : Fin 5 → ℕ := ![0,1,2,5,6]

def nextSourceRow (j : Fin 4) (hj : j.val<3) (r : Fin 5) : Fin 48 :=
  ⟨7*((nextInner j hj).val+1)+sourceRowOffset r,by
    have hr : sourceRowOffset r ≤ 6 := by fin_cases r <;> decide
    dsimp only [nextInner]
    omega⟩

/-- Exactly five new physical tests remain after positivity of the next
amplifier and unit have been proved. -/
theorem physical_next_source_rows (j : Fin 4) (hj : j.val<3)
    (x : Fin 14 → ℝ) (V Red ell : ℝ) :
    let k := nextInner j hj
    let y := extendCoordinates x k V Red ell
    ∀r : Fin 5,Coordinates.rows (nextSourceRow j hj r) y=
      ![V+Red-ell,modelUnit k y-Coordinates.mu*modelUnit j x,
        modelLength k y+(6*Coordinates.kappa-1)*modelSlots k y-modelUnit k y,
        modelLength k y-modelSlots k y,modelSlots k y] r := by
  fin_cases j <;> norm_num at hj
  all_goals intro k y r; fin_cases r
  all_goals simp [k,y,nextSourceRow,sourceRowOffset,nextInner,extendCoordinates,
    modelUnit,modelLength,modelSlots,Coordinates.b, Coordinates.rootSlack, Coordinates.V0, Coordinates.V1, Coordinates.V2, Coordinates.V3, Coordinates.Red0, Coordinates.Red1, Coordinates.Red2, Coordinates.Red3, Coordinates.ell0, Coordinates.ell1, Coordinates.ell2, Coordinates.ell3, Coordinates.U0, Coordinates.U1, Coordinates.U2, Coordinates.U3, Coordinates.U4, Coordinates.A0, Coordinates.A1, Coordinates.A2, Coordinates.A3, Coordinates.A4, Coordinates.z0, Coordinates.z1, Coordinates.z2, Coordinates.z3, Coordinates.z4, Coordinates.capA0, Coordinates.capA1, Coordinates.capA2, Coordinates.capA3, Coordinates.capA4, Coordinates.gap0, Coordinates.gap1, Coordinates.gap2, Coordinates.gap3, Coordinates.gap4, Coordinates.a0, Coordinates.a1, Coordinates.a2, Coordinates.a3, Coordinates.a4, Coordinates.d0, Coordinates.d1, Coordinates.d2, Coordinates.d3, Coordinates.d4, Coordinates.mu, Coordinates.row07, Coordinates.row08, Coordinates.row09, Coordinates.row10, Coordinates.row11, Coordinates.row12, Coordinates.row13, Coordinates.row14, Coordinates.row15, Coordinates.row16, Coordinates.row17, Coordinates.row18, Coordinates.row19, Coordinates.row20, Coordinates.row21, Coordinates.row22, Coordinates.row23, Coordinates.row24, Coordinates.row25, Coordinates.row26, Coordinates.row27, Coordinates.row28, Coordinates.row29, Coordinates.row30, Coordinates.row31, Coordinates.row32, Coordinates.row33, Coordinates.row34, Coordinates.rows]

/-- The true width/old-region/source-capacity tests complete the next
raw prefix. All earlier rows and exact physical signs are inherited. -/
theorem raw_prefix_of_physical_step (j : Fin 4) (hj : j.val<3)
    (x : Fin 14 → ℝ) (V Red ell : ℝ)
    (hprefix : PrefixRows (j.val+1) x)
    (hphysical : ∀i : Fin 48,35 ≤ i.val → 0 ≤ Coordinates.rows i x)
    (hV : 0 ≤ V) (hRed : 0 ≤ Red) (hell : 0 ≤ ell)
    (hpaid : -(1/1000000000000000:ℝ) ≤ V+Red-ell)
    (hwide : Coordinates.mu*modelUnit j x ≤
      modelUnit (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell))
    (hactive : 0 < modelLength (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)+
      (6*Coordinates.kappa-1)*modelSlots (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)-
      modelUnit (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell))
    (hplain : 0 ≤ modelLength (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)-
      modelSlots (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell))
    (hslots : 0 ≤ modelSlots (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)) :
    RawPrefixRows (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell) := by
  let k := nextInner j hj
  let y := extendCoordinates x k V Red ell
  intro i hi hna hnu
  by_cases hpast : i.val<7*(k.val+1)
  · rw [earlier_rows_extend x k V Red ell i hpast]
    apply hprefix i
    left
    dsimp only [k,nextInner] at hpast
    omega
  by_cases hvar : 35 ≤ i.val
  · exact le_trans (by norm_num) (physical_next_nonnegative x k V Red ell hphysical hV hRed hell i hvar)
  have hcases : i=nextSourceRow j hj 0 ∨ i=nextSourceRow j hj 1 ∨
      i=nextSourceRow j hj 2 ∨ i=nextSourceRow j hj 3 ∨ i=nextSourceRow j hj 4 := by
    simp [Fin.ext_iff,nextSourceRow,sourceRowOffset,nextInner] at ⊢
    dsimp only [k,nextInner] at hpast hi hna hnu
    omega
  have hr := physical_next_source_rows j hj x V Red ell
  rcases hcases with hi | hi | hi | hi | hi
  · subst i
    rw [hr 0]
    exact hpaid
  · subst i
    rw [hr 1]
    change -(1/1000000000000000:ℝ) ≤ modelUnit (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)-Coordinates.mu*modelUnit j x
    linarith only [hwide]
  · subst i
    rw [hr 2]
    change -(1/1000000000000000:ℝ) ≤ modelLength (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)+
      (6*Coordinates.kappa-1)*modelSlots (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)-modelUnit (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)
    linarith only [hactive]
  · subst i
    rw [hr 3]
    change -(1/1000000000000000:ℝ) ≤ modelLength (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)-modelSlots (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)
    linarith only [hplain]
  · subst i
    rw [hr 4]
    change -(1/1000000000000000:ℝ) ≤ modelSlots (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)
    linarith only [hslots]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.physical_next_models
#print axioms OAI.SevenEighths.Cycle153Reachable.physical_next_history

#print axioms OAI.SevenEighths.Cycle153Reachable.raw_prefix_of_physical_step
