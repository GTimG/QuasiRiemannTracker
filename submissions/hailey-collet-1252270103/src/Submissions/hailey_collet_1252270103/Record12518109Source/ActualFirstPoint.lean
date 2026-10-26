/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uses the literal valuation factorization adapted from Gao, PR63, Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.FiniteCone
import Submissions.hailey_collet_1252270103.Record12518109Natural.Valuation
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators
open Record12518109Admission
open OAI.SevenEighths
open CenteredMomentActive

theorem netExponent_eq_residue (i j : ℕ) : (netExponent i j:ℤ) = residue i j := by
  unfold netExponent residue
  omega

theorem local_fields_actual (i j : ℕ) :
    localR i j = (if netExponent i j = 0 then (0:ℝ) else 1) ∧
      localL i j = (OAI.SevenEighths.Record12518109Natural.FirstNumeratorValuation.sourceExponent true i j:ℝ) ∧
      localO i j = (if netExponent i j = 5 then (1:ℝ) else 0) := by
  have hr := netExponent_eq_residue i j
  have hn := netExponent_lt_six i j
  have hc : netExponent i j = 0 ∨ netExponent i j = 1 ∨ netExponent i j = 2 ∨
      netExponent i j = 3 ∨ netExponent i j = 4 ∨ netExponent i j = 5 := by omega
  rcases hc with h|h|h|h|h|h <;>
    norm_num [localR,localL,localO,←hr,h,OAI.SevenEighths.Record12518109Natural.FirstNumeratorValuation.sourceExponent]

def firstJoin (a b : Fin 6→ℝ) : Fin 8→ℝ :=
  ![a 0,a 1,a 2,a 3,a 4,b 4,a 5,b 5]

theorem firstJoin_weighted {ι : Type*} (s : Finset ι) (i j : ι→ℕ) (w : ι→ℝ) :
    firstJoin (OAI.SevenEighths.Record12518109Natural.Valuation.weighted s i j w) (OAI.SevenEighths.Record12518109Natural.Valuation.weighted s j i w) = firstWeighted s i j w := by
  funext k
  fin_cases k <;> simp only [firstJoin,OAI.SevenEighths.Record12518109Natural.Valuation.weighted,firstWeighted,firstPoint,OAI.SevenEighths.Record12518109Natural.Valuation.point,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ]
  all_goals apply Finset.sum_congr rfl; intro t ht
  all_goals simp only [(local_fields_actual (i t) (j t)).1,
    (local_fields_actual (i t) (j t)).2.1,(local_fields_actual (i t) (j t)).2.2,
    (local_fields_actual (j t) (i t)).2.1,(local_fields_actual (j t) (i t)).2.2]
  all_goals rfl

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.firstJoin_weighted
