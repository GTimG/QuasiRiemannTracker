/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.MixedSteps
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators
open Record12518109Admission

def firstPoint (i j : ℕ) : Fin 8 → ℝ :=
  ![(i:ℝ),(j:ℝ),1,localR i j,localL i j,localL j i,localO i j,localO j i]
def firstWeighted {ι : Type*} (s : Finset ι) (i j : ι→ℕ) (w : ι→ℝ) : Fin 8→ℝ :=
  fun k => ∑t∈s,w t*firstPoint (i t) (j t) k
def firstLinear (a x : Fin 8→ℝ) : ℝ :=
  a 0*x 0+a 1*x 1+a 2*x 2+a 3*x 3+a 4*x 4+a 5*x 5+a 6*x 6+a 7*x 7

theorem firstLinear_weighted {ι : Type*} (s : Finset ι) (i j : ι→ℕ)
    (w : ι→ℝ) (a : Fin 8→ℝ) :
    firstLinear a (firstWeighted s i j w) = ∑t∈s,w t*firstLinear a (firstPoint (i t) (j t)) := by
  simp [firstLinear,firstWeighted,Finset.mul_sum,mul_add,Finset.sum_add_distrib,
    mul_assoc,mul_left_comm]

theorem weighted_min_le {ι : Type*} (s : Finset ι) (w x y : ι→ℝ)
    (hw : ∀t∈s,0 ≤ w t) :
    (∑t∈s,w t*min (x t) (y t)) ≤ min (∑t∈s,w t*x t) (∑t∈s,w t*y t) := by
  apply le_min
  · exact Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (min_le_left _ _) (hw t ht))
  · exact Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (min_le_right _ _) (hw t ht))

theorem weighted_max_le {ι : Type*} (s : Finset ι) (w x : ι→ℝ)
    (hw : ∀t∈s,0 ≤ w t) :
    max (∑t∈s,w t*x t) 0 ≤ ∑t∈s,w t*max (x t) 0 := by
  apply max_le
  · exact Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (le_max_left _ _) (hw t ht))
  · exact Finset.sum_nonneg (fun t ht => mul_nonneg (hw t ht) (le_max_right _ _))

theorem weighted_diff_max_le {ι : Type*} (s : Finset ι) (w x y : ι→ℝ)
    (hw : ∀t∈s,0 ≤ w t) :
    max ((∑t∈s,w t*x t)-(∑t∈s,w t*y t)) 0 ≤ ∑t∈s,w t*max (x t-y t) 0 := by
  have he : (∑t∈s,w t*x t)-(∑t∈s,w t*y t) = ∑t∈s,w t*(x t-y t) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  rw [he]
  exact weighted_max_le s w (fun t => x t-y t) hw

theorem minMaxCone_weighted {ι : Type*} (s : Finset ι) (w x y : ι→ℝ)
    (hw : ∀t∈s,0 ≤ w t) (A B C D E : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (∑t∈s,w t*minMaxCone A B C D E (x t) (y t)) ≤
      minMaxCone A B C D E (∑t∈s,w t*x t) (∑t∈s,w t*y t) := by
  have hm := mul_le_mul_of_nonneg_left (weighted_min_le s w x y hw) hC
  have hd := mul_le_mul_of_nonneg_left (weighted_diff_max_le s w x y hw) hD
  have he := mul_le_mul_of_nonneg_left (weighted_diff_max_le s w y x hw) hE
  have hid : (∑t∈s,w t*minMaxCone A B C D E (x t) (y t)) =
      A*(∑t∈s,w t*x t)+B*(∑t∈s,w t*y t)+C*(∑t∈s,w t*min (x t) (y t))-
        D*(∑t∈s,w t*max (x t-y t) 0)-E*(∑t∈s,w t*max (y t-x t) 0) := by
    calc
      _ = ∑t∈s,(A*(w t*x t)+B*(w t*y t)+C*(w t*min (x t) (y t))-
          D*(w t*max (x t-y t) 0)-E*(w t*max (y t-x t) 0)) := by
        apply Finset.sum_congr rfl
        intro t ht
        unfold minMaxCone
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  rw [hid]
  unfold minMaxCone
  linarith only [hm,hd,he]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.minMaxCone_weighted
