/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.GlobalCone
import Submissions.hailey_collet_1252270103.Record12518109Source.LocalSurplus
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators
open Record12518109Admission

def globalB (flip : Bool) (v : Fin 8→ℝ) : ℝ :=
  max (firstLinear (if flip then ![-5,3,0,-1,0,0,0,0] else ![3,-5,0,-1,0,0,0,0]) v) 0/6
def globalSigma (v : Fin 8→ℝ) : ℝ :=
  (firstLinear ![1,1,-2,-1,0,0,0,0] v-globalB false v-globalB true v)/2
def globalLocalization (v : Fin 8→ℝ) : ℝ :=
  3*min (v 0) (v 1)+4*globalSigma v-v 0-v 1

theorem globalB_false (v : Fin 8→ℝ) :
    globalB false v = max (3*v 0-5*v 1-v 3) 0/6 := by
  simp [globalB,firstLinear]
  congr 2
  all_goals ring
theorem globalB_true (v : Fin 8→ℝ) :
    globalB true v = max (3*v 1-5*v 0-v 3) 0/6 := by
  simp [globalB,firstLinear]
  congr 2
  ring

theorem globalB_point (i j : ℕ) :
    globalB false (firstPoint i j) = localB i j ∧
      globalB true (firstPoint i j) = localB j i := by
  rw [globalB_false,globalB_true]
  simp [firstPoint,localB,localR_swap i j]

theorem globalSigma_point (i j : ℕ) :
    globalSigma (firstPoint i j) = localSigma i j := by
  unfold globalSigma
  rw [(globalB_point i j).1,(globalB_point i j).2]
  simp [firstLinear,firstPoint,localSigma]
  ring

theorem globalLocalization_point (i j : ℕ) :
    globalLocalization (firstPoint i j) = localizationReserve i j := by
  unfold globalLocalization
  rw [globalSigma_point]
  rfl

theorem globalB_weighted {ι : Type*} (s : Finset ι) (i j : ι→ℕ)
    (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t) (flip : Bool) :
    globalB flip (firstWeighted s i j w) ≤ ∑t∈s,w t*globalB flip (firstPoint (i t) (j t)) := by
  let a : Fin 8→ℝ := if flip then ![-5,3,0,-1,0,0,0,0] else ![3,-5,0,-1,0,0,0,0]
  have h := weighted_max_le s w (fun t => firstLinear a (firstPoint (i t) (j t))) hw
  rw [←firstLinear_weighted] at h
  have hh := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 6)
  simpa only [globalB,mul_div_assoc,Finset.sum_div,a] using hh

theorem globalSigma_weighted {ι : Type*} (s : Finset ι) (i j : ι→ℕ)
    (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t) :
    (∑t∈s,w t*globalSigma (firstPoint (i t) (j t))) ≤
      globalSigma (firstWeighted s i j w) := by
  have hb := globalB_weighted s i j w hw false
  have hc := globalB_weighted s i j w hw true
  unfold globalSigma
  rw [firstLinear_weighted]
  simp_rw [←mul_div_assoc,mul_sub]
  rw [←Finset.sum_div,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  linarith only [hb,hc]

theorem globalSigma_nonnegative {ι : Type*} (s : Finset ι) (i j : ι→ℕ)
    (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hi : ∀t∈s,0 < i t) (hj : ∀t∈s,0 < j t) :
    0 ≤ globalSigma (firstWeighted s i j w) := by
  apply le_trans (b:=∑t∈s,w t*globalSigma (firstPoint (i t) (j t))) ?_
    (globalSigma_weighted s i j w hw)
  apply Finset.sum_nonneg
  intro t ht
  rw [globalSigma_point]
  exact mul_nonneg (hw t ht) (localSigma_all (i t) (j t) (hi t ht) (hj t ht))

theorem globalLocalization_weighted {ι : Type*} (s : Finset ι) (i j : ι→ℕ)
    (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hi : ∀t∈s,0 < i t) (hj : ∀t∈s,0 < j t) :
    0 ≤ globalLocalization (firstWeighted s i j w) := by
  have hm := weighted_min_le s w (fun t => (i t:ℝ)) (fun t => (j t:ℝ)) hw
  have hsigma := globalSigma_weighted s i j w hw
  have hp : 0 ≤ ∑t∈s,w t*localizationReserve (i t) (j t) :=
    Finset.sum_nonneg (fun t ht => mul_nonneg (hw t ht)
      (localization_all (i t) (j t) (hi t ht) (hj t ht)))
  have heq : (∑t∈s,w t*localizationReserve (i t) (j t)) =
      3*(∑t∈s,w t*min (i t:ℝ) (j t:ℝ))+
        4*(∑t∈s,w t*globalSigma (firstPoint (i t) (j t)))-
        (∑t∈s,w t*(i t:ℝ))-(∑t∈s,w t*(j t:ℝ)) := by
    simp only [globalSigma_point,localizationReserve,mul_sub,mul_add,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc,mul_left_comm]
  rw [heq] at hp
  change 0 ≤ 3*min (∑t∈s,w t*(i t:ℝ)) (∑t∈s,w t*(j t:ℝ))+
    4*globalSigma (firstWeighted s i j w)-(∑t∈s,w t*(i t:ℝ))-(∑t∈s,w t*(j t:ℝ))
  linarith only [hm,hsigma,hp]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.globalSigma_nonnegative
#print axioms QRH.Record12518109Source.globalLocalization_weighted
