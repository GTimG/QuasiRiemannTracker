/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.GlobalSurplus
import Submissions.hailey_collet_1252270103.Record12518109Source.FloorValuations
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators
open Record12518109Admission

def globalFloor (c : Cell) (p : Bool) (ν : ℝ) (v : Fin 8→ℝ) : ℝ :=
  minMaxLinear (d ν-floorK c p*d ν/3) (d ν+etaD ν-floorK c p*d ν/3)
    (floorK c p*d ν) 0 (d ν-rr ν) ![0,0,-2*d ν,rr ν,0,-rr ν,0,-d ν] v
def globalComplement (c : Cell) (ν : ℝ) (v : Fin 8→ℝ) : ℝ :=
  globalFloor c false ν v-d ν*globalB false v

theorem globalFloor_point (c : Cell) (p : Bool) (ν : ℝ) (i j : ℕ) :
    globalFloor c p ν (firstPoint i j) = naturalFloor c i j p ν := by
  rw [naturalFloor_eq]
  simp [globalFloor,minMaxLinear,firstPoint,firstLinear,floorPeriodic]
  ring

theorem globalComplement_point (c : Cell) (ν : ℝ) (i j : ℕ) :
    globalComplement c ν (firstPoint i j) = complementaryFloor i j ν := by
  unfold globalComplement
  rw [globalFloor_point,(globalB_point i j).1,complementaryFloor_eq c]

theorem globalFloor_weighted_lower {ι : Type*} (c : Cell) (p : Bool) (ν : ℝ)
    (s : Finset ι) (i j : ι→ℕ) (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hk : 0 ≤ floorK c p) (hd : 0 ≤ d ν) (hν : 0 ≤ ν) :
    (∑t∈s,w t*globalFloor c p ν (firstPoint (i t) (j t))) ≤
      globalFloor c p ν (firstWeighted s i j w) := by
  exact minMaxLinear_weighted s i j w hw
    (d ν-floorK c p*d ν/3) (d ν+etaD ν-floorK c p*d ν/3)
    (floorK c p*d ν) 0 (d ν-rr ν) ![0,0,-2*d ν,rr ν,0,-rr ν,0,-d ν]
    (mul_nonneg hk hd) le_rfl (by unfold rr; linarith)

theorem globalComplement_weighted_lower {ι : Type*} (c : Cell) (ν : ℝ)
    (s : Finset ι) (i j : ι→ℕ) (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hd : 0 ≤ d ν) (hν : 0 ≤ ν) :
    (∑t∈s,w t*globalComplement c ν (firstPoint (i t) (j t))) ≤
      globalComplement c ν (firstWeighted s i j w) := by
  have hf := globalFloor_weighted_lower c false ν s i j w hw (by simp [floorK]) hd hν
  have hb := mul_le_mul_of_nonneg_left (globalB_weighted s i j w hw false) hd
  have heq : (∑t∈s,w t*globalComplement c ν (firstPoint (i t) (j t))) =
      (∑t∈s,w t*globalFloor c false ν (firstPoint (i t) (j t)))-
        d ν*(∑t∈s,w t*globalB false (firstPoint (i t) (j t))) := by
    simp [globalComplement,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc,mul_left_comm]
  rw [heq]
  unfold globalComplement
  linarith only [hf,hb]

theorem globalFloor_weighted {ι : Type*} (k : Fin 15) (p : Bool) {ν : ℝ}
    (hν : ν ∈ Set.Icc (rawCells k).q (3/4)) (s : Finset ι)
    (i j : ι→ℕ) (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hi : ∀t∈s,0 < i t) (hj : ∀t∈s,0 < j t) :
    0 ≤ globalFloor (rawCells k) p ν (firstWeighted s i j w) := by
  have hq := (raw_mixed_parameters k).2.2.2.2.1
  have hdn := floor_density_bound (ν:=ν) ⟨hq.trans hν.1,hν.2⟩
  have hp := globalFloor_weighted_lower (rawCells k) p ν s i j w hw
    (raw_floorK_bounds k p).1 hdn.2.1 hdn.1
  apply le_trans (b:=∑t∈s,w t*globalFloor (rawCells k) p ν (firstPoint (i t) (j t))) ?_ hp
  apply Finset.sum_nonneg
  intro t ht
  rw [globalFloor_point]
  exact mul_nonneg (hw t ht) (raw_naturalFloor_all k hν p (i t) (j t) (hi t ht) (hj t ht))

theorem globalComplement_weighted {ι : Type*} (k : Fin 15) {ν : ℝ}
    (hν : ν ∈ Set.Icc (rawCells k).q (3/4)) (s : Finset ι)
    (i j : ι→ℕ) (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hi : ∀t∈s,0 < i t) (hj : ∀t∈s,0 < j t) :
    0 ≤ globalComplement (rawCells k) ν (firstWeighted s i j w) := by
  have hq := (raw_mixed_parameters k).2.2.2.2.1
  have hdn := floor_density_bound (ν:=ν) ⟨hq.trans hν.1,hν.2⟩
  have hp := globalComplement_weighted_lower (rawCells k) ν s i j w hw hdn.2.1 hdn.1
  apply le_trans (b:=∑t∈s,w t*globalComplement (rawCells k) ν (firstPoint (i t) (j t))) ?_ hp
  apply Finset.sum_nonneg
  intro t ht
  rw [globalComplement_point]
  exact mul_nonneg (hw t ht) (raw_complementaryFloor_all k hν (i t) (j t) (hi t ht) (hj t ht))

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.globalFloor_weighted
#print axioms QRH.Record12518109Source.globalComplement_weighted
