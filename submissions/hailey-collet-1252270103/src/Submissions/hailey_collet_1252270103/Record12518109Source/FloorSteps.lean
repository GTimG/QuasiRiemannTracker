/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.MixedSteps
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

def floorK (c : Cell) (positiveDefect : Bool) : ℝ :=
  if positiveDefect then c.q/K else 0
def floorPeriodic (ν : ℝ) (i j : ℕ) : ℝ :=
  -2*d ν+rr ν*localR i j-rr ν*localL j i-d ν*localO j i

theorem naturalFloor_eq (c : Cell) (i j : ℕ) (p : Bool) (ν : ℝ) :
    naturalFloor c i j p ν =
      minMaxCone (d ν-floorK c p*d ν/3) (d ν+etaD ν-floorK c p*d ν/3)
        (floorK c p*d ν) 0 (d ν-rr ν) i j+floorPeriodic ν i j := by
  cases p <;> simp only [naturalFloor,floorK,Bool.false_eq_true,if_false,if_true]
  all_goals unfold floorCore minMaxCone floorPeriodic; ring

theorem floorPeriodic_add_left (ν : ℝ) (i j : ℕ) :
    floorPeriodic ν (i+6) j = floorPeriodic ν i j := by
  simp [floorPeriodic,localR_add_left,localL_add_right,localO_add_right]
theorem floorPeriodic_add_right (ν : ℝ) (i j : ℕ) :
    floorPeriodic ν i (j+6) = floorPeriodic ν i j := by
  simp [floorPeriodic,localR_add_right,localL_add_left,localO_add_left]

theorem naturalFloor_step_left (c : Cell) (p : Bool) (ν : ℝ) (i j : ℕ)
    (hd : 0 ≤ d ν) (hν : 0 ≤ ν) (hk : 0 ≤ floorK c p) :
    naturalFloor c i j p ν+6*d ν*(1-floorK c p/3) ≤
      naturalFloor c (i+6) j p ν := by
  rw [naturalFloor_eq,naturalFloor_eq,floorPeriodic_add_left]
  push_cast
  have h := minMaxCone_step_left (A:=d ν-floorK c p*d ν/3)
    (B:=d ν+etaD ν-floorK c p*d ν/3) (C:=floorK c p*d ν)
    (D:=0) (E:=d ν-rr ν) (x:=(i:ℝ)) (y:=(j:ℝ))
    (mul_nonneg hk hd) le_rfl (by unfold rr; linarith)
  nlinarith only [h]

theorem naturalFloor_step_right (c : Cell) (p : Bool) (ν : ℝ) (i j : ℕ)
    (hd : 0 ≤ d ν) (hν : 0 ≤ ν) (hk : 0 ≤ floorK c p) :
    naturalFloor c i j p ν+6*(etaD ν+rr ν-floorK c p*d ν/3) ≤
      naturalFloor c i (j+6) p ν := by
  rw [naturalFloor_eq,naturalFloor_eq,floorPeriodic_add_right]
  push_cast
  have h := minMaxCone_step_right (A:=d ν-floorK c p*d ν/3)
    (B:=d ν+etaD ν-floorK c p*d ν/3) (C:=floorK c p*d ν)
    (D:=0) (E:=d ν-rr ν) (x:=(i:ℝ)) (y:=(j:ℝ))
    (mul_nonneg hk hd) le_rfl (by unfold rr; linarith)
  linarith only [h]

theorem complementaryFloor_eq (c : Cell) (i j : ℕ) (ν : ℝ) :
    complementaryFloor i j ν = naturalFloor c i j false ν-d ν*localB i j := by
  simp [complementaryFloor,naturalFloor]

theorem complementaryFloor_step_left (c : Cell) (ν : ℝ) (i j : ℕ)
    (hd : 0 ≤ d ν) (hν : 0 ≤ ν) :
    complementaryFloor i j ν+3*d ν ≤ complementaryFloor (i+6) j ν := by
  have h := naturalFloor_step_left c false ν i j hd hν (by simp [floorK])
  simp only [floorK,Bool.false_eq_true,if_false,zero_div,sub_zero] at h
  have hb := mul_le_mul_of_nonneg_left (localB_add_left_le i j) hd
  rw [complementaryFloor_eq c,complementaryFloor_eq c]
  nlinarith only [h,hb]

theorem complementaryFloor_step_right (c : Cell) (ν : ℝ) (i j : ℕ)
    (hd : 0 ≤ d ν) (hν : 0 ≤ ν) :
    complementaryFloor i j ν+6*(etaD ν+rr ν) ≤ complementaryFloor i (j+6) ν := by
  have h := naturalFloor_step_right c false ν i j hd hν (by simp [floorK])
  simp only [floorK,Bool.false_eq_true,if_false,zero_mul,zero_div,sub_zero] at h
  have hb := mul_le_mul_of_nonneg_left (localB_add_right_le i j) hd
  rw [complementaryFloor_eq c,complementaryFloor_eq c]
  linarith only [h,hb]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.naturalFloor_step_right
#print axioms QRH.Record12518109Source.complementaryFloor_step_left
#print axioms QRH.Record12518109Source.complementaryFloor_step_right
