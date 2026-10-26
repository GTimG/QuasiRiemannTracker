/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.Localization
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

def minMaxCone (A B C D E x y : ℝ) : ℝ :=
  A*x+B*y+C*min x y-D*max (x-y) 0-E*max (y-x) 0

theorem minMaxCone_step_left {A B C D E x y : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    minMaxCone A B C D E x y+6*(A-D) ≤ minMaxCone A B C D E (x+6) y := by
  have hm := min_le_min (by linarith : x ≤ x+6) (le_refl y)
  have h1 : max (x+6-y) 0 ≤ max (x-y) 0+6 := by
    apply max_le <;> linarith [le_max_left (x-y) 0,le_max_right (x-y) 0]
  have h2 := max_le_max (by linarith : y-(x+6) ≤ y-x) (le_refl (0:ℝ))
  have hc := mul_nonneg hC (sub_nonneg.mpr hm)
  have hd := mul_nonneg hD (sub_nonneg.mpr h1)
  have he := mul_nonneg hE (sub_nonneg.mpr h2)
  unfold minMaxCone
  nlinarith

theorem minMaxCone_step_right {A B C D E x y : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    minMaxCone A B C D E x y+6*(B-E) ≤ minMaxCone A B C D E x (y+6) := by
  have hm := min_le_min (le_refl x) (by linarith : y ≤ y+6)
  have h1 := max_le_max (by linarith : x-(y+6) ≤ x-y) (le_refl (0:ℝ))
  have h2 : max (y+6-x) 0 ≤ max (y-x) 0+6 := by
    apply max_le <;> linarith [le_max_left (y-x) 0,le_max_right (y-x) 0]
  have hc := mul_nonneg hC (sub_nonneg.mpr hm)
  have hd := mul_nonneg hD (sub_nonneg.mpr h1)
  have he := mul_nonneg hE (sub_nonneg.mpr h2)
  unfold minMaxCone
  nlinarith

def mixedPeriodic (c : Cell) (ν : ℝ) (i j : ℕ) : ℝ :=
  -2*d ν+(2*d ν*omega-d ν*omega*(c.q/c.priorL)*c.priorB+rr ν)*localR i j-
  d ν*omega*(1-(c.q/c.priorL)*c.priorB)*localL i j-rr ν*localL j i-
  d ν*omega*localO i j-d ν*localO j i

theorem mixedLowHigh_eq (c : Cell) (i j : ℕ) (ν : ℝ) :
    mixedLowHigh c i j ν =
      minMaxCone (d ν*(1+omega*(c.q/c.priorL))) (d ν+etaD ν)
        (d ν*(1-omega)*(c.q/K)) (d ν*omega*(c.q/c.priorL)*c.priorB)
        (d ν-rr ν) i j+mixedPeriodic c ν i j := by
  unfold mixedLowHigh localSigma minMaxCone mixedPeriodic
  ring

theorem mixedPeriodic_add_left (c : Cell) (ν : ℝ) (i j : ℕ) :
    mixedPeriodic c ν (i+6) j = mixedPeriodic c ν i j := by
  simp [mixedPeriodic,localR_add_left,localR_add_right,localL_add_left,
    localL_add_right,localO_add_left,localO_add_right]
theorem mixedPeriodic_add_right (c : Cell) (ν : ℝ) (i j : ℕ) :
    mixedPeriodic c ν i (j+6) = mixedPeriodic c ν i j := by
  simp [mixedPeriodic,localR_add_left,localR_add_right,localL_add_left,
    localL_add_right,localO_add_left,localO_add_right]

theorem mixedLowHigh_step_left (c : Cell) (ν : ℝ) (i j : ℕ)
    (hd : 0 ≤ d ν) (hν : 0 ≤ ν) (hk : 0 ≤ c.q/K) (hell : 0 ≤ c.q/c.priorL)
    (hB : 0 ≤ c.priorB) :
    mixedLowHigh c i j ν+6*d ν*(1+omega*(c.q/c.priorL)*(1-c.priorB)) ≤
      mixedLowHigh c (i+6) j ν := by
  rw [mixedLowHigh_eq,mixedLowHigh_eq,mixedPeriodic_add_left]
  push_cast
  have h := minMaxCone_step_left (A:=d ν*(1+omega*(c.q/c.priorL)))
    (B:=d ν+etaD ν) (C:=d ν*(1-omega)*(c.q/K))
    (D:=d ν*omega*(c.q/c.priorL)*c.priorB) (E:=d ν-rr ν) (x:=(i:ℝ)) (y:=(j:ℝ))
    (mul_nonneg (mul_nonneg hd (by norm_num [omega])) hk)
    (mul_nonneg (mul_nonneg (mul_nonneg hd (by norm_num [omega])) hell) hB)
    (by unfold rr; linarith)
  nlinarith only [h]

theorem mixedLowHigh_step_right (c : Cell) (ν : ℝ) (i j : ℕ)
    (hd : 0 ≤ d ν) (hν : 0 ≤ ν) (hk : 0 ≤ c.q/K)
    (hell : 0 ≤ c.q/c.priorL) (hB : 0 ≤ c.priorB) :
    mixedLowHigh c i j ν+6*(etaD ν+rr ν) ≤ mixedLowHigh c i (j+6) ν := by
  rw [mixedLowHigh_eq,mixedLowHigh_eq,mixedPeriodic_add_right]
  push_cast
  have h := minMaxCone_step_right (A:=d ν*(1+omega*(c.q/c.priorL)))
    (B:=d ν+etaD ν) (C:=d ν*(1-omega)*(c.q/K))
    (D:=d ν*omega*(c.q/c.priorL)*c.priorB) (E:=d ν-rr ν) (x:=(i:ℝ)) (y:=(j:ℝ))
    (mul_nonneg (mul_nonneg hd (by norm_num [omega])) hk)
    (mul_nonneg (mul_nonneg (mul_nonneg hd (by norm_num [omega])) hell) hB)
    (by unfold rr; linarith)
  linarith only [h]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.mixedLowHigh_step_left
#print axioms QRH.Record12518109Source.mixedLowHigh_step_right
