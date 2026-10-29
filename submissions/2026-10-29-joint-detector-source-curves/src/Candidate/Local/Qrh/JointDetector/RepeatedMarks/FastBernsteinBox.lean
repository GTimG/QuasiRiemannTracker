/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.BernsteinBox
namespace Qrh.JointDetector.RepeatedMarks.FastBernsteinBox
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BernsteinBox

def density24 (a : Fin 3 → Fin 5 → ℝ) (lo hi : ℝ) (i : Fin 3) (j : Fin 5) : ℝ :=
 ![a 0 j+lo*a 1 j+lo^2*a 2 j,
   a 0 j+(lo+hi)/2*a 1 j+lo*hi*a 2 j,
   a 0 j+hi*a 1 j+hi^2*a 2 j] i

def fast24 (a : Fin 3 → Fin 5 → ℝ) (lo hi : ℝ) (i : Fin 3) (j : Fin 5) : ℝ :=
 let d := density24 a lo hi i
 ![d 0,d 0+d 1/4,d 0+d 1/2+d 2/6,
   d 0+3*d 1/4+d 2/2+d 3/4,d 0+d 1+d 2+d 3+d 4] j

def fast20 (a : Fin 3 → Fin 1 → ℝ) (lo hi : ℝ) (i : Fin 3) (_j : Fin 1) : ℝ :=
 ![a 0 0+lo*a 1 0+lo^2*a 2 0,
   a 0 0+(lo+hi)/2*a 1 0+lo*hi*a 2 0,
   a 0 0+hi*a 1 0+hi^2*a 2 0] i

theorem coefficients24_eq (a : Fin 3 → Fin 5 → ℝ) (lo hi : ℝ) (i : Fin 3) (j : Fin 5) :
 coefficients a lo hi i j=fast24 a lo hi i j := by
 fin_cases i <;> fin_cases j <;>
  norm_num [coefficients,intervalPower,fast24,density24,Fin.sum_univ_succ,Nat.choose] <;> ring

theorem coefficients20_eq (a : Fin 3 → Fin 1 → ℝ) (lo hi : ℝ) (i : Fin 3) (j : Fin 1) :
 coefficients a lo hi i j=fast20 a lo hi i j := by
 fin_cases i <;> fin_cases j <;>
  norm_num [coefficients,intervalPower,fast20,Fin.sum_univ_succ,Nat.choose] <;> ring

end
end Qrh.JointDetector.RepeatedMarks.FastBernsteinBox
