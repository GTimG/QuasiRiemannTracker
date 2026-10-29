/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks.BernsteinBox
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 60000
open scoped BigOperators

def powerEval {n m : ℕ} (a : Fin (n+1) → Fin (m+1) → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, a i j*x^i.val*y^j.val

def bernEval {n m : ℕ} (a : Fin (n+1) → Fin (m+1) → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, a i j*((n.choose i.val:ℕ):ℝ)*x^i.val*(1-x)^(n-i.val)*
    ((m.choose j.val:ℕ):ℝ)*y^j.val*(1-y)^(m-j.val)

def intervalPower {n m : ℕ} (a : Fin (n+1) → Fin (m+1) → ℝ)
    (lo hi : ℝ) (i : Fin (n+1)) (j : Fin (m+1)) : ℝ :=
  ∑ k, if i.val ≤ k.val then
    a k j*((k.val.choose i.val:ℕ):ℝ)*lo^(k.val-i.val)*(hi-lo)^i.val else 0

def coefficients {n m : ℕ} (a : Fin (n+1) → Fin (m+1) → ℝ)
    (lo hi : ℝ) (i : Fin (n+1)) (j : Fin (m+1)) : ℝ :=
  ∑ k, ∑ l, if k.val ≤ i.val ∧ l.val ≤ j.val then
    intervalPower a lo hi k l * ((i.val.choose k.val:ℕ):ℝ)/((n.choose k.val:ℕ):ℝ)*
      ((j.val.choose l.val:ℕ):ℝ)/((m.choose l.val:ℕ):ℝ) else 0

theorem bernEval_nonneg {n m : ℕ} {a : Fin (n+1) → Fin (m+1) → ℝ}
    (ha : ∀ i j, 0 ≤ a i j) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) : 0 ≤ bernEval a x y := by
  unfold bernEval
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have haij := ha i j
  have hx0 := hx.1
  have hy0 := hy.1
  have h0 : 0 ≤ 1-x := by linarith [hx.2]
  have h1 : 0 ≤ 1-y := by linarith [hy.2]
  positivity

/-- Fixed-degree conversion identities are proved once symbolically, so
individual rational source steps only check coefficient signs. -/
theorem reconstruct24 (a : Fin 3 → Fin 5 → ℝ) (lo hi x y : ℝ) :
    powerEval a (lo+(hi-lo)*x) y = bernEval (coefficients a lo hi) x y := by
  norm_num [powerEval,bernEval,coefficients,intervalPower,Fin.sum_univ_succ,Nat.choose]
  ring

theorem reconstruct54 (a : Fin 6 → Fin 5 → ℝ) (lo hi x y : ℝ) :
    powerEval a (lo+(hi-lo)*x) y = bernEval (coefficients a lo hi) x y := by
  norm_num [powerEval,bernEval,coefficients,intervalPower,Fin.sum_univ_succ,Nat.choose]
  ring

theorem reconstruct20 (a : Fin 3 → Fin 1 → ℝ) (lo hi x y : ℝ) :
    powerEval a (lo+(hi-lo)*x) y = bernEval (coefficients a lo hi) x y := by
  norm_num [powerEval,bernEval,coefficients,intervalPower,Fin.sum_univ_succ,Nat.choose]
  ring

theorem reconstruct30 (a : Fin 4 → Fin 1 → ℝ) (lo hi x y : ℝ) :
    powerEval a (lo+(hi-lo)*x) y = bernEval (coefficients a lo hi) x y := by
  norm_num [powerEval,bernEval,coefficients,intervalPower,Fin.sum_univ_succ,Nat.choose]
  ring

end
end Qrh.JointDetector.RepeatedMarks.BernsteinBox
