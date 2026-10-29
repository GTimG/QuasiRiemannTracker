/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

/-- Detector precision is chosen after the fixed moment degree, without
refining the physical mesh. Every parameter stays fixed as U grows. -/
theorem choose_zero_budget (εMax buffer loss : ℝ) (J : ℕ)
    (hεMax : 0<εMax) (hbuffer : 0<buffer) (hloss : 0<loss) :
    ∃ε e κ η τ : ℝ,∃n : ℕ,
      0<ε ∧ ε≤εMax ∧ 0<e ∧ e≤buffer ∧ e<1/1000 ∧
      0<κ ∧ κ≤1 ∧ 0≤η ∧
      12*e*((22:ℝ)+2)+8*κ+2*η≤ε/2 ∧
      0<τ ∧ τ<1/2 ∧ 4*τ<η ∧ τ*(J:ℝ)≤loss/4 ∧
      0<n ∧ (49/100:ℝ)≤(n:ℝ)*e := by
  let ε := min (εMax/2) (1/1000:ℝ)
  have hε : 0<ε := lt_min (by positivity) (by norm_num)
  have hεle : ε≤εMax := (min_le_left _ _).trans (by linarith)
  have hεsmall : ε≤1/1000 := min_le_right _ _
  let e := min (buffer/2) (ε/10000)
  have he : 0<e := lt_min (by positivity) (by positivity)
  have heb : e≤buffer := (min_le_left _ _).trans (by linarith)
  have heε : e≤ε/10000 := min_le_right _ _
  have hesmall : e<1/1000 := by linarith
  let κ := ε/100
  let η := ε/100
  let τ := min (η/8) (min (1/4:ℝ) (loss/(8*((J:ℝ)+1))))
  have hη : 0<η := by dsimp [η];positivity
  have hτ : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hτη : τ≤η/8 := min_le_left _ _
  have hτsmall : τ≤1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hτloss : τ≤loss/(8*((J:ℝ)+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτJ : τ*(J:ℝ)≤loss/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*((J:ℝ)+1))).mp hτloss
    have hp := mul_nonneg hτ.le (show 0≤(J:ℝ) by positivity)
    nlinarith only [hh,hτ.le,hloss.le]
  let n : ℕ := ⌈(49/100:ℝ)/e⌉₊+1
  have hn : 0<n := by dsimp [n];omega
  have hne : (49/100:ℝ)≤(n:ℝ)*e := by
    have hh : (49/100:ℝ)/e≤(n:ℝ) :=
      (Nat.le_ceil _).trans (by dsimp [n];push_cast;linarith)
    exact (div_le_iff₀ he).mp hh
  refine ⟨ε,e,κ,η,τ,n,hε,hεle,he,heb,hesmall,?_,?_,hη.le,?_,hτ,?_,?_,hτJ,hn,hne⟩
  · dsimp [κ];positivity
  · dsimp [κ];linarith
  · dsimp [κ,η];linarith
  · linarith
  · linarith

end
end Qrh.JointDetector.RepeatedMarks
