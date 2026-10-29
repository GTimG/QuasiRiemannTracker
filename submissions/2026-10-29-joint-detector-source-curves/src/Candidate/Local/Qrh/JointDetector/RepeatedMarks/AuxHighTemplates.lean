/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.HighTemplates
namespace Qrh.JointDetector.RepeatedMarks.AuxHighTemplates
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BernsteinBox

def selectedDen (a0 a1 ν : ℝ) : ℝ := 3-ν-2*(a0+a1*ν)
def selectedSave (a0 a1 ν : ℝ) : ℝ := selectedDen a0 a1 ν-3*(1-ν)*(1-a0-a1*ν)
def selectedHigh (a0 a1 H P S u rho ν : ℝ) : ℝ :=
 H*selectedSave a0 a1 ν-ν*P*selectedDen a0 a1 ν-
 (a0+a1*ν)*S*selectedDen a0 a1 ν+(u-rho)*selectedDen a0 a1 ν

def selectedPower (a0 a1 H P S u rho : ℝ) (i : Fin 3) (_j : Fin 1) : ℝ :=
 ![H*a0-a0*S*(3-2*a0)+(u-rho)*(3-2*a0),
   H*(2-3*a0+a1)-P*(3-2*a0)-S*(a0*(-1-2*a1)+a1*(3-2*a0))+(u-rho)*(-1-2*a1),
   -3*a1*H-P*(-1-2*a1)-a1*S*(-1-2*a1)] i

def tailHigh (B a0 a1 H P S u rho ν : ℝ) : ℝ :=
 H*ν*B-ν*P-(a0+a1*ν)*S+u-rho
def tailPower (B a0 a1 H P S u rho : ℝ) (i : Fin 3) (_j : Fin 1) : ℝ :=
 ![u-rho-a0*S,H*B-P-a1*S,0] i

theorem selected_power (a0 a1 H P S u rho ν : ℝ) :
 powerEval (selectedPower a0 a1 H P S u rho) ν 0=selectedHigh a0 a1 H P S u rho ν := by
 norm_num [powerEval,selectedPower,selectedHigh,selectedSave,selectedDen,Fin.sum_univ_succ]
 ring

theorem tail_power (B a0 a1 H P S u rho ν : ℝ) :
 powerEval (tailPower B a0 a1 H P S u rho) ν 0=tailHigh B a0 a1 H P S u rho ν := by
 norm_num [powerEval,tailPower,tailHigh,Fin.sum_univ_succ]
 ring

theorem univariate_nonneg {p : Fin 3 → Fin 1 → ℝ} {lo hi ν : ℝ}
 (hlo : lo < hi) (hν : ν ∈ Set.Icc lo hi)
 (hc : ∀ i j,0 ≤ coefficients p lo hi i j) : 0 ≤ powerEval p ν 0 := by
 let x := (ν-lo)/(hi-lo)
 have hx : x ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (by linarith [hν.1]) (by linarith)
  · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hν.2])
 have he : lo+(hi-lo)*x=ν := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
 have hp := bernEval_nonneg hc hx (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl,by norm_num⟩)
 rw [←reconstruct20,he] at hp
 exact hp

theorem selected_high_nonneg (a0 a1 H P S u rho lo hi ν : ℝ)
 (hlo : lo < hi) (hν : ν ∈ Set.Icc lo hi)
 (hc : ∀ i j,0 ≤ coefficients (selectedPower a0 a1 H P S u rho) lo hi i j) :
 0 ≤ selectedHigh a0 a1 H P S u rho ν := by
 rw [←selected_power]
 exact univariate_nonneg hlo hν hc

theorem tail_high_nonneg (B a0 a1 H P S u rho lo hi ν : ℝ)
 (hlo : lo < hi) (hν : ν ∈ Set.Icc lo hi)
 (hc : ∀ i j,0 ≤ coefficients (tailPower B a0 a1 H P S u rho) lo hi i j) :
 0 ≤ tailHigh B a0 a1 H P S u rho ν := by
 rw [←tail_power]
 exact univariate_nonneg hlo hν hc

end
end Qrh.JointDetector.RepeatedMarks.AuxHighTemplates
