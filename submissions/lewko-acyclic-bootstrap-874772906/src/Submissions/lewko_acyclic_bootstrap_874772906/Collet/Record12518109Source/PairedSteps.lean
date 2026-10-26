/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.MixedSteps
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

def pairedPeriodic (l r : ℝ) (i j : ℕ) : ℝ :=
  -2-localO i j-localO j i+(1+rho l+rho r)*localR i j-
    rho l*localL i j-rho r*localL j i

theorem pairedGap_eq (c : Cell) (i j : ℕ) (l r : ℝ) :
    pairedGap c i j l r =
      minMaxCone (l+1-gamma c) (r+1-gamma c) 0 (1-rho l) (1-rho r) i j+
        pairedPeriodic l r i j := by
  unfold pairedGap minMaxCone pairedPeriodic
  ring

theorem pairedPeriodic_add_left (l r : ℝ) (i j : ℕ) :
    pairedPeriodic l r (i+6) j = pairedPeriodic l r i j := by
  simp [pairedPeriodic,localR_add_left,localL_add_left,localL_add_right,
    localO_add_left,localO_add_right]
theorem pairedPeriodic_add_right (l r : ℝ) (i j : ℕ) :
    pairedPeriodic l r i (j+6) = pairedPeriodic l r i j := by
  simp [pairedPeriodic,localR_add_right,localL_add_left,localL_add_right,
    localO_add_left,localO_add_right]

theorem rho_bounds {ν : ℝ} (hν : ν ∈ Set.Icc (31/50) (3/4)) :
    2/7 ≤ rho ν ∧ rho ν ≤ 1 := by
  have hd : 0 < 3*d ν := by unfold d; linarith [hν.2]
  have hn : 0 ≤ 10*ν/(3*d ν) := div_nonneg (by linarith [hν.1]) hd.le
  have hh : 10*ν/(3*d ν) ≤ 5/7 := by
    apply (div_le_iff₀ hd).mpr
    unfold d
    linarith [hν.2]
  unfold rho
  constructor <;> linarith

theorem pairedGap_step_left (c : Cell) (i j : ℕ) (l r : ℝ)
    (hl : rho l ≤ 1) (hr : rho r ≤ 1) :
    pairedGap c i j l r+6*(l+rho l-gamma c) ≤ pairedGap c (i+6) j l r := by
  rw [pairedGap_eq,pairedGap_eq,pairedPeriodic_add_left]
  push_cast
  have h := minMaxCone_step_left (A:=l+1-gamma c) (B:=r+1-gamma c)
    (C:=0) (D:=1-rho l) (E:=1-rho r) (x:=(i:ℝ)) (y:=(j:ℝ))
    le_rfl (by linarith) (by linarith)
  linarith only [h]

theorem pairedGap_step_right (c : Cell) (i j : ℕ) (l r : ℝ)
    (hl : rho l ≤ 1) (hr : rho r ≤ 1) :
    pairedGap c i j l r+6*(r+rho r-gamma c) ≤ pairedGap c i (j+6) l r := by
  rw [pairedGap_eq,pairedGap_eq,pairedPeriodic_add_right]
  push_cast
  have h := minMaxCone_step_right (A:=l+1-gamma c) (B:=r+1-gamma c)
    (C:=0) (D:=1-rho l) (E:=1-rho r) (x:=(i:ℝ)) (y:=(j:ℝ))
    le_rfl (by linarith) (by linarith)
  linarith only [h]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.rho_bounds
#print axioms QRH.Record12518109Source.pairedGap_step_left
