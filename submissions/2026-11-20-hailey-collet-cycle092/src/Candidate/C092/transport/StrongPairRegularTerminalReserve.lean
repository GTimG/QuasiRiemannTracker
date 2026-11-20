/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The source certificate rho stays fixed. A smaller positive terminal reserve
survives every actual branch and the stated total finite-class overhead. -/
import Candidate.C092.Source

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

def terminalReserve : ℝ := (rho:ℝ)/8

def terminalFramePrice (V : ℝ) : ℝ :=
  V+(u:ℝ)-terminalReserve+(5/6)*max 0 ((H:ℝ)-V)

theorem terminal_reserve_pos : 0 < terminalReserve := by norm_num [terminalReserve,rho]

theorem terminal_H_unchanged : (H:ℝ)=1-6*(u:ℝ) := by norm_num [H,u]

/-- Low, high, small-native and paid ordinary all have the checked rho/4
price. Marked/unmarked P6 have radialAllowance+inverseLoss; inverseLoss<=rho/8
places both beneath the SAME rho/4 price before outer overhead. -/
theorem terminal_branch_reserves {V inverseLoss overhead : ℝ}
    (hInv : inverseLoss ≤ (rho:ℝ)/8) (hOver : overhead < (rho:ℝ)/8) :
    V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)+overhead < terminalFramePrice V ∧
    V+radialAllowance V+inverseLoss+overhead < terminalFramePrice V := by
  unfold terminalFramePrice terminalReserve radialAllowance
  push_cast
  have hrho : (0:ℝ) < (rho:ℝ) := by norm_num [rho]
  constructor <;> linarith

/-- Four explicitly named power losses suffice. Finite numbers of response,
source, attaining-slot and character labels are absorbed in the constant;
the genuine U-dependent dyad count has its separate charged power. -/
theorem terminal_named_overhead_budget
    {heightLoss dyadLoss mellinLoss groupingLoss : ℝ}
    (hh0 : 0 ≤ heightLoss) (hd0 : 0 ≤ dyadLoss) (hm0 : 0 ≤ mellinLoss) (hg0 : 0 ≤ groupingLoss)
    (hh : heightLoss ≤ (rho:ℝ)/64) (hd : dyadLoss ≤ (rho:ℝ)/64)
    (hm : mellinLoss ≤ (rho:ℝ)/64) (hg : groupingLoss ≤ (rho:ℝ)/64) :
    0 ≤ heightLoss+dyadLoss+mellinLoss+groupingLoss ∧
    heightLoss+dyadLoss+mellinLoss+groupingLoss < (rho:ℝ)/8 := by
  have hrho : (0:ℝ) < (rho:ℝ) := by norm_num [rho]
  constructor <;> linarith

/-- Every positive choice used here is strictly smaller than the fixed
certificate margin. No certificate, u, H, length cap or source is changed. -/
theorem terminal_explicit_loss_choices :
    0 < (rho:ℝ)/8 ∧ 0 < (rho:ℝ)/64 ∧ 4*((rho:ℝ)/64) < (rho:ℝ)/8 := by norm_num [rho]

#print axioms terminal_branch_reserves
#print axioms terminal_named_overhead_budget
end
end QRH.Cycle092.StrongPair
