/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.AuxHighTemplates
namespace Qrh.JointDetector.RepeatedMarks.CurveHighTemplates
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 60000
open BernsteinBox HighTemplates AuxHighTemplates
def hCoeff (A D : ℝ) : Fin 3 → ℝ := ![1,D-6*A,0]
def pCoeff (B L s D : ℝ) : Fin 3 → ℝ := ![B-L*s,D*(B-L*s)-L,-D*L]
def sCoeff (s A D : ℝ) : Fin 3 → ℝ := ![s,1+D*s-A,D]
def uCoeff (A : ℝ) : Fin 3 → ℝ := ![0,A,0]
def rCoeff (rho D : ℝ) : Fin 3 → ℝ := ![rho,rho*D,0]
def capPower (B0 L0 c a0 a1 B L s A D rho : ℝ) (i : Fin 4) (j : Fin 3) : ℝ :=
  affineCapHighPower B0 L0 c a0 a1 (hCoeff A D j) (pCoeff B L s D j) (sCoeff s A D j) (uCoeff A j) (rCoeff rho D j) i 0
theorem cap_power (B0 L0 c a0 a1 B L s A D rho nu v : ℝ) :
  powerEval (capPower B0 L0 c a0 a1 B L s A D rho) nu v =
    affineCapHigh B0 L0 c a0 a1 (1+(D-6*A)*v) ((B-L*(s+v))*(1+D*v))
      ((s+v)*(1+D*v)-A*v) (A*v) (rho*(1+D*v)) nu := by
  norm_num [powerEval,capPower,affineCapHighPower,affineCapHigh,hCoeff,pCoeff,sCoeff,uCoeff,rCoeff,Fin.sum_univ_succ]
  ring
def budgetPower (B0 L0 c a0 a1 B L s A D rho : ℝ) (i : Fin 4) (j : Fin 3) : ℝ :=
  affineBudgetHighPower B0 L0 c a0 a1 (hCoeff A D j) (pCoeff B L s D j) (sCoeff s A D j) (uCoeff A j) (rCoeff rho D j) i 0
theorem budget_power (B0 L0 c a0 a1 B L s A D rho nu v : ℝ) :
  powerEval (budgetPower B0 L0 c a0 a1 B L s A D rho) nu v =
    affineBudgetHigh B0 L0 c a0 a1 (1+(D-6*A)*v) ((B-L*(s+v))*(1+D*v))
      ((s+v)*(1+D*v)-A*v) (A*v) (rho*(1+D*v)) nu := by
  norm_num [powerEval,budgetPower,affineBudgetHighPower,affineBudgetHigh,hCoeff,pCoeff,sCoeff,uCoeff,rCoeff,Fin.sum_univ_succ]
  ring
def selectedPower (B0 L0 c a0 a1 B L s A D rho : ℝ) (i : Fin 4) (j : Fin 3) : ℝ :=
  if hi : i.val<3 then AuxHighTemplates.selectedPower a0 a1 (hCoeff A D j) (pCoeff B L s D j) (sCoeff s A D j) (uCoeff A j) (rCoeff rho D j) ⟨i.val,hi⟩ 0 else 0
theorem selected_power (B0 L0 c a0 a1 B L s A D rho nu v : ℝ) :
  powerEval (selectedPower B0 L0 c a0 a1 B L s A D rho) nu v =
    selectedHigh a0 a1 (1+(D-6*A)*v) ((B-L*(s+v))*(1+D*v))
      ((s+v)*(1+D*v)-A*v) (A*v) (rho*(1+D*v)) nu := by
  norm_num [powerEval,selectedPower,AuxHighTemplates.selectedPower,selectedHigh,selectedDen,selectedSave,hCoeff,pCoeff,sCoeff,uCoeff,rCoeff,Fin.sum_univ_succ]
  ring
def tailPower (B0 L0 c a0 a1 B L s A D rho : ℝ) (i : Fin 4) (j : Fin 3) : ℝ :=
  if hi : i.val<3 then AuxHighTemplates.tailPower B0 a0 a1 (hCoeff A D j) (pCoeff B L s D j) (sCoeff s A D j) (uCoeff A j) (rCoeff rho D j) ⟨i.val,hi⟩ 0 else 0
theorem tail_power (B0 L0 c a0 a1 B L s A D rho nu v : ℝ) :
  powerEval (tailPower B0 L0 c a0 a1 B L s A D rho) nu v =
    tailHigh B0 a0 a1 (1+(D-6*A)*v) ((B-L*(s+v))*(1+D*v))
      ((s+v)*(1+D*v)-A*v) (A*v) (rho*(1+D*v)) nu := by
  norm_num [powerEval,tailPower,AuxHighTemplates.tailPower,tailHigh,selectedDen,selectedSave,hCoeff,pCoeff,sCoeff,uCoeff,rCoeff,Fin.sum_univ_succ]
  ring
end
end Qrh.JointDetector.RepeatedMarks.CurveHighTemplates
