/- The fixed root ledger supplies the actual native reserve facts.
Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.Constants

set_option autoImplicit false
namespace Cycle153Endpoint.Arithmetic
noncomputable section
open Cycle63.Optimization
noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Arithmetic_LocalReserves : Cycle63.AffineLedger := Cycle153.Root.rootLedger

def firstCellTop : ℝ := Cycle153.Root.floor+Cycle153.Root.mesh
def g (b : ℝ) : ℝ := B-1+(6*slotPrice-lambda)*b
def regionGap (b : ℝ) : ℝ := B-Cycle153.MarkedRootPrice.intercept+(6*Cycle153.MarkedRootPrice.price-lambda)*b
def amp (b : ℝ) : ℝ := Ka*regionGap b+alpha
def totalA (b : ℝ) : ℝ := B-(lambda-1)*(b-Cycle153.Root.mesh)
def cellUpper (j : ℕ) : ℝ := Cycle153.Root.floor+(j:ℝ)*Cycle153.Root.mesh
def amplifierFloor : ℝ := amp firstCellTop

theorem slotFloor_pos : 0<Cycle153.Root.floor := by norm_num [Cycle153.Root.floor]

theorem cellMesh_pos : 0< Cycle153.Root.mesh := Cycle63.AffineLedger.cellMesh_pos
theorem one_le_cellCount : 1≤ Cycle153.Root.cellCount := Cycle63.AffineLedger.one_le_cellCount
theorem cellCount_mul : (Cycle153.Root.cellCount:ℝ)*Cycle153.Root.mesh=Cycle153.MarkedRootPrice.top-Cycle153.Root.floor := Cycle63.AffineLedger.cellCount_mul
bracket firstCellTop_bounds (digits:=12) : firstCellTop unfolding [firstCellTop,Cycle153.Root.floor,Cycle153.Root.mesh]
bracket slotTop_bounds (digits:=12) : Cycle153.MarkedRootPrice.top unfolding [Cycle153.MarkedRootPrice.top]

theorem cellUpper_bounds {j:ℕ} (hj1:1≤ j)(hjn:j≤ Cycle153.Root.cellCount) :
    firstCellTop≤ cellUpper j ∧ cellUpper j≤ Cycle153.MarkedRootPrice.top :=
  Cycle63.AffineLedger.cellUpper_bounds hj1 hjn

theorem amplifierFloor_pos : 0< amplifierFloor := Cycle63.AffineLedger.amplifierFloor_pos

theorem g_pos {b:ℝ} (hb:firstCellTop≤ b ∧ b≤ Cycle153.MarkedRootPrice.top) : 0< g b :=
  Cycle63.AffineLedger.g_pos hb

theorem amp_pos {b:ℝ} (hb:firstCellTop≤ b ∧ b≤ Cycle153.MarkedRootPrice.top) : 0< amp b :=
  Cycle63.AffineLedger.amp_pos hb

theorem supply_lower : 4/21< ell/dPlus := by
  have hh:=h_bounds
  have hz:=dPlusOffset_bounds
  have hd:0< dPlus:=by unfold dPlus; linarith [hh.1,hz.1]
  rw [lt_div_iff₀ hd]
  unfold dPlus
  norm_num [ell,theta]
  linarith [hh.2,hz.2]
end
end Cycle153Endpoint.Arithmetic

#print axioms Cycle153Endpoint.Arithmetic.amplifierFloor_pos
#print axioms Cycle153Endpoint.Arithmetic.supply_lower
