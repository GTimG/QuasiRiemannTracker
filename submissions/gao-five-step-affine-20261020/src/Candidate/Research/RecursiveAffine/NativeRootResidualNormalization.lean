/- Exact residual-shell normalization for actual ROOT paid source outputs.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsResidual

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentSecondCanonicalScalar Cycle153LowPhysical
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]

/-- The physical shell weight is a literal scalar in the native OLD
selected-row cost. Factoring it does not change a reciprocal or source
label. -/
theorem native_old_selected_cost_mul_factor
    (reflected second : Bool)(s : Input alpha)(R : Ideal O)
    (Z Mrow amp xi reserve b firstHeight : ℝ)(N : ℕ)(hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (Psi : 𝓢(ℝ,ℂ))(epsMass shellLoss error Cg fixed factor : ℝ) :
    nativeOldSelectedCost reflected second s R Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2
      firstIndex Psi epsMass shellLoss error Cg (fixed*factor)=
      nativeOldSelectedCost reflected second s R Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2
        firstIndex Psi epsMass shellLoss error Cg fixed*factor :=by
  unfold nativeOldSelectedCost
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Remove the actual raw AtState power once, after the SAME whole
receipt's exact value identity has been used. This is the literal
one-shell contract consumed by the physical residual/ray/buffer operator. -/
theorem actual_root_residual_shell_normalization
    {Z outer source oldWithShell oldBase Cg fixed physical shell weighted value : ℝ}
    (hZ : 0<Z)
    (hsource : Z^outer*source≤Z^outer*oldWithShell+Cg*(fixed*shell)*physical*weighted)
    (hold : oldWithShell=oldBase*shell)(hvalue : value=weighted) :
    source≤(oldBase+Z^(-outer)*(Cg*fixed*physical)*value)*shell :=by
  have hinv : Z^(-outer)*Z^outer=1:=by
    rw [←Real.rpow_add hZ]
    simp only [neg_add_cancel,Real.rpow_zero]
  calc
    source=(Z^(-outer))*(Z^outer*source):=by rw [←mul_assoc,hinv,one_mul]
    _≤Z^(-outer)*(Z^outer*oldWithShell+Cg*(fixed*shell)*physical*weighted):=
      mul_le_mul_of_nonneg_left hsource (Real.rpow_nonneg hZ.le _)
    _=(oldBase+Z^(-outer)*(Cg*fixed*physical)*value)*shell:=by
      rw [hold,←hvalue]
      calc
        _=(Z^(-outer)*Z^outer)*(oldBase*shell)+
          Z^(-outer)*(Cg*fixed*physical)*value*shell:=by ring
        _=_:=by rw [hinv];ring
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.native_old_selected_cost_mul_factor
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_root_residual_shell_normalization
