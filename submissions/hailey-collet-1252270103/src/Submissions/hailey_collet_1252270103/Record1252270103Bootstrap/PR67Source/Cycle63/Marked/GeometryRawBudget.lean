import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.GeometryRawGates
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedParameters
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators

/-- Pay the polynomial geometric height and an optional multiplicative
normalization loss in the actual raw count. -/
theorem marked_geometry_raw_bound_paid
    (Z τ D S ρ δ μ normfee C Q : ℝ) (I J : ℕ)
    (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hC : 0 ≤ C)
    (hD0 : 0 ≤ D) (hD : D ≤ 130) (hS : S ≤ Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0 ≤ δ ∧ δ ≤ Cycle63.Optimization.markedBinTop) (hρδ : Cycle63.Optimization.density δ ≤ ρ)
    (hρ : ρ ≤ 1)
    (hμ : μ ≤ Cycle63.Optimization.geometryLossCap) (hnorm : normfee ≤ μ/32) (hheight : τ*(J:ℝ) ≤ μ/8)
    (hbound : Q ≤ C*(1+geometryRawHeight Z τ I)^J*
      Z^(D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
        131*(156*markedRate+markedRawMesh+markedRate+markedRate)+markedPad*ρ-
        min (Cycle63.Optimization.markedGain δ S ((1-6*markedRootCutoff)*D))
          (D*markedRootCutoff*(6*(ρ+markedRate)-1-(Cycle63.Optimization.tailSlack))))) :
    Z^normfee*Q ≤ (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*
      Z^(D*ρ+δ*S-Cycle63.Optimization.markedGain δ S ((1-6*markedRootCutoff)*D)+Cycle63.Optimization.markedLoss) := by
  have hp : 0 < Z:=zero_lt_one.trans_le hZ
  let E:=D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
    131*(156*markedRate+markedRawMesh+markedRate+markedRate)+markedPad*ρ-
    min (Cycle63.Optimization.markedGain δ S ((1-6*markedRootCutoff)*D))
      (D*markedRootCutoff*(6*(ρ+markedRate)-1-(Cycle63.Optimization.tailSlack)))
  have he : E+normfee+τ*(J:ℝ) ≤
      D*ρ+δ*S-Cycle63.Optimization.markedGain δ S ((1-6*markedRootCutoff)*D)+Cycle63.Optimization.markedLoss :=
    marked_raw_exponent_paid D S ρ δ markedRawMesh μ normfee (τ*(J:ℝ))
      hD0 hD hS hδ hρδ hρ marked_raw_mesh_gates.2.2 hμ hnorm hheight
  calc
    Z^normfee*Q ≤ Z^normfee*(C*(1+geometryRawHeight Z τ I)^J*Z^E) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hp.le _)
    _ ≤ Z^normfee*(C*((1+2*Real.pi+6*(I+1:ℕ))^J*Z^(τ*(J:ℝ)))*Z^E) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      exact mul_le_mul_of_nonneg_left (geometry_raw_height_power hZ hτ I J) hC
    _ = (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*Z^(E+normfee+τ*(J:ℝ)) := by
      rw [Real.rpow_add hp,Real.rpow_add hp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg hC (pow_nonneg (by positivity) _))

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
