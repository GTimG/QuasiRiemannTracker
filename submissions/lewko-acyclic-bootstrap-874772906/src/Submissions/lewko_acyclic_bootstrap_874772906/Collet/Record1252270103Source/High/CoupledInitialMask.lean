/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The initial whole-column coprimality mask is inserted without changing the row.
This is mask algebra for the actual coefficient, not a modified moment estimate. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledInitialRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledInitial
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentHeckeExpansion
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceRectangleMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentCommonRadialData
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open QRH.Record1252270103Restoration OAI.SevenEighths.Record1252270103Source
open CoupledFirst
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledInitialMaskDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma initial_row_mask (η:Character)(R I:Ideal O)(A z:O)(t:ℝ) :
    (if IsCoprime I R then (1:ℂ) else 0)*
      rowWeight η (fixedBadMask*idealGenerator R) A z t I=
      rowWeight η (fixedBadMask*idealGenerator R) A z t I := by
  by_cases h:IsCoprime I R
  · simp only [h,ite_true,one_mul]
  · have hh:=rowWeight_ideal_mask η fixedBadMask A z t
      (dvd_mul_right goodLambda 2) (dvd_mul_left 2 goodLambda) R I
    rw [if_neg h,zero_mul] at hh
    rw [if_neg h,zero_mul,←hh]

lemma centered_source_initial_mask (s:Input ι)(modifier:Tuple ι→ℂ)(R:Ideal O)(A z:O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),
      coefficient s modifier R 1 I*rowWeight s.η (fixedBadMask*idealGenerator R) A z s.t I)=
    ∑I∈finiteColumns (Fintype.piFinset s.pools),
      coefficient s modifier 1 1 I*rowWeight s.η (fixedBadMask*idealGenerator R) A z s.t I := by
  unfold coefficient
  rw [finite_column_regroup,finite_column_regroup]
  apply Finset.sum_congr rfl
  intro v hv
  unfold tupleCoefficient profileCoefficient
  simp only [one_mul,isCoprime_one_right,ite_true,mul_one,one_dvd]
  have h:=initial_row_mask s.η R (finiteTupleProduct v) A z s.t
  calc
    _ = (modifier v*(∏j,s.ν j (v (Sum.inl j))*s.W j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/s.P j))*
          CenteredMomentRectangle.idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂
            (v (Sum.inr 0)) (v (Sum.inr 1)))*
        ((if IsCoprime (finiteTupleProduct v) R then (1:ℂ) else 0)*
          rowWeight s.η (fixedBadMask*idealGenerator R) A z s.t (finiteTupleProduct v)) := by ring
    _ = _ := by rw [h];ring

/-- Literal initial row at m=fixedBadMask*genR and its actual reference scale. -/
theorem squarefree_initial_row_difference (s:Input ι)(R:Ideal O)(A z:O)
    (b:ℝ)(hb₁:s.b₁≤b)(hb₂:s.b₂≤b) :
    squarefreePositiveSlotRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b s.slots
      (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t s.X₁ s.X₂-
    squarefreePositiveSlotRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b s.slots
      (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t s.Y₁ s.Y₂=
    (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      ∑I∈finiteColumns (Fintype.piFinset s.pools),
        coefficient s (sourceModifier 1 1 1 (fun _=>1)) R 1 I*
          rowWeight s.η (fixedBadMask*idealGenerator R) A z s.t I := by
  rw [centered_source_initial_mask]
  exact squarefree_row_difference s _ A z b hb₁ hb₂

end
end QRH.Record1252270103Source.High.CoupledInitial
#print axioms QRH.Record1252270103Source.High.CoupledInitial.initial_row_mask
#print axioms QRH.Record1252270103Source.High.CoupledInitial.squarefree_initial_row_difference
