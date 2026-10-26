/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A literal absolute second-column bound, uniform in every character, row and
Mellin height. The full modified coefficient is retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondWindow
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceAbsoluteEnvelope
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonWindowColumn
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentAbsoluteEnergy CenteredMomentFirstSectors
open CenteredMomentExceptionalAmplitudePair CenteredMomentHeckeExpansion CenteredMomentSmooth
open CenteredMomentExceptionalWholeWindow
local notation "O"=>HeckeFamily.O
local instance plainAbsoluteDecidable {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem modified_plain_absolute {ι:Type*}[Fintype ι]
    (s:Input ι)(modifier:Tuple ι→ℂ)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t:ℝ)(z:O):
    ‖modifiedPlainColumn s modifier C hC R seed L η t z‖≤
      (Real.sqrt (volume s.toData))⁻¹*
        ∑I∈finiteColumns (Fintype.piFinset s.pools),‖CoupledFirst.coefficient s modifier R seed I‖ := by
  classical
  let Q:=finiteColumns (Fintype.piFinset s.pools)
  let β:=fun I:Ideal O=>if IsCoprime C I ∧ L∣I then CoupledFirst.coefficient s modifier R seed (C*I) else 0
  have he:modifiedPlainColumn s modifier C hC R seed L η t z=
      (Real.sqrt (volume s.toData):ℂ)⁻¹*
        (∑I∈columns s C hC,β I*rowWeight η CenteredMomentSecondHeightFamily.fixedBadMask 1 z t I):=by
    unfold modifiedPlainColumn
    simp only [modifiedWindowCoefficient,mul_assoc]
    rw [rowPolynomial_factor]
    apply congrArg (fun w:ℂ=>(Real.sqrt (volume s.toData):ℂ)⁻¹*w)
    exact height_source_row η t (columns s C hC) β z
  rw [he,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hb:(∑I∈columns s C hC,‖β I*rowWeight η CenteredMomentSecondHeightFamily.fixedBadMask 1 z t I‖)≤
      ∑I∈columns s C hC,‖CoupledFirst.coefficient s modifier R seed (C*I)‖:=by
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    apply (mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all _ _ _ _ _ _)).trans
    dsimp only [β]
    split_ifs <;> simp only [norm_zero,le_refl,norm_nonneg]
  apply ((norm_sum_le _ _).trans hb).trans
  have hi:Function.Injective (fun I:Ideal O=>C*I):=fun I J h=>mul_left_cancel₀ hC.1 h
  have himage: (∑I∈(columns s C hC).image (fun I=>C*I),‖CoupledFirst.coefficient s modifier R seed I‖)=
      ∑I∈columns s C hC,‖CoupledFirst.coefficient s modifier R seed (C*I)‖ :=
    Finset.sum_image (fun I _ J _ h=>hi h)
  rw [←himage]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun I _ _=>norm_nonneg _)
  intro I hI
  obtain ⟨J,hJ,rfl⟩:=Finset.mem_image.mp hI
  exact (mem_residualPool C hC.1 Q J).mp hJ

/-- Pointwise square, in the same normalization as the second contraction. -/
theorem modified_plain_absolute_sq {ι:Type*}[Fintype ι]
    (s:Input ι)(modifier:Tuple ι→ℂ)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t:ℝ)(z:O):
    ‖modifiedPlainColumn s modifier C hC R seed L η t z‖^2≤
      (∑I∈finiteColumns (Fintype.piFinset s.pools),‖CoupledFirst.coefficient s modifier R seed I‖)^2/volume s.toData := by
  have h:=pow_le_pow_left₀ (norm_nonneg _) (modified_plain_absolute s modifier C hC R seed L η t z) 2
  apply h.trans_eq
  rw [mul_pow,inv_pow,Real.sq_sqrt (volume_pos s.toData).le]
  ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_plain_absolute
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_plain_absolute_sq
