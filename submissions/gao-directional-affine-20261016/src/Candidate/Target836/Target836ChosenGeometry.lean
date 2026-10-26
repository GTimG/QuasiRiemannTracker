/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target836.Target836SourceLiteral
import Candidate.Target836.Target836ChosenAffine

set_option autoImplicit false
namespace Target836.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle63InitialMass Target836SourceAssembly
open scoped SchwartzMap

/-- The chosen-source interface is exactly the literal geometry budget
followed by the proved physical-mass and affine assembly. The budget remains
an explicit analytic obligation; this adapter does not assert it. -/
theorem actual_affine_input_of_geometry (A : ChosenData) (bΦ δ τ ξ : ℝ)
    (hbΦ : 0< bΦ) (hδ : 0< δ) (hτ : 0< τ) (hξ : 0< ξ)
    (hδgap : δ≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000)
    (hsΦ : Function.support
      (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (hmesh : A.P.mesh≤ Cycle63FirstActual.comparisonMesh 1 1 (δ/2))
    (hbudget : Target836SourceAssembly.SourceLiteralAffineGeometryBudget A.F bΦ A.P.mesh (δ/4) τ ξ) :
    Numerator.Source.ActualAffineInput A := by
  have hgap : Arithmetic.theta< HeckeZeroSupremum.beta := by linarith
  have hβ:=moment_parameter_gates hgap
  obtain ⟨degree,S,C,hC,hbound⟩:=Target836SourceAssembly.weighted_source_affine_from_geometry A.F
    bΦ A.P.mesh δ τ ξ hbΦ A.P.mesh_pos hδ hτ hξ hmesh hβ.2.2 hβ.2.1 hbudget
  exact ⟨bΦ,δ,hδ,hδgap,hsΦ,degree,S,C,hC,hbound⟩

end
end Target836.FinalAssembly
#print axioms Target836.FinalAssembly.actual_affine_input_of_geometry
