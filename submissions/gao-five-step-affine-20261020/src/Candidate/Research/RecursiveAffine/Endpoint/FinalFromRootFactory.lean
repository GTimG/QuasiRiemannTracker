/- The two endpoint consumers share one literal initial-energy theorem.
Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.ChosenAffine
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.CountAffine.Supply

set_option autoImplicit false
namespace Cycle153Endpoint.FinalAssembly
noncomputable section
open Filter OAI.SevenEighths HeckeFamily CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource ProbePhysical
variable [RootMomentFactory]

/-- Choose the mesh before the genuine source data. The same literal
factory used on the detector side supplies the conjugated numerator. -/
theorem chosen_affine_from_root_factory : ChosenAffineInput := by
  intro hgap
  let ε:ℝ:=(HeckeZeroSupremum.beta-Arithmetic.theta)/20000
  have hε:0<ε := by dsimp [ε]; linarith
  have hεsmall:ε≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 := by
    dsimp [ε]; linarith
  obtain ⟨A,hmesh⟩:=exists_chosen_data_with_mesh hgap (RootMomentFactory.mesh_pos hε)
  obtain ⟨b,_hb,hs⟩:=CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  let bΦ:ℝ:=max 2 b
  have hbΦ:2≤ bΦ:=le_max_left _ _
  have hsΦ:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ:=by
    intro x hx
    exact (show x≤ b from hs hx).trans (le_max_right _ _)
  let η:=fixedSourcePrincipal A.F.S A.F.exclusions.prime
  have hη:η.modulus≤ Ideal.span {fixedBadMask}:=by
    change A.F.modulus≤ Ideal.span {fixedBadMask}
    exact Cycle153EndpointSource.source_modulus_le_mask A.F
  have hηunit : excluded η 1=η :=by
    dsimp only [η]
    unfold fixedSourcePrincipal HeckeRayFamily.character
    exact Cycle63InitialMass.excluded_one_ofResidue _ _ _ _
  obtain ⟨degree,Sd,C,hC,hactual⟩:=RootMomentFactory.moment A.F η hη hηunit
    ε A.P.mesh bΦ hε A.P.mesh_pos hmesh hbΦ (moment_parameter_gates hgap).2.2 baseline_beta
  refine ⟨A,bΦ,ε,hε,hεsmall,hsΦ,degree,Sd,C,hC,?_⟩
  exact hactual

/-- This conditional endpoint has exactly one analytic interface. The
public record theorem is exported only after constructing that interface
from the actual finite-depth source proof. -/
theorem allDirichlet_of_root_factory {q:ℕ}[NeZero q]
    (χ:DirichletCharacter ℂ q)(s:ℂ)(hs:Arithmetic.theta< s.re)
    (hexc:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  dirichlet_nonzero_of_chosen_affine
    Cycle153EndpointProbeFinalAssemblyCertifiedBands.actual_detector_affine_input
    chosen_affine_from_root_factory χ s hs hexc

theorem zeta_of_root_factory (s:ℂ)(hs:Arithmetic.theta< s.re) : riemannZeta s≠0 :=
  riemannZeta_nonzero_of_chosen_affine
    Cycle153EndpointProbeFinalAssemblyCertifiedBands.actual_detector_affine_input
    chosen_affine_from_root_factory s hs
end
end Cycle153Endpoint.FinalAssembly

#print axioms Cycle153Endpoint.FinalAssembly.allDirichlet_of_root_factory
#print axioms Cycle153Endpoint.FinalAssembly.zeta_of_root_factory
