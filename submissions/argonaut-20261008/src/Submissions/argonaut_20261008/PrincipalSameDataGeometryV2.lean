import Submissions.argonaut_20261008.PrincipalGeometryPerturbedV2
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedPrincipalPerCharacterInterfaces

namespace OAI.SevenEighths.LocalPrincipalSameDataGeometryV2
noncomputable section

/-!
Exact definitional/numerical bridges between the V2 principal geometry and the
already fixed high-frontier consumer geometry.  These lemmas do not introduce
new data or estimates; they identify the two independently named copies of the
same frozen constants.
-/

/-- The V2 total compensation length is the exact total used by the target
`EulerPrincipalRawPerCharacterAt` interface. -/
lemma E_eq_frontier_totalE :
    LocalPrincipalGeometryV2.E = HighFrontierTargets.totalE := by
  norm_num [LocalPrincipalGeometryV2.E,
    Parameters.perturbedTotalE, Parameters.perturbedRho,
    HighFrontierTargets.totalE, HighFrontierTargets.rho]



lemma frontier_totalE_eq_central_totalE :
    HighFrontierTargets.totalE = PerturbedCentral.totalE := by
  norm_num [HighFrontierTargets.totalE, HighFrontierTargets.rho,
    PerturbedCentral.totalE, PerturbedCentral.rho0]

/-- The V2 x-scale is the exact source x-scale of the common probe. -/
lemma lx_eq_central_sourceLx :
    LocalPrincipalGeometryV2.lx = PerturbedCentral.sourceLx := by
  norm_num [LocalPrincipalGeometryV2.lx, LocalPrincipalGeometryV2.rho,
    Parameters.perturbedRho,
    PerturbedCentral.sourceLx, PerturbedCentral.rho0]

/-- The V2 y-scale is the exact source y-scale of the common probe. -/
lemma ly_eq_central_sourceLy :
    LocalPrincipalGeometryV2.ly = PerturbedCentral.sourceLy := by
  norm_num [LocalPrincipalGeometryV2.ly, LocalPrincipalGeometryV2.rho,
    Parameters.perturbedRho,
    PerturbedCentral.sourceLy, PerturbedCentral.rho0]

/-- The local analytic boundary is the exact central/high-frontier boundary. -/
lemma analyticBoundaryB0_eq_central_boundary :
    analyticBoundaryB0 = PerturbedCentral.boundary := by
  norm_num [analyticBoundaryB0,
    PerturbedCentral.boundary, PerturbedCentral.rho0]

lemma analyticBoundaryB0_eq_sigmaBoundary :
    analyticBoundaryB0 = HighFrontierTargets.sigmaBoundary := by
  norm_num [analyticBoundaryB0,
    HighFrontierTargets.sigmaBoundary, HighFrontierTargets.rho]

lemma central_boundary_eq_sigmaBoundary :
    PerturbedCentral.boundary = HighFrontierTargets.sigmaBoundary := by
  rw [← analyticBoundaryB0_eq_central_boundary,
    analyticBoundaryB0_eq_sigmaBoundary]

/-- The constructor total, central total and high-frontier total are literally
the same frozen number. -/
lemma E_eq_central_totalE :
    LocalPrincipalGeometryV2.E = PerturbedCentral.totalE := by
  norm_num [LocalPrincipalGeometryV2.E,
    Parameters.perturbedTotalE, Parameters.perturbedRho,
    PerturbedCentral.totalE, PerturbedCentral.rho0]

/-- The height identity used by the physical remainder agrees with the central
consumer's fixed physical height. -/
lemma H_eq_central_physicalHeight :
    LocalPrincipalGeometryV2.H = PerturbedCentral.physicalHeight := by
  norm_num [LocalPrincipalGeometryV2.H,
    Parameters.perturbedHeight, Parameters.perturbedRho,
    PerturbedCentral.physicalHeight, PerturbedCentral.rho0]

end
end OAI.SevenEighths.LocalPrincipalSameDataGeometryV2
