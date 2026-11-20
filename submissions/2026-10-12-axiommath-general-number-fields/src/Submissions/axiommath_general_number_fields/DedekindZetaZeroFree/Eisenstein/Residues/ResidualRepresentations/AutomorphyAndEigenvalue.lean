/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/ResidualRepresentations/AutomorphyAndEigenvalue.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Residues.Regularity.CoreResidue
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.CasimirEigenvalue

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem coreResidue_native_eigen (x : V) (g : MomentSources.Group R) :
    KPMsGreenFlux.casimir F ζ hζ (coreResidue R P C x) g =
      KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
        coreResidue R P C x g := by
  obtain ⟨M, HR, HP, HH, n, U, m, w, B, Z, z, hz, heig, horth, hnative, hcus, he⟩ :=
    core_residue_hilbert_orthogonal_centers R P C x
  let a := fun i j => B i j 0
  have hpin : coreResidue R P C x = fun g ↦
      ResidualHilbertCenters.finiteCenterSum F ζ hζ M HR HP HH U m w a Z
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
    funext g
    exact (he g).trans (ResidualHilbertCenters.finiteCenterSum_lift
      F ζ hζ M HR HP HH U m w a Z g).symm
  rw [hpin]
  exact ResidualHilbertCenters.finiteCenterSum_native_eigen F ζ hζ M HR HP HH U m w a Z
    _ hnative g

theorem coreResidue_raw_automorphic (x : V) :
    KPLiteralRaw.Automorphic F ζ hζ (coreResidue R P C x) := by
  have hr := coreResidue_regular R P C x
  refine ⟨?_, hr.2⟩
  obtain ⟨M, HR, HP, HH, n, U, m, w, B, Z, z, hz, heig, horth, hnative, hcus, he⟩ :=
    core_residue_hilbert_orthogonal_centers R P C x
  let a := fun i j => B i j 0
  have hpin : coreResidue R P C x = fun g ↦
      ResidualHilbertCenters.finiteCenterSum F ζ hζ M HR HP HH U m w a Z
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
    funext g
    exact (he g).trans (ResidualHilbertCenters.finiteCenterSum_lift
      F ζ hζ M HR HP HH U m w a Z g).symm
  rw [hpin]
  exact ResidualHilbertCenters.finiteCenterSum_raw_smooth F ζ hζ M HR HP HH U m w a Z

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
