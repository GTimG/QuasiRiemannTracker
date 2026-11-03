/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/CompactPicture/ArchimedeanRootCovariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.Archimedean.BorelCharacter
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Archimedean.MatrixInsertion

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPLiteralScalarHCLocalCovariance
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCSliceCharts
open KPCplxCharacterHaar
open KPGlobalTorusBorelTwistCompatibility
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming complexSectionHom → complexSectionHom

variable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (C : ModelData F ζ hζ) (f : Flat F ζ hζ K)

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry renaming arch_center → arch_center

theorem productModel_arch_character (z : KPGlobalTorusFunctionData.TorusArch F) :
    ∃ t : (productModel F ζ hζ C).H,
      t.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ z ∧
      (productModel F ζ hζ C).character t =
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ t.val) := by
  obtain ⟨c, hc, hχ⟩ := arch_center F ζ hζ z
  let t : (productModel F ζ hζ C).H :=
    ⟨c.val, KPGlobalProductPolarizationCharacter.center_le_B F ζ hζ C c.property⟩
  refine ⟨t, hc, ?_⟩
  change KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment t = _
  rw [KPGlobalProductPolarizationCharacter.lambdaB_extends_center F ζ hζ C C.adjustment t c rfl]
  exact hχ

open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion

end DedekindZetaZeroFree.KPLiteralScalarHCLocalCovariance

end
