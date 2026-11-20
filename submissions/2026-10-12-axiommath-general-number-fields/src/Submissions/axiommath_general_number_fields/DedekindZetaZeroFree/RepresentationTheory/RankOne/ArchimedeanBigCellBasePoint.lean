/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/RankOne/ArchimedeanBigCellBasePoint.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw
open KPGlobalResidualConstruction
open scoped Topology

theorem archChart_base (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    archChart F ζ hζ (archBase F) = 1 := by
  unfold archChart
  dsimp only
  suffices ht : (⟨_, _⟩ : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) =
      (1 : RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
        (fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _)) Filter.cofinite) by
    rw [ht, map_one, map_one]
  apply Subtype.ext
  funext v
  cases v <;> simp [archBase] <;> rfl

end DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw

end
