/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/FlatSectionLinearRelations.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.CompactAndFlatSections
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.KPLiteralTensorEquivariance.FiniteClearedCovariance
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem flat_finite_combination_of_zero
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (n : ℕ) (d : Fin n → ℂ)
    (v : Fin n → Flat F ζ hζ K)
    (hzero : ∀ g, f.val 0 g = ∑ i, d i * (v i).val 0 g) :
    ∀ z g, f.val z g = ∑ i, d i * (v i).val z g := by
  intro z g
  simp_rw [← KPLiteralChamber.compactExtension_eq_flat F ζ hζ K hK,
    KPLiteralChamber.compactExtension]
  simp_rw [mul_left_comm (d _)]
  rw [← Finset.mul_sum, hzero]

end DedekindZetaZeroFree.KPLiteralTensorEquivariance.FiniteClearedCovariance

end
