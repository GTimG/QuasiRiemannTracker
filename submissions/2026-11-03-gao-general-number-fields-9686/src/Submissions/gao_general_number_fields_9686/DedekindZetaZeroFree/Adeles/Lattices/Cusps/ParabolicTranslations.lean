/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Lattices/Cusps/ParabolicTranslations.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Kubota.RootGroups.ConjugatedFiniteLevel

@[expose] public section

noncomputable section
open scoped NumberField MatrixGroups
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
set_option backward.isDefEq.respectTransparency false

theorem mem_parabolicL_of_rationalUnipotent_mem {F : Type} [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : KPCuspCharts.ParabolicData F S)
    (r : F) (hr : KPChamberBruhatTwoCells.rationalUnipotent F r ∈ S) : r ∈ D.L := by
  let A : Matrix.GeneralLinearGroup (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, r; 0, 1] (by simp [Matrix.det_fin_two])
  let g : S := ⟨KPChamberBruhatTwoCells.rationalUnipotent F r, hr⟩
  have hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) := rfl
  have hratio := D.ratioFormula g A hA (by simp [A])
  have h1 : D.ratio g = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa [A] using hratio.symm
  have hker : g ∈ D.ratio.ker := h1
  rw [← D.exact] at hker
  obtain ⟨x, hx⟩ := hker
  let y : D.L := Multiplicative.toAdd x
  have hi : Matrix.ProjGenLinGroup.mk A =
      (D.inclusion (Multiplicative.ofAdd y) : KPCuspArithmetic.PGL2 F) := by
    simpa [y, hx] using hA
  have hparam := (D.unipotentFormula y A hi).2.2
  have hy : r = (y : F) := by simpa [A] using hparam
  rw [hy]
  exact y.property

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
