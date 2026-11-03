/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/BigCellSectionSmoothness.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem literal_raw_group_chart_contDiffOn_source (h : Functions F ζ hζ) (hh : Smooth F ζ hζ h)
    (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => h (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro z₀ hz₀
  obtain ⟨O, q, hO, hzO, hq, hqO, heq⟩ :=
    literal_group_chart_local_transition F ζ hζ g z₀ hz₀
  refine ⟨O, hO, hzO, ?_⟩
  have H := (hh.2.1
    (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z₀ * g)).comp hq hqO
  apply (H.congr (fun z hz => congrArg h (heq z hz))).mono
  exact Set.inter_subset_right

end DedekindZetaZeroFree.KPLiteralChamber

end
