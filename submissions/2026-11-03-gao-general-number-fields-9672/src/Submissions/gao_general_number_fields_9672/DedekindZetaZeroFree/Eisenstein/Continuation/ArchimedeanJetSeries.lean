/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/ArchimedeanJetSeries.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanSectionRegularity
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Analysis.Analytic.SmoothSeries.ScalarMultiplication

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeChartProduct renaming domain_open → domain_open
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming native_word_smooth → native_word_smooth
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming actual_eq_word → actual_eq_word
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word_add → word_add
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word_smul → word_smul

def space : Submodule ℂ (KPLiteralRaw.G F ζ hζ → ℂ) where
  carrier := {f | ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun x => f (g * archChart F ζ hζ x)) (archDomain F)}
  zero_mem' := fun _ => contDiffOn_const
  add_mem' := fun hf hh g => (hf g).add (hh g)
  smul_mem' := fun c f hf g => contDiffOn_const.smul (hf g)

abbrev Observation := (archDomain F) × (ℕ → ArchCoordinates F)
abbrev Index := KPLiteralRaw.G F ζ hζ × ℕ

def jets (i : Index F ζ hζ) : space F ζ hζ →ₗ[ℂ] C(Observation F, ℂ) where
  toFun f := ⟨fun p => iteratedFDeriv ℝ i.2
    (fun x => f.val (i.1 * archChart F ζ hζ x)) p.1.val (fun j => p.2 j.val), by
      have hc := (ContinuousOn.continuousOn_iteratedFDeriv (f.property i.1)
        (domain_open F) (by simp : (i.2 : ℕ∞ω) ≤ ∞)).restrict
      exact (hc.comp continuous_fst).eval (by fun_prop)⟩
  map_add' f h := by
    ext p
    change iteratedFDeriv ℝ i.2
      ((fun x => f.val (i.1 * archChart F ζ hζ x)) +
       (fun x => h.val (i.1 * archChart F ζ hζ x))) p.1.val _ = _
    rw [iteratedFDeriv_add_apply
      (((f.property i.1).contDiffAt ((domain_open F).mem_nhds p.1.property)).of_le (by simp))
      (((h.property i.1).contDiffAt ((domain_open F).mem_nhds p.1.property)).of_le (by simp))]
    rfl
  map_smul' c f := by
    ext p
    change iteratedFDeriv ℝ i.2
      (c • (fun x => f.val (i.1 * archChart F ζ hζ x))) p.1.val _ = _
    rw [iteratedFDeriv_const_smul_apply
      (((f.property i.1).contDiffAt ((domain_open F).mem_nhds p.1.property)).of_le (by simp))]
    rfl

def word (w : List (Fin (groupDimension F))) : space F ζ hζ →ₗ[ℂ] space F ζ hζ where
  toFun f := ⟨actualRightWord F ζ hζ w f.val, native_word_smooth F ζ hζ _ f.property w⟩
  map_add' f h := by
    apply Subtype.ext
    simp_rw [actual_eq_word]
    exact word_add F ζ hζ _ _ f.property h.property _
  map_smul' c f := by
    apply Subtype.ext
    simp_rw [actual_eq_word]
    exact word_smul F ζ hζ c _ f.property _

end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries

end
