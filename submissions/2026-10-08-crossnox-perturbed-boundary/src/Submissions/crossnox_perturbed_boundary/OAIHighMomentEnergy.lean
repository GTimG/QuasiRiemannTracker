/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighMomentEnergy.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighMomentFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState
open ProbeDetectorPlainMarkedFineField ProbeDetectorPlainUnmarkedField
local notation "O" => HeckeFamily.O

def PerturbedPositiveFineSourceInput
    {gap : ℝ} {D : Parameters.PerturbedHighData gap}
    (F : PerturbedSourceData D) (mesh : ℝ) : Prop :=
  ∀ bΦ : ℝ, 0 < bΦ → ∃ degree : ℕ,
    ∃ seminorms : Finset (ℕ × ℕ),
      ∀ η₀ : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
        PositiveAt (α := Fin D.N) F.modulus ⊤ le_top
          (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4) bΦ 0 1
          mesh (33 / 50) (33 / 50) 2 (D.small / 4) (3 / 4)
          U η₀ (perturbedFixedIdeal F) degree seminorms C

theorem perturbed_plain_inputs
    {gap : ℝ} (D : Parameters.PerturbedHighData gap)
    (F : PerturbedSourceData D)
    (hβ : AsymmetricGeometry.boundary < HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    PerturbedPositiveFineSourceInput F
      (fineMesh 2 0 1 (3 / 4) (D.small / 4)) ∧
    (∃ degree : ℕ, ∃ control : Finset (ℕ × ℕ),
      ∀ η₀ : Character, ∃ A : ℝ, 0 < A ∧ ∀ᶠ U : ℝ in atTop,
        ZeroAt (internalQ (perturbedFixedIdeal F) η₀)
          (1 / 4) (9 / 4) radialSupportUpper 0 1 2
          (D.small / 4) U degree control A) := by
  have ht (bΦ : ℝ) (hbΦ : 0 < bΦ) :=
    certified_terminal F.modulus ⊤ le_top
      (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4)
      bΦ 0 1 (33 / 50) (33 / 50) 2 (3 / 4)
      (D.small / 4)
      (by norm_num) (by norm_num)
      (by norm_num) (by exact div_pos D.small_pos (by norm_num))
      (perturbed_detector_certified_band D F hβ hβhi bΦ hbΦ)
  have hactual (bΦ : ℝ) (hbΦ : 0 < bΦ) :
      ∃ degree : ℕ, ∃ control : Finset (ℕ × ℕ),
        ∀ η₀ : Character, ∃ Czero Cpositive : ℝ,
          0 < Czero ∧ 0 < Cpositive ∧ ∀ᶠ U : ℝ in atTop,
          ZeroAt (internalQ (perturbedFixedIdeal F) η₀)
            (1 / 4) (9 / 4) bΦ 0 1 2
            (D.small / 4) U degree control Czero ∧
          PositiveAt (α := Fin D.N) F.modulus ⊤ le_top
            (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4)
            bΦ 0 1 (fineMesh 2 0 1 (3 / 4) (D.small / 4))
            (33 / 50) (33 / 50) 2
            (D.small / 4) (3 / 4) U η₀
            (perturbedFixedIdeal F) degree control Cpositive := by
    obtain ⟨degree, control, hbound⟩ := ht bΦ hbΦ
    refine ⟨degree, control, ?_⟩
    intro η₀
    obtain ⟨Cz, Cp, hCz, hCp, hbound⟩ :=
      hbound η₀ (perturbedFixedIdeal F)
        (perturbedFixedIdeal_le_modulus F)
        (perturbed_fixed_gates F η₀).1
        (internalQ_ne_top _ (perturbedFixedIdeal_ne_top F) η₀)
        (perturbed_fixed_gates F η₀).2.2.2
    exact ⟨Cz, Cp, hCz, hCp,
      hbound.mono (fun U h => ⟨h.2.1, h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree, control, h⟩ := hactual bΦ hbΦ
    refine ⟨degree, control, ?_⟩
    intro η₀
    obtain ⟨Cz, Cp, hCz, hCp, h⟩ := h η₀
    exact ⟨Cp, hCp, h.mono (fun U h => h.2)⟩
  · obtain ⟨degree, control, h⟩ :=
      hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree, control, ?_⟩
    intro η₀
    obtain ⟨Cz, Cp, hCz, hCp, h⟩ := h η₀
    exact ⟨Cz, hCz, h.mono (fun U h => h.1)⟩

end SevenEighths.ProbeFinalAssembly

end

end OAI
