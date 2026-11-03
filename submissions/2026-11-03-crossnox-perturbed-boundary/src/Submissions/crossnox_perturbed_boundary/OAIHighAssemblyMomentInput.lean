/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighAssemblyMomentInput.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def PerturbedSourceMomentBound {gap : ℝ} {D : PerturbedHighData gap}
    (F : PerturbedSourceData D)
    (counts : CountParameters F.modulus ⊤ D.small) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀ rows : Finset FreeRow, ∀ d a : ℝ,
    (1 / 200 : ℝ) ≤ d → d ≤ 7 / 8 → 51 / 100 < a → a ≤ 7 / 8 →
    (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z ^ (d - D.small)) →
    ∀ i : ℕ, ∀ z : ℂ, z.re = 17 / 50 → |z.im| ≤ height →
    SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows
      D.ell (fun _ y => (F.w y : ℂ)) Z d a D.ε τ (7 / 8) 2
      ((1 + 6 * perturbedSlotLengthShift) * D.small) D.small i z 0
      (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
      (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
      C height D.small

lemma PerturbedSourceMomentBound.mono_constant
    {gap : ℝ} {D : PerturbedHighData gap} {F : PerturbedSourceData D}
    {counts : CountParameters F.modulus ⊤ D.small}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0 ≤ Z) (h : PerturbedSourceMomentBound F counts η Z τ C height)
    (hC : C ≤ C') :
    PerturbedSourceMomentBound F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh
  exact sourceMomentsAt_mono_constant F.modulus ⊤ le_top F.S
    F.exclusions.prime η rows D.ell (fun _ y => (F.w y : ℂ))
    Z d a D.ε τ (7 / 8) 2
    ((1 + 6 * perturbedSlotLengthShift) * D.small) D.small i z 0 _ _
    C C' height D.small hZ hC
    (h rows d a hd hd' ha ha' hrows i z hz hzh)

def RawPerturbedMomentInput : Prop :=
  ∀ _hβ : (AsymmetricGeometry.boundary : ℝ) < HeckeZeroSupremum.beta,
    ∀ D : PerturbedHighData
      (HeckeZeroSupremum.beta - (AsymmetricGeometry.boundary)),
    ∀ F : PerturbedSourceData D,
    ∀ counts : CountParameters F.modulus ⊤ D.small,
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        PerturbedSourceMomentBound F counts η Z τ
          (C * (1 + Z ^ (2 * τ)) ^ J) (Z ^ (2 * τ))

def ChosenPerturbedMomentInput : Prop :=
  ∀ _hβ : (AsymmetricGeometry.boundary : ℝ) < HeckeZeroSupremum.beta,
    ∃ D : PerturbedHighData
      (HeckeZeroSupremum.beta - (AsymmetricGeometry.boundary)),
    ∃ F : PerturbedSourceData D,
    ∃ counts : CountParameters F.modulus ⊤ D.small,
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        PerturbedSourceMomentBound F counts η Z τ
          (C * (1 + Z ^ (2 * τ)) ^ J) (Z ^ (2 * τ))

def FinePerturbedMomentInput : Prop :=
  ∀ _hβ : (AsymmetricGeometry.boundary : ℝ) < HeckeZeroSupremum.beta,
    ∃ mesh : ℝ → ℝ, (∀ small : ℝ, 0 < small → 0 < mesh small) ∧
      ∀ D : PerturbedHighData
          (HeckeZeroSupremum.beta - (AsymmetricGeometry.boundary)),
        (∀ j, D.ell j ≤ mesh D.small / 200) →
        ∀ F : PerturbedSourceData D,
        ∀ counts : CountParameters F.modulus ⊤ D.small,
          ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
            ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
              PerturbedSourceMomentBound F counts η Z τ
                (C * (1 + Z ^ (2 * τ)) ^ J) (Z ^ (2 * τ))

theorem chosen_perturbed_input_of_fine
    (h : FinePerturbedMomentInput) : ChosenPerturbedMomentInput := by
  intro hβ
  obtain ⟨mesh, hmesh, hmom⟩ := h hβ
  obtain ⟨D, hD⟩ := exists_perturbed_high_data_fine _
    (sub_pos.mpr hβ) mesh hmesh
  obtain ⟨F⟩ := exists_perturbed_source_data D
  obtain ⟨counts⟩ := perturbed_source_count_parameters F
  exact ⟨D, F, counts, hmom D hD F counts⟩

theorem chosen_perturbed_input_of_raw
    (h : RawPerturbedMomentInput) : ChosenPerturbedMomentInput := by
  intro hβ
  obtain ⟨D⟩ := exists_perturbed_high_data _ (sub_pos.mpr hβ)
  obtain ⟨F⟩ := exists_perturbed_source_data D
  obtain ⟨counts⟩ := perturbed_source_count_parameters F
  exact ⟨D, F, counts, h hβ D F counts⟩

theorem perturbed_chosen_data_height
    {gap : ℝ} (D : PerturbedHighData gap)
    (F : PerturbedSourceData D)
    (counts : CountParameters F.modulus ⊤ D.small)
    (J : ℝ) (hJ : 0 ≤ J)
    (hbound : ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        PerturbedSourceMomentBound F counts η Z τ
          (C * (1 + Z ^ (2 * τ)) ^ J) (Z ^ (2 * τ))) :
    ∃ τ : ℝ, 0 < τ ∧ τ < (1 / 200 : ℝ) / 2 ∧
      4 * τ < (1 / 200 : ℝ) * D.cost ∧ τ < D.small ∧
      2 * τ ≤ D.small ∧ τ * (2 + 4 * D.eps) < D.small ∧
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        PerturbedSourceMomentBound F counts η Z τ
          (C * Z ^ D.small) (Z ^ (2 * τ)) := by
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτJ, hτeps⟩ :=
    D.height_choice J hJ
  have hτ1 : τ ≤ 1 := by linarith
  refine ⟨τ, hτ, hτd, hτcost, hτt, by nlinarith,
    hτeps, ?_⟩
  intro η
  obtain ⟨C, hC, hbound⟩ := hbound η
  refine ⟨C * 2 ^ J, by positivity, ?_⟩
  filter_upwards [hbound τ hτ hτ1,
    eventually_ge_atTop (1 : ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith)
    (polynomial_height_absorption C Z τ J D.small
      hC.le hZ hτ.le hJ hτJ)

end SevenEighths.ProbeFinalAssembly

end

end OAI
