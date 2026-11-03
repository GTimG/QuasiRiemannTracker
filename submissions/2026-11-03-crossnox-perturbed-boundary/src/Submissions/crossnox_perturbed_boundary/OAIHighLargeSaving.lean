/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighLargeSaving.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighLargeTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.LargeSaving

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open AsymmetricGeometry
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_tail_arbitrary_saving_with_perturbed_lengths
    (K : ℕ) (δ a b B ζ t saving : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) (hζ : 0 < ζ) (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (hB : 0 ≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (hfirst : FirstTail (1 / 4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) :
    ∃ r C : ℝ, (17 / 50 : ℝ) ≤ r ∧ 0 < C ∧
      ∀ (η : Character) (Z : ℝ), 1 ≤ Z → ∀ R : ℕ → Finset FreeRow,
      (∀ n u, u ∈ R n → u.val ≠ 1 ∧
        Z ^ (rowBase + 3 * t / 2 + ζ) * (2 : ℝ) ^ n ≤
          ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ∧
        ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤
          2 * (Z ^ (rowBase + 3 * t / 2 + ζ) * (2 : ℝ) ^ n)) →
      ∀ (T : Fin K → Finset PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S),
      (∀ P : (∀ i, T i), Function.Injective (fun i => (P i).val)) →
      ∀ length : Fin K → ℝ, (∀ i, 0 ≤ length i) →
      (∑ i, length i) = (1 / 6 : ℝ) + t →
      ∀ W : Fin K → ℝ → ℂ, (∀ i, Function.support (W i) ⊆ Icc a b) →
      (∀ i y, ‖W i y‖ ≤ B) →
      Summable (fun n => absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W
        (fun i => Z ^ (length i)) W0 W1
        (Z ^ (xBase - t / 2 : ℝ)) (Z ^ (yBase - t / 2 : ℝ)) Z 2 2 r) ∧
      (∑' n, absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W
        (fun i => Z ^ (length i)) W0 W1
        (Z ^ (xBase - t / 2 : ℝ)) (Z ^ (yBase - t / 2 : ℝ)) Z 2 2 r) ≤
        C * (η.modulus.absNorm : ℝ) ^ δ * Z ^ (-saving) := by
  obtain ⟨r, hr, hr', hpower⟩ :=
    exists_large_tail_line ζ δ (saving + (33 / 20 + 3 * δ / 2) * t) hζ
  obtain ⟨C, hC, hmain⟩ :=
    large_physical_dyads_summable_with_perturbed_lengths K δ a b B r ζ t
      hδ hδ' hr hr' hζ ht ha hb hB S hS hmax hfirst
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨r, C, hr, hC, ?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hs, hb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  refine ⟨hs, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hskewCost : 0 ≤ skew * (1 / 2 + (8 / 5 + δ)) :=
    mul_nonneg bound_skew.1 (by linarith)
  simp only [rowBase]
  nlinarith [hpower, hskewCost]

end SevenEighths.ProbeHighRowFamily
end

end OAI
