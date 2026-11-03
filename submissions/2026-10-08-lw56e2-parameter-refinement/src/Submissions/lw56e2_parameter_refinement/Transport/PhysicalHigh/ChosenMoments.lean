/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/ChosenMoments.lean
Original SHA-256: 9cd89e2ae969763c34e14b10cad03d92b29ffed8173b17fc0927bc77091d4391
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.SourceMoments
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.ChosenMomentsCore
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.Parameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput

/-!
# Actual moments with a last-chosen height exponent

The moment degree is supplied by the arithmetic proof, uniformly over target
characters. Only then is the positive height exponent chosen. The resulting
height growth is absorbed into the already reserved high-side loss t.
-/

namespace LW56e2.Transport.PhysicalHigh
noncomputable section
open scoped Classical BigOperators
open Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification ProbeFinalAssembly ProbeHighRowFamily
open Parameters

/-- Chosen-height actual moment production. `P` was chosen after the slots;
its height choice is evaluated only after `actual_source_moments` returns J. -/
theorem actual_chosen_moments {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (N : ℕ) (ell : Fin N → ℝ) (hell : ∀ j, 0 < ell j)
    (hinj : Function.Injective ell)
    (t rmin ellMin allowance : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (P : DetectorScales t N rmin ellMin allowance)
    (hfine : ∀ j, ell j ≤ plainMesh t / 200)
    (cB kB cH kH : ℝ) (hcB : 0 < cB) (hkB : 0 < kB)
    (hcH : 0 < cH) (hkH : 0 < kH)
    (hbeta : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ 7 / 8) :
    ∃ τ : ℝ, 0 < τ ∧ τ < (1 / 200 : ℝ) / 2 ∧
      4 * τ < (1 / 200 : ℝ) * P.cost ∧ τ < t ∧
      2 * τ ≤ t ∧ τ * (2 + 4 * P.eps) < t ∧
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        1 < Z ∧ ∀ rows : Finset FreeRow,
        (∀ u ∈ rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
        ∀ d : ℝ, (1 / 200 : ℝ) ≤ d →
        ∀ a dmax slotMesh binWidth : ℝ, ∀ i : ℕ, ∀ z : ℂ,
        z.re = 17 / 50 → |z.im| ≤ Z ^ (2 * τ) →
        SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows ell
          (fun _ y => (F.w y : ℂ)) Z d a P.ε τ dmax 2 slotMesh binWidth i z 0
          (if 2 * a - 1 ≤ 5 / 6 then cB else cH)
          (if 2 * a - 1 ≤ 5 / 6 then kB else kH)
          (C * Z ^ t) (Z ^ (2 * τ)) t := by
  exact actual_chosen_moments_from_inputs F N ell hell hinj t rmin ellMin allowance ht ht1
    P hfine cB kB cH kH hcB hkB hcH hkH (actual_plain_inputs F N t ht hbeta hceiling)

end
end LW56e2.Transport.PhysicalHigh
