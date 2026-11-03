/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Profiles/SheetIntegralPowerBounds.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.RadialJetsAndLocalNorms
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.ProductSheetIntegralBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem sheet_product_power_majorant_integrals (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (_C : JointDigitDescentSources R N)
    (σ : ℝ) (hσ : -(1 / 4 : ℝ) < σ) (A : ℝ) (hA : max σ 0 < A)
    (M : ℝ) (hM : 0 < M) :
    letI : MeasurableSpace R.A.G1 := borel _;
    (∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ,
      Integrable (fun y : R.A.G1 => sheetProductPowerMajorant R M A
        (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u))) R.probe.domain.measure ∧
      (∫ y : R.A.G1, sheetProductPowerMajorant R M A
        (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u))
          ∂ R.probe.domain.measure) ≤ K * Real.exp (-σ * u)) ∧
    (∀ u : ℝ, ∃ s ∈ nhds u, ∃ E : R.A.G1 → ℝ,
      Integrable E R.probe.domain.measure ∧ ∀ᵐ y ∂ R.probe.domain.measure,
        ∀ t ∈ s, sheetProductPowerMajorant R M A
          (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t)) ≤ E y) := by
  exact SheetRescaling.product_sheet_integrals R N σ hσ A hA M hM
end DedekindZetaZeroFree.ThetaExpansion

end
