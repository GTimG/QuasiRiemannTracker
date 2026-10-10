import WeightedQRH.HighRows.WeightedSourceLoss
import WeightedQRH.HighRows.ConditionalFinal

/-! Final quantifier-preserving assembly of the actual integrated weighted
source estimate.  The analytic input below is explicit and is not asserted
by this module.  The transformation adds only the two external integrals
and the actual source normalizer. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.WeightedHighFinalAssembly
open HeckeFamily ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands

/-- The literal integrated source target, with its height degree chosen
before the contour height parameter and its constant independent of C0. -/
def IntegratedFullWAnalyticInput : Prop :=
  ∀_hβ : WeightedQRH.theta < HeckeZeroSupremum.beta,
  ∀D : WeightedQRH.HighParameters.HighData (HeckeZeroSupremum.beta-WeightedQRH.theta),
  (∀j,D.ell j ≤ weighted_detectorMesh D.t/200) →
  ∀F : WeightedSourceData D.toMomentData,
  ∀counts : CountParameters F.modulus ⊤ D.t,
  ∃Jw : ℝ,0 ≤ Jw ∧
  ∀τ : ℝ,0 < τ → τ < (1/200:ℝ)/2 → 4*τ < (1/200)*D.cost →
    τ < D.t → 2*τ ≤ D.t → τ*(2+4*D.eps) < D.t → 2*τ*(1+Jw) ≤ D.t →
  ∀n : ℕ,∀η : Character,∃Cw : ℝ,0 ≤ Cw ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1 ≤ C0 →
    weighted_SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
    IntegratedWeightedCellsAt D F η Z τ n Cw C0

/-- Integrating and normalizing preserves every required uniformity,
including a fixed degree chosen before tau and linear dependence on C0. -/
theorem fullW_input_of_integrated_input (hinput : IntegratedFullWAnalyticInput) :
    FullWAnalyticInput := by
  intro hβ D hfine F counts
  obtain ⟨Jw,hJw,hinput⟩ := hinput hβ D hfine F counts
  obtain ⟨C,hC,hfinish⟩ := fullWCellsAt_of_integrated D F
  refine ⟨Jw,hJw,?_⟩
  intro τ hτ hτsmall hτcost hτt hτ2 hτeps hτJ n η
  obtain ⟨Cw,hCw,hinput⟩ := hinput τ hτ hτsmall hτcost hτt hτ2 hτeps hτJ n η
  refine ⟨C*Cw,mul_nonneg hC.le hCw,?_⟩
  filter_upwards [hinput,hfinish τ hτ n] with Z hi hf
  intro C0 hC0 hmom
  exact hf η Cw C0 hCw (zero_le_one.trans hC0) (hi C0 hC0 hmom)

end SevenEighths.WeightedHighFinalAssembly
end
end OAI
