/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/FinitePlaceNormalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.FiniteHaarTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.CurrentFiniteHaarBinding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
set_option backward.isDefEq.respectTransparency false

theorem integerVolume_eq (q : KPFinitePlace F) :
    PoissonS.integerVolume F q = localHalfDifferentFactor F q := by
  rw [PoissonS.integerVolume,
    FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent F q,
    zpow_natCast, localHalfDifferentFactor_eq_inv_sqrt F q,
    localDifferentNorm, Nat.cast_pow, one_div]

theorem finiteHaar_eq (N : MomentSources.TraceHaarTransport R) (q : KPFinitePlace F) :
    N.finiteHaar q = localNormalizedHaar F q := by
  letI := N.finiteHaar_add q
  let K := finiteCompletionIntegersPositiveCompacts F q
  have h := Measure.addHaarMeasure_unique (N.finiteHaar q) K
  have hO : (K : Set (q.adicCompletion F)) = {x | ‖x‖ ≤ (1 : ℝ)} := by
    rw [coe_finiteCompletionIntegersPositiveCompacts]
    ext x
    exact ⟨norm_le_one_of_mem_adicCompletionIntegers q,
      mem_adicCompletionIntegers_of_norm_le_one q⟩
  rw [hO, N.finite_mass q, integerVolume_eq] at h
  exact h

end DedekindZetaZeroFree.FourierContinuation.CurrentFiniteHaarBinding

end
