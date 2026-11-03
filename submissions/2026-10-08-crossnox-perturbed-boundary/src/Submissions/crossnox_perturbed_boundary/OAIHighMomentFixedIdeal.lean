/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighMomentFixedIdeal.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighMomentCertificate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def perturbedFixedIdeal {gap : ℝ} {D : Parameters.PerturbedHighData gap}
    (F : PerturbedSourceData D) : Ideal O :=
  F.modulus ⊓ Ideal.span {(72 : O)}

lemma perturbedFixedIdeal_ne_zero
    {gap : ℝ} {D : Parameters.PerturbedHighData gap}
    (F : PerturbedSourceData D) : perturbedFixedIdeal F ≠ 0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0))

lemma perturbedFixedIdeal_ne_top
    {gap : ℝ} {D : Parameters.PerturbedHighData gap}
    (F : PerturbedSourceData D) : perturbedFixedIdeal F ≠ ⊤ := by
  have hmem : Ideal.span {goodLambda} ∈ F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda} ∈
      ({Ideal.span {goodLambda}, Ideal.span {(2 : O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus ≤ Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O => P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top
    (top_le_iff.mp (h ▸ (inf_le_left.trans hle :
      perturbedFixedIdeal F ≤ Ideal.span {goodLambda})))

lemma perturbedFixedIdeal_le_modulus
    {gap : ℝ} {D : Parameters.PerturbedHighData gap}
    (F : PerturbedSourceData D) : perturbedFixedIdeal F ≤ F.modulus :=
  inf_le_left

lemma perturbedFixedIdeal_le_72
    {gap : ℝ} {D : Parameters.PerturbedHighData gap}
    (F : PerturbedSourceData D) :
    perturbedFixedIdeal F ≤ Ideal.span {(72 : O)} :=
  inf_le_right

lemma perturbed_fixed_gates
    {gap : ℝ} {D : Parameters.PerturbedHighData gap}
    (F : PerturbedSourceData D) (η : Character) :
    internalQ (perturbedFixedIdeal F) η ≠ 0 ∧
    internalQ (perturbedFixedIdeal F) η ≤ F.modulus ∧
    internalQ (perturbedFixedIdeal F) η ≤ η.modulus ∧
    internalQ (perturbedFixedIdeal F) η ≤ Ideal.span {(72 : O)} :=
  ⟨internalQ_ne_zero _ (perturbedFixedIdeal_ne_zero F) η,
    inf_le_left.trans (perturbedFixedIdeal_le_modulus F),
    inf_le_right,
    inf_le_left.trans (perturbedFixedIdeal_le_72 F)⟩

theorem perturbed_source_label_modulus_eventually
    {gap : ℝ} {D : Parameters.PerturbedHighData gap}
    (F : PerturbedSourceData D) (η : Character)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀ d : ℝ, (1 / 200 : ℝ) ≤ d →
        ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm : ℝ)
          ≤ (Z ^ d) ^ δ := by
  have hc : ∀ᶠ Z : ℝ in atTop,
      ∀ label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
        ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm : ℝ)
          ≤ Z ^ ((1 / 200) * δ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually
      (eventually_ge_atTop _)
  filter_upwards [hc, eventually_gt_atTop (1 : ℝ)] with Z hz hZ
  refine ⟨hZ, ?_⟩
  intro label d hd
  apply (hz label).trans
  rw [← Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le
    (mul_le_mul_of_nonneg_right hd hδ.le)

end SevenEighths.ProbeFinalAssembly

end

end OAI
