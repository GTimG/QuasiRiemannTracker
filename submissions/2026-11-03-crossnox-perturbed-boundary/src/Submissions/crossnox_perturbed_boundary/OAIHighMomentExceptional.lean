/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighMomentExceptional.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighMomentFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.PerturbedMomentTransport
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open UniqueFactorizationMonoid CenteredMomentDetectorDictionary
open CenteredExceptionalProfile CenteredExceptionalCount
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily ProbeFinalAssembly
local notation "O" => HeckeFamily.O

variable {gap : ℝ} {D : Parameters.PerturbedHighData gap}

def sourceExceptional (F : PerturbedSourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (perturbedFixedIdeal F) η)
    (fixedBadMask * idealGenerator 1) 1 u.val

lemma source_keep_iff (F : PerturbedSourceData D) (η : Character) (u : FreeRow) :
    initialKeep η (internalQ (perturbedFixedIdeal F) η) u.val ↔
      ¬sourceExceptional F η u := by
  exact and_iff_right u.property.1

def sourceExceptionalBound (F : ProbeFinalAssembly.PerturbedSourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (perturbedFixedIdeal F) η)).toFinset

lemma source_exceptional_norm (F : ProbeFinalAssembly.PerturbedSourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm≤sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (perturbedFixedIdeal F) η)
    (internalQ_ne_zero _ (perturbedFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (perturbedFixedIdeal_ne_top F) η)
    (inf_le_left.trans (perturbedFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem eventually_source_no_exceptional (F : ProbeFinalAssembly.PerturbedSourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤rowNorm u →
      ¬sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)<Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤_
    exact_mod_cast source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

end SevenEighths.PerturbedMomentTransport

end

end OAI
