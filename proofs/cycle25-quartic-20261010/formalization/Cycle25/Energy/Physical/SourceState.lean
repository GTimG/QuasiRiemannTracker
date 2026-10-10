import OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Cycle25.Assembly.SourceData
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open UniqueFactorizationMonoid CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {D : Cycle25.Weighted.MomentData}

def weighted_sourceFixedIdeal (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma weighted_sourceFixedIdeal_ne_zero (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma weighted_sourceFixedIdeal_ne_top (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus ≤ Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : weighted_sourceFixedIdeal F ≤ Ideal.span {goodLambda})))

lemma weighted_sourceFixedIdeal_le_modulus (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F ≤ F.modulus := inf_le_left
lemma weighted_sourceFixedIdeal_le_72 (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F ≤ Ideal.span {(72:O)} := inf_le_right

def weighted_sourceExceptional (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (weighted_sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

def weighted_sourceExceptionalBound (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (weighted_sourceFixedIdeal F) η)).toFinset

lemma weighted_source_exceptional_norm (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character)
    (u : FreeRow) (hu : weighted_sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm ≤ weighted_sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (weighted_sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

lemma weighted_source_keep_iff (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val↔¬weighted_sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma weighted_source_fixed_gates (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    internalQ (weighted_sourceFixedIdeal F) η≠0 ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ F.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ η.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)⟩

end SevenEighths.Cycle25WeightedNumeratorPhysical

end

end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
