import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
import Cycle25.Assembly.SourceData
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalFixedRaySource Cycle25ProbeFinalAssembly
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

end SevenEighths.Cycle25CenteredMomentNaturalFixedRaySource

end

end OAI
