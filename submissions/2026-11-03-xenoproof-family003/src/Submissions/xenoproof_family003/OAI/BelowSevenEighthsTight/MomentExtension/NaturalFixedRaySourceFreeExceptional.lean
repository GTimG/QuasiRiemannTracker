/- UNVERIFIED adapters retaining original physical plain moment objects. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.NaturalFixedRaySourceFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ExceptionalRows

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

variable {Δ total margin recordMesh : ℝ} {D : _root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin recordMesh}

def sourceExceptionalBound_retuned (F : _root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (sourceFixedIdeal_retuned F) η)).toFinset

lemma source_exceptional_norm_retuned (F : _root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional_retuned F η u) :
    (Ideal.span {u.val}).absNorm≤sourceExceptionalBound_retuned F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (sourceFixedIdeal_retuned F) η)
    (internalQ_ne_zero _ (sourceFixedIdeal_ne_zero_retuned F) η)
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top_retuned F) η)
    (inf_le_left.trans (sourceFixedIdeal_le_72_retuned F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem eventually_source_no_exceptional_retuned (F : _root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤rowNorm u →
      ¬sourceExceptional_retuned F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound_retuned F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)<Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound_retuned F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤_
    exact_mod_cast source_exceptional_norm_retuned F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

theorem eventually_source_sector_gate_retuned (F : _root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤rowNorm u→ rowNorm u≤Z^(d-D.t) →
      ∀θ : RayQuotient.Characters F.modulus ⊤,
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      let χ:=(CenteredMomentNaturalRowSource.naturalRow η₀ u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top η₀ θ)
      χ.residue≠1 ∧ (χ.modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [eventually_source_no_exceptional_retuned F η,
    eventually_source_sector_capacity F.modulus ⊤ le_top F.S F.exclusions.prime η D.t D.t_pos]
    with Z hn hc
  intro label d u hlo hhi θ
  exact ⟨source_retained_sector_nonprincipal_retuned F _ u (hn label u hlo) θ,hc label d u hhi θ⟩

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

#print axioms OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.source_exceptional_norm_retuned
#print axioms OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.eventually_source_no_exceptional_retuned
#print axioms OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.eventually_source_sector_gate_retuned
