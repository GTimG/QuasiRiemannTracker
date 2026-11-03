/- UNVERIFIED wrappers around ORIGINAL exceptional rows and energy states. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.NaturalFixedRaySourceFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.State
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

variable {Δ L margin mesh : ℝ}{D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh}

theorem source_label_modulus_eventually_retuned (F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)
    (η:Character)(δ:ℝ)(hδ:0<δ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤d→
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^δ:=by
  have hc:∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤Z^((1/200)*δ):=by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro label d hd
  apply (hz label).trans
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right hd hδ.le)

lemma source_keep_iff_retuned (F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (sourceFixedIdeal_retuned F) η) u.val↔¬sourceExceptional_retuned F η u:=by
  exact and_iff_right u.property.1

lemma source_fixed_gates_retuned (F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(η:Character):
    internalQ (sourceFixedIdeal_retuned F) η≠0 ∧
    internalQ (sourceFixedIdeal_retuned F) η≤F.modulus ∧
    internalQ (sourceFixedIdeal_retuned F) η≤η.modulus ∧
    internalQ (sourceFixedIdeal_retuned F) η≤Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (sourceFixedIdeal_ne_zero_retuned F) η,
    inf_le_left.trans (sourceFixedIdeal_le_modulus_retuned F),inf_le_right,
    inf_le_left.trans (sourceFixedIdeal_le_72_retuned F)⟩

theorem source_energy_split_state_retuned (F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(η:Character)
    (rows:Finset FreeRow)(f:FreeRow→ℂ):
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>initialKeep η (internalQ (sourceFixedIdeal_retuned F) η) u.val),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional_retuned F η),‖f u‖^2:=by
  simpa only [source_keep_iff_retuned] using source_energy_split_retuned F η rows f

theorem source_initial_states_retuned (F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D):
    ∃bΦ:ℝ,0<bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d:ℝ,(1/200:ℝ)≤d→
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label;
      ∃s:NaturalState (Z^d) 0 bΦ,
        s.character=η₀ ∧ s.fixedModulus=internalQ (sourceFixedIdeal_retuned F) η₀ ∧
        s.puncture=1 ∧ s.radial.profile=radialMajorant ∧ s.radial.scale=Z^d ∧
        s.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal_retuned F) η₀) ∧
        s.rowWidth=1 ∧ s.characterWidth=δ ∧ s.width=1+δ:=by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually_retuned F η δ hδ] with Z hz
  intro label d hd
  have hd0:0<d:=by linarith
  have hU:1≤Z^d:=(Real.one_lt_rpow hz.1 hd0).le
  dsimp only
  refine ⟨initialState (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
    (internalQ (sourceFixedIdeal_retuned F) (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label))
    radialMajorant bΦ (Z^d) δ hU hδ.le hs
    radialMajorant_nonneg (hz.2 label d hd),?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end SevenEighths.CenteredMomentDetectorEnergyInitialState

end

end OAI

#print axioms OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.source_label_modulus_eventually_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.source_keep_iff_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.source_fixed_gates_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.source_energy_split_state_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.source_initial_states_retuned
