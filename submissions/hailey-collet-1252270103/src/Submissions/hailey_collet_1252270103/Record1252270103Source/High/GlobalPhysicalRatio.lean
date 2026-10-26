/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact ratio grouping of actual modified first blocks and joint contraction.
Adapted from pinned Cycle61 RatioBins and JointBlock; all original labels retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstMellin
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSectorLocalization CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic
open Cycle61InitialMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _
/-- An exact dyadic ratio index, independent of any first-label envelope. -/
def sourceRatioIndex (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) : ℤ :=
  (q.2.2 0).val+(q.2.2 1).val-(q.2.2 2).val-(q.2.2 3).val

def sourceRatioBins (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) : Finset ℤ :=
  Finset.univ.image (sourceRatioIndex s modifier R seed K Z ξ)

abbrev SourceRatioFiber (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (r : ℤ) :=
  {q : SourceCoordinate s modifier R seed K Z ξ // sourceRatioIndex s modifier R seed K Z ξ q=r}

omit [DecidableEq ι] in
lemma actual_source_ratio (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) :
    dyadicScale (q.2.2 0)*dyadicScale (q.2.2 1)/
      (dyadicScale (q.2.2 2)*dyadicScale (q.2.2 3)) =
      dyadicScale (sourceRatioIndex s modifier R seed K Z ξ q) := by
  simp only [sourceRatioIndex,dyadicScale,zpow_sub₀ (by norm_num : (2:ℝ)≠0),
    zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  ring

omit [DecidableEq ι] in
lemma actual_source_ratio_fiber (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (r : ℤ) (q : SourceRatioFiber s modifier R seed K Z ξ r) :
    dyadicScale (q.val.2.2 0)*dyadicScale (q.val.2.2 1)/
      (dyadicScale (q.val.2.2 2)*dyadicScale (q.val.2.2 3)) = dyadicScale r := by
  rw [actual_source_ratio,q.property]

/-- Exact physical mass as a sum of norms of full first-label ratio groups.
Every phase has norm at most one; all first labels remain inside each fiber. -/
theorem actual_physical_mass_ratio_groups (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s modifier R seed
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ =
    ∑r∈sourceRatioBins s modifier R seed K Z ξ,
      ‖∑q : SourceRatioFiber s modifier R seed K Z ξ r,
        normPhase (coordinateBlock s modifier R seed W K Z ξ q.val)*
          coordinateBlock s modifier R seed W K Z ξ q.val‖ := by
  rw [actual_physical_mass_joint_sum]
  simp_rw [normPhase_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  simp_rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun q (hq : q∈(Finset.univ : Finset (SourceCoordinate s modifier R seed K Z ξ))) =>
      Finset.mem_image_of_mem (sourceRatioIndex s modifier R seed K Z ξ) hq)]
  apply Finset.sum_congr rfl
  intro r _
  exact (Finset.sum_subtype (Finset.univ.filter (fun q : SourceCoordinate s modifier R seed K Z ξ =>
    sourceRatioIndex s modifier R seed K Z ξ q=r))
    (fun q => by simp) (fun q => ‖coordinateBlock s modifier R seed W K Z ξ q‖))

def ratioFirstSource (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (r : ℤ) (q : SourceRatioFiber s modifier R seed K Z ξ r) :=
  originalFirstBlock s modifier R seed K Z ξ hK q.val

def ratioFirstPhase (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ)
    (r : ℤ) (q : SourceRatioFiber s modifier R seed K Z ξ r) :=
  normPhase (coordinateBlock s modifier R seed W K Z ξ q.val)

/-- Actual physical mass is contracted over each genuine ratio group, with
all first labels inside the matched column energy. -/
theorem actual_physical_mass_joint_contraction (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
      (E : ℤ → ℝ), (∀r∈sourceRatioBins s modifier R seed K Z ξ, 0≤E r) →
      (∀r∈sourceRatioBins s modifier R seed K Z ξ, ∀t : ℝ,
        firstJointEnergyPair (ratioFirstSource s modifier R seed K Z ξ hK r)
          (ratioFirstPhase s modifier R seed W K Z ξ r) (fun _ => logAnnulus) t ≤
          E r*(1+‖t‖)^J) →
      physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ ≤
        C*∑r∈sourceRatioBins s modifier R seed K Z ξ, E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hbound⟩ := actual_first_joint_contraction W (fun _ => logAnnulus)
    (fun _ => Real.log 4) (fun _ => Real.log_nonneg (by norm_num))
    (fun _ _ hn => CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro s modifier R seed K Z ξ hK E hE he
  rw [actual_physical_mass_ratio_groups,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hh := hbound (ratioFirstSource s modifier R seed K Z ξ hK r)
    (ratioFirstPhase s modifier R seed W K Z ξ r) (dyadicScale r) (dyadicScale_pos r)
    (fun q => actual_source_ratio_fiber s modifier R seed K Z ξ r q)
    (fun q => logAnnulus_norm _) (fun q => logAnnulus_norm _) (E r) (hE r hr) (he r hr)
  have hp : 0<(1+dyadicScale r)^A := pow_pos (by linarith [dyadicScale_pos r]) _
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  have hv (q : SourceRatioFiber s modifier R seed K Z ξ r) :
      (ratioFirstSource s modifier R seed K Z ξ hK r q).value W (fun _ => logAnnulus) =
        coordinateBlock s modifier R seed W K Z ξ q.val := rfl
  simpa only [ratioFirstPhase,hv,mul_comm] using hh

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_physical_mass_ratio_groups
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_physical_mass_joint_contraction
