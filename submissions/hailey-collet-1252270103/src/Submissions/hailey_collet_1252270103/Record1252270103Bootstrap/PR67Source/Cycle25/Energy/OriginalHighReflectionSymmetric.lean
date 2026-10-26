import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.OriginalHighReflectionOriginal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.ReferenceState
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.ReferenceLowBranchGeometry
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/OriginalHighReflectionSymmetric.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

omit [DecidableEq α] in
lemma energy_swap (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β:α→ Ideal O→ℂ)(P:α→ℝ)(X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₂ W₁ pool β P X₂ X₁ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      positiveSlotRow η m A z W₂ W₁ pool β P t X₂ X₁:=by
    unfold positiveSlotRow
    rw [mul_comm X₁ X₂]
    ring
  rw [hh]

theorem balanced_four_scale_gates (Z width X₁ X₂:ℝ)(hZ:1<Z)(hwidth:0<width)
    (hX₁:0<X₁)(hX₂:0<X₂)
    (hshort:width/4≤ min (length Z X₁) (length Z X₂)):
    Z^(width/4)≤X₁ ∧ Z^(width/4)≤X₂ ∧
    Z^(width/4)≤ comparisonFirst Z width ∧
    Z^(width/4)≤ comparisonSecond Z width X₁ X₂ ∧
    length Z X₁+length Z X₂=Real.logb Z (X₁*X₂):=by
  have h₁:width/4≤length Z X₁:=hshort.trans (min_le_left _ _)
  have h₂:width/4≤length Z X₂:=hshort.trans (min_le_right _ _)
  have hraw (X:ℝ)(hX:0<X)(h:width/4≤length Z X):
      length Z X=Real.logb Z X ∧ width/4≤Real.logb Z X:=by
    have he:=Cycle25CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX
    have hp:0<Real.logb Z X:=by
      by_contra hn
      rw [he,max_eq_left (le_of_not_gt hn)] at h
      linarith
    refine ⟨he.trans (max_eq_right hp.le),?_⟩
    rwa [he,max_eq_right hp.le] at h
  obtain ⟨he₁,hr₁⟩:=hraw X₁ hX₁ h₁
  obtain ⟨he₂,hr₂⟩:=hraw X₂ hX₂ h₂
  refine ⟨?_,?_,le_refl _,?_,?_⟩
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₁] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₁
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₂] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₂
  · rw [comparison_second_power Z width X₁ X₂ hZ hX₁ hX₂,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · rw [he₁,he₂,Real.logb_mul hX₁.ne' hX₂.ne']

variable (M:Ideal O)[NeZero M]
local instance originalHighReflectionSymmetricFinite : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric

end

end OAI

end Record1252270103Bootstrap.PR67
