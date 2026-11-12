/- Copyright (c) 2026 Sil and Joseph Bebel. Apache-2.0. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RestoredRootSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.PR98Improvement.GeneralizedRootSource
open Candidate.FourthPower
open Candidate.FourthPower.RestoredRootSource
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentLattice
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.Record1252270103Source
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open CenteredMomentEnergyBands CenteredMomentAddedZeroUniform
open CenteredMomentAllocatedNaturalRadial
open CenteredMomentTwist
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowProfiles
open KernelRowPools KernelPunctureRows KernelLabelledSlots
open NativeFiniteHoles NativeInjectiveEnergy ReferencePrimeEnclosure
open MixedCommonCoefficient MixedCanonicalSource MixedFrozenSource MixedPrincipalPair
open MixedPrincipalHeights MixedPrincipalWindow MixedPrincipalAllocations MixedFirstSeededSource
open MixedFirstPuncturedReference MixedFirstActualNonexceptional
open MixedFirstGeometricCaps MixedFirstChosenEnergy RestoredRootDictionary
open MixedFirstRebase
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ)

theorem face_root_gates {α : Type*} [Fintype α]
    (ρ : ℝ) (hρ : 0 < ρ)
    (Z X₁ X₂ Y₁ Y₂ : ℝ) (w : α → ℝ) (hw : ∀ i,0 ≤ w i)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hy₁ : Y₁ ≤ X₁) (hy₂ : Y₂ ≤ X₂)
    (hface : (globalFace (1-ρ) (93/25) (3/50)).Admissible
      (length Z X₁) (length Z X₂) (∑ i,w i) 1)
    (T : Finset α) (η : Character) (K : ℝ) (hK : Z ≤ K) :
    Y₁ ≤ Z ∧ Y₂ ≤ Z ∧
    (∀ i : T,0 ≤ w i.val ∧ w i.val ≤ 3/50) ∧
    (∑ i : T,w i.val) ≤ 3/50 ∧
    Real.logb Z (Y₁*Y₂)+(93/25)*(∑ i : T,w i.val) ≤
      inputWidth η K Z-ρ := by
  have hs : 0 ≤ ∑ i,w i := Finset.sum_nonneg (fun i _ => hw i)
  obtain ⟨hcap,hbudget⟩ := (globalFace_admissible_iff
    (length_nonneg Z X₁ hZ) (length_nonneg Z X₂ hZ) hs (by norm_num : (0:ℝ) ≤ 93/25)).mp hface
  simp only [mul_one] at hcap hbudget
  have hsub : (∑ i : T,w i.val) ≤ ∑ i,w i := by
    rw [Finset.sum_coe_sort T (fun i => w i)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hw i)
  have hlog₁ : Real.logb Z Y₁ ≤ length Z X₁ :=
    Real.logb_le_logb_of_le hZ hY₁ (hy₁.trans (le_max_right _ _))
  have hlog₂ : Real.logb Z Y₂ ≤ length Z X₂ :=
    Real.logb_le_logb_of_le hZ hY₂ (hy₂.trans (le_max_right _ _))
  have hlen₁ : length Z X₁ ≤ 1 := by
    nlinarith [length_nonneg Z X₂ hZ]
  have hlen₂ : length Z X₂ ≤ 1 := by
    nlinarith [length_nonneg Z X₁ hZ]
  have hYcap (Y : ℝ) (hY : 0 < Y) (hlog : Real.logb Z Y ≤ 1) : Y ≤ Z := by
    calc
      Y = Z^(Real.logb Z Y) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY).symm
      _ ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le hlog
      _ = Z := Real.rpow_one _
  refine ⟨hYcap Y₁ hY₁ (hlog₁.trans hlen₁),hYcap Y₂ hY₂ (hlog₂.trans hlen₂),?_,hsub.trans hcap,?_⟩
  · intro i
    have hi : w i.val ≤ ∑ j,w j := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ _)
    exact ⟨hw _,hi.trans hcap⟩
  · rw [Real.logb_mul hY₁.ne' hY₂.ne']
    have hr := input_width_one η K Z hZ hK
    nlinarith

/-- A direct constructor on the actual surviving subset of the original
slots. Use T=remainingSet r A and R₀=the literal restorationHoles; no
estimate or compatibility premise is requested by this constructor. -/
def fromFace {α : Type*} [Fintype α]
    (ρ : ℝ) (hρ : 0 < ρ)
    (Z Lcap : ℝ) (hZ : 1 < Z) (hLcap : 8 ≤ Lcap)
    (W : ℝ → ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (η₀ : Character) (θ : α → RayQuotient.Characters M Hray)
    (w freq : α → ℝ) (hw : ∀ i,0 ≤ w i) (t : ℝ)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ Y₁ Y₂ : ℝ)
    (hy₁ : Y₁ ≤ X₁) (hy₂ : Y₂ ≤ X₂)
    (hn₁ : comparisonScale (9/4) < Y₁) (hn₂ : comparisonScale (9/4) < Y₂)
    (hface : (globalFace (1-ρ) (93/25) (3/50)).Admissible
      (length Z X₁) (length Z X₂) (∑ i,w i) 1)
    (T : Finset α) (R₀ : T → Finset Id) : Data M Hray T := by
  have hg := face_root_gates ρ hρ Z X₁ X₂ Y₁ Y₂ w hw hZ
    ((comparisonScale_pos _).trans hn₁) ((comparisonScale_pos _).trans hn₂)
    hy₁ hy₂ hface T η₀ Z le_rfl
  exact {
    Z := Z, hZ := hZ, Lcap := Lcap, hLcap := hLcap
    W := W, hW := hW, hWs := hWs
    η₀ := η₀, θ := fun i => θ i.val
    w := fun i => w i.val, freq := fun i => freq i.val
    hw := fun i => (hg.2.2.1 i).1
    hwcap := fun i => (hg.2.2.1 i).2
    R₀ := R₀, t := t, p := p
    X₁ := Y₁, X₂ := Y₂, hx₁ := hn₁, hx₂ := hn₂
    hcap₁ := hg.1, hcap₂ := hg.2.1 }

end
end Qrh.PR98Improvement.GeneralizedRootSource
