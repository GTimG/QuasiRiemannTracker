/- Copyright (c) 2026 Sil. Apache-2.0.
Exact specialization of RestrictedInitialAt's literal restored row to the
canonical root Source. This file contains no moment bound or energy premise.
-/
import Candidate.SilPrior.FourthPower.RestoredRootSource
import Candidate.SilPrior.FourthPower.RestoredInitialSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RestoredRootEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentLattice
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.Record1252270103Source
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal
open CenteredMomentSourceMass CenteredMomentSourceRectangle
open CenteredMomentDetectorEnergyInitialState CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyBands CenteredMomentTwist
open KernelCollisionEnergy KernelAssignmentReindex KernelMarkedRows
open KernelNaturalSlots KernelRowProfiles KernelRowPools KernelLabelledSlots
open RestorationFamily RestorationCollisionEnergy NativeFiniteHoles NativeMaskedEnergy
open MixedCanonicalSource MixedFrozenSource MixedPrincipalPair
open MixedFirstSeededSource MixedFirstPuncturedReference
open MixedFirstRebase
open RestoredInitialSource RestoredRootDictionary
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {α : Type*} [Fintype α]
variable (rayM : Id) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Literal data from one RestrictedInitialAt instance. The coefficient
restrictions remain collisionBeta followed by crossBeta. No injectivity is
needed for the dictionary (the analytic input may retain that hypothesis).
The extra enclosure exponent is fixed uniformly after the ambient slot type.
-/
structure Setup (α : Type*) [Fintype α] where
  Z : ℝ
  hZ : 1 < Z
  Lcap : ℝ
  hLcap : 8 ≤ Lcap
  W : ℝ → ℂ
  hW : Continuous W
  hWs : Function.support W ⊆ Icc (1:ℝ) 2
  η₀ : Character
  θ : α → RayQuotient.Characters rayM H
  w : α → ℝ
  σ : α → ℝ
  v : α → ℝ
  hw : ∀ i, 0 ≤ w i
  hσlo : ∀ i, (33/50:ℝ) ≤ σ i
  hσhi : ∀ i, σ i ≤ (33/50:ℝ)
  t : ℝ
  p : Profiles (1/4) (9/4)
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  hY₁ : 0 < Y₁
  hY₂ : 0 < Y₂
  hy₁ : Y₁ ≤ X₁
  hy₂ : Y₂ ≤ X₂
  hface : (globalFace (99999/100000) (93/25) (3/50)).Admissible
    (length Z X₁) (length Z X₂) (∑ i,w i) 1
  r : Setoid α
  tc : {q // ¬singletonBlock r q} → primeEnclosure Z
  A : Finset {q // singletonBlock r q}
  ti : A → primeEnclosure Z

namespace Setup
variable {rayM H}
variable (s : Setup rayM H α)

def literalRow (χ : Character) : ℂ :=
  RestorationFamily.row false (primeEnclosure s.Z) χ
    (fun q : Remaining s.r s.A =>
      initialPool rayM H s.w s.Z (singletonRepresentative s.r q.val))
    (crossBeta s.A (primeEnclosure s.Z) s.ti
      (collisionBeta s.r (primeEnclosure s.Z) s.tc
        (initialCoefficient rayM H hH s.η₀ s.θ s.W s.w s.σ s.v s.Z s.t)))
    (fun q => s.Z^(s.w (singletonRepresentative s.r q.val)))
    (raisedProfile s.p s.t 0) (raisedProfile s.p s.t 1) (9/4) s.Y₁ s.Y₂

def rootData (hn₁ : comparisonScale (9/4) < s.Y₁)
    (hn₂ : comparisonScale (9/4) < s.Y₂) :
    RestoredRootSource.Data rayM H (remainingSet s.r s.A) :=
  RestoredRootSource.fromFace rayM H s.Z s.Lcap s.hZ s.hLcap
    s.W s.hW s.hWs s.η₀ s.θ s.w s.v s.hw s.t s.p
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.hy₁ s.hy₂ hn₁ hn₂ s.hface
    (remainingSet s.r s.A) (fun _ => restorationHoles s.r (primeEnclosure s.Z) s.tc s.A s.ti)

def rootSource (hn₁ : comparisonScale (9/4) < s.Y₁)
    (hn₂ : comparisonScale (9/4) < s.Y₂) :
    Source (remainingSet s.r s.A) (1/4) (9/4) :=
  (s.rootData hn₁ hn₂).source hH

set_option maxHeartbeats 800000 in
/-- Exact initial row, including both generated masks, the original ordinary
height, marked height and the natural product normalization. The character
and the initial nonprincipal gate are unchanged. -/
theorem literal_row_source (hn₁ : comparisonScale (9/4) < s.Y₁)
    (hn₂ : comparisonScale (9/4) < s.Y₂) (η : Character) (Q : Id) (z : O)
    (hz : initialKeep η (internalQ Q s.η₀) z) :
    s.literalRow hH (naturalCharacter η z) =
      weightedRow (s.rootSource hH hn₁ hn₂) (by norm_num) 1
        (idealCoeff (naturalCharacter η z)) := by
  have hσ : s.σ = fun _ => (33/50:ℝ) :=
    funext (fun i => le_antisymm (s.hσhi i) (s.hσlo i))
  have he := restored_row_on_original_subset s.r (primeEnclosure s.Z)
    s.tc s.A s.ti (naturalCharacter η z) (initialPool rayM H s.w s.Z)
    (fun i => relativeCharacter rayM H hH s.η₀ (s.θ i))
    s.W (fun i => s.Z^(s.w i)) s.σ s.v s.t
    (raisedProfile s.p s.t 0) (raisedProfile s.p s.t 1) (9/4) s.Y₁ s.Y₂
  have hf := RestoredRootSource.natural_original_row_source rayM H hH
    (s.rootData hn₁ hn₂) η (internalQ Q s.η₀) z hz
  calc
    s.literalRow hH (naturalCharacter η z) =
      RestorationFamily.row false (primeEnclosure s.Z) (naturalCharacter η z)
        (fun i : remainingSet s.r s.A => initialPool rayM H s.w s.Z i.val)
        (fun i I => slotCoefficient
          (fun j : remainingSet s.r s.A => relativeCharacter rayM H hH s.η₀ (s.θ j.val))
          (fun _ => restorationHoles s.r (primeEnclosure s.Z) s.tc s.A s.ti) s.t i I *
          slotProfile s.W (33/50) (s.v i.val) (I.absNorm/s.Z^(s.w i.val)))
        (fun i => s.Z^(s.w i.val))
        (raisedProfile s.p s.t 0) (raisedProfile s.p s.t 1) (9/4) s.Y₁ s.Y₂ := by
          simp only [hσ] at he
          unfold literalRow
          rw [hσ]
          convert he using 1 <;> rfl
    _ = weightedRow (s.rootSource hH hn₁ hn₂) (by norm_num) 1
        (idealCoeff (naturalCharacter η z)) := by
      convert hf using 1 <;> rfl

/-- Exactly the finite weighted energy in RestrictedInitialAt. Off retained
rows the original weight vanishes before invoking the character dictionary.
No additional height or profile loss occurs in this equality. -/
theorem initial_energy_source (hn₁ : comparisonScale (9/4) < s.Y₁)
    (hn₂ : comparisonScale (9/4) < s.Y₂) (η : Character) (Q : Id)
    (Φ : 𝓢(ℝ,ℂ)) (rows : Finset O) :
    (∑ z ∈ rows, initialWeight η s.η₀ Q Φ s.Z z *
      ‖s.literalRow hH (naturalCharacter η z)‖^2) =
    ∑ z ∈ rows, initialWeight η s.η₀ Q Φ s.Z z *
      ‖weightedRow (s.rootSource hH hn₁ hn₂) (by norm_num) 1
        (idealCoeff (naturalCharacter η z))‖^2 := by
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hk : initialKeep η (internalQ Q s.η₀) z
  · rw [s.literal_row_source hH hn₁ hn₂ η Q z hk]
  · simp only [initialWeight,hk,ite_false,zero_mul]

/-- This exact zero branch covers arbitrarily tiny positive Y; it is not
an analytic truncation and needs no power lower bound on those lengths. -/
theorem initial_energy_small (η : Character) (Q : Id)
    (Φ : 𝓢(ℝ,ℂ)) (rows : Finset O)
    (hsmall : s.Y₁ ≤ comparisonScale (9/4) ∨ s.Y₂ ≤ comparisonScale (9/4)) :
    (∑ z ∈ rows, initialWeight η s.η₀ Q Φ s.Z z *
      ‖s.literalRow hH (naturalCharacter η z)‖^2) = 0 := by
  apply Finset.sum_eq_zero
  intro z hz
  have he : s.literalRow hH (naturalCharacter η z) = 0 :=
    RestoredRootSource.small_row _ _ _ _ _ _ _ _ _ hsmall
  rw [he,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero]

/-- The Source stores the original ordinary profiles and one common height;
there is no double raising of the profiles in the canonical energy input. -/
theorem root_profiles (hn₁ : comparisonScale (9/4) < s.Y₁)
    (hn₂ : comparisonScale (9/4) < s.Y₂) :
    (s.rootSource hH hn₁ hn₂).W₁ = s.p.profile 0 ∧
    (s.rootSource hH hn₁ hn₂).W₂ = s.p.profile 1 ∧
    (s.rootSource hH hn₁ hn₂).t₁ = s.t ∧
    (s.rootSource hH hn₁ hn₂).t₂ = s.t := ⟨rfl,rfl,rfl,rfl⟩
end Setup

theorem initial_weight_nonneg (η η₀ : Character) (Q : Id)
    (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x,0 ≤ (Φ x).re) (Z : ℝ) (z : O) :
    0 ≤ initialWeight η η₀ Q Φ Z z := by
  unfold initialWeight
  split_ifs <;> first | exact hΦ _ | exact le_rfl

end
end Candidate.SilPrior.FourthPower.RestoredRootEnergy
