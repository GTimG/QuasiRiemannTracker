/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The two leaf payments of the reference lane from one instance of the parent's
literal initial energy `InitialAffineAt` on the face `G(.99, 49/20, .14)` at row scale `Z`:
* `direct_leaf`: a canonical native leaf (two ordinary profiles, canonical slots) whose lengths
  lie in the parent face;
* `reflected_child`: a reflected child of the natural reflection (annular dual piece, short
  profile, canonical slots) whose lengths lie in the parent face, in the radial form consumed
  by `natural_reference_reflection_homogeneous`.
Adapted from SDS `Assembly/ParentRows.lean` (`hleaves`) and HC
`Cycle61/Physical/FirstBranches/Child.lean` (`reflected_child_from_positive`), with the parent's
`InitialAffineAt` in place of `PositiveAt`. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Majorant
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Gates
import Submissions.sil_density_split_20261026.CubeFree.Assembly.ParentRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneous
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Reference
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic ConcreteTraceCRT
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalRowSource
open QuadraticInitialBound
open CenteredMomentPrimeSlot (primePool)
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The radial energy only sees rows where the profile does not vanish. -/
theorem energy_effective_keep {ι : Type*} [Fintype ι] [DecidableEq ι] (η : Character) (m A : O)
    (t : ℝ) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ (fun z => keep z ∧ Φ (‖eisEmbedding z‖^2/K) ≠ 0) Φ K =
      energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk : keep z <;> by_cases hz : Φ (‖eisEmbedding z‖^2/K) = 0 <;> simp [hk, hz]

section
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Id) [NeZero M]
local instance instFiniteQuotLeaf : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- **Direct leaf**: a native leaf whose lengths lie in the parent face is paid by the parent's
initial energy, with the inherited height moved into the slot frequencies. -/
theorem direct_leaf (W : ℝ → ℂ) (η η₀ : Character) (Q₀ : Id) (hQ₀ : internalQ Q₀ η₀ = Q₀)
    (Ψ : 𝓢(ℝ,ℂ)) (bΨ : ℝ) (hΨs : Function.support (Ψ:ℝ → ℂ) ⊆ Iic bΨ) (hΨ : ∀ x, 0 ≤ (Ψ x).re)
    (meshP ε : ℝ) (dP : ℕ) (SP : Finset (ℕ×ℕ)) (CP Z : ℝ) (hZ : 1 < Z)
    (hP : InitialAffineAt (α:=α) M H hH (globalFace Bref Lref cref) W 2 (1/4) (9/4) bΨ meshP
      (33/50) (33/50) 1 1 ε Z η η₀ Q₀ dP SP CP)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ meshP) (hσ : ∀ i, σ i = 33/50)
    (hV : 0 ≤ V) (hfreq : ∀ i, |freq i| ≤ V)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Icc (1/4) (9/4)) (t₁ t₂ : ℝ)
    (A : Finset α) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hadm : (globalFace Bref Lref cref).Admissible (length Z X₁) (length Z X₂)
      (∑ i ∈ A, w i) 1) :
    nativeLeaf M H hH W η₀ θ Z w σ freq t η (initialKeep η Q₀) Ψ Z W₁ W₂ t₁ t₂ A X₁ X₂ ≤
      CP*diagonalControl Ψ*((independentProfiles (by norm_num : (0:ℝ) < 1/4) W₁ W₂ hs₁ hs₂ t₁ t₂).control SP)^2*
        (1+|t|+V)^dP*Z^(1+ε) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  rw [nativeLeaf_energy M H hH W η₀ θ Z hZ0 w σ freq t η (initialKeep η Q₀) (fun z hz => hz.1)
    Ψ Z hZ0 hΨ (by norm_num : (0:ℝ) < 1/4) W₁ W₂ hs₁ hs₂ t₁ t₂ A X₁ X₂ hX₁ hX₂]
  have hsA : ∑ i : A, w i = ∑ i ∈ A, w i := Finset.sum_coe_sort A w
  have hb := hP A (fun i => θ i) (fun i => w i) (fun i => σ i) (fun i => t + freq i) 0 (|t|+V)
    (fun i => hw i) (fun i => hwm i) (fun i => (hσ i).ge) (fun i => (hσ i).le)
    (by positivity)
    (fun i => (abs_add_le _ _).trans (add_le_add le_rfl (hfreq i)))
    1 le_rfl le_rfl Ψ hΨs hΨ
    (independentProfiles (by norm_num : (0:ℝ) < 1/4) W₁ W₂ hs₁ hs₂ t₁ t₂) X₁ X₂ hX₁ hX₂
    (by rw [hsA]; exact hadm)
  rw [hQ₀, Real.rpow_one] at hb
  have h0 : (1+|(0:ℝ)|+(|t|+V)) = 1+|t|+V := by rw [abs_zero]; ring
  rw [h0] at hb
  exact hb

/-- **Reflected child**: an annular dual piece, the short profile and canonical slots on `F`,
in the radial form of the natural reflection on the initial state at `Z`, paid by the parent
when its lengths lie in the parent face. -/
theorem reflected_child (W : ℝ → ℂ) (η η₀ : Character) (Q₀ : Id) (hQ₀ : internalQ Q₀ η₀ = Q₀)
    (Ψ : 𝓢(ℝ,ℂ)) (bΨ : ℝ) (hΨs : Function.support (Ψ:ℝ → ℂ) ⊆ Iic bΨ) (hΨ : ∀ x, 0 ≤ (Ψ x).re)
    (meshP ε : ℝ) (dP : ℕ) (SP : Finset (ℕ×ℕ)) (CP Z δ : ℝ) (hZ : 1 < Z) (hδ : 0 ≤ δ)
    (hη : (η.modulus.absNorm:ℝ) ≤ Z^δ)
    (hP : InitialAffineAt (α:=α) M H hH (globalFace Bref Lref cref) W 2 (1/4) (9/4) bΨ meshP
      (33/50) (33/50) 1 1 ε Z η η₀ Q₀ dP SP CP)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ meshP) (hσ : ∀ i, σ i = 33/50)
    (hV : 0 ≤ V) (hfreq : ∀ i, |freq i| ≤ V)
    (Wshort : 𝓢(ℝ,ℂ)) (hsW : Function.support (Wshort:ℝ→ℂ) ⊆ Icc (1/4) (9/4))
    (F : Finset α) (j k : Fin 2) (v X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hadm : (globalFace Bref Lref cref).Admissible (length Z X₁) (length Z X₂)
      (∑ i ∈ F, w i) 1) :
    let s := initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη
    radialEnergy (fun z => polynomial (naturalCharacter s.character z) false
        (scaleTest (fun y:ℝ => (annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v) *
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏ i ∈ F, naturalSlot (naturalCharacter s.character z) (primePool M H 2 (Z^(w i)))
        (heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      CP*diagonalControl Ψ*
        ((reflectionProfiles (by norm_num : (0:ℝ) < 1/4) le_rfl (by norm_num) Wshort hsW j k v t).control SP)^2*
        (1+|t|+V)^dP*Z^(1+ε) := by
  intro s
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have he := reflected_child_ray_energy s (by norm_num : (0:ℝ) < 1/4) le_rfl (by norm_num)
    Wshort hsW F (fun i => primePool M H 2 (Z^(w i)))
    (fun i => relativeCharacter M H hH η₀ (θ i)) (fun _ => W) (fun i => Z^(w i)) σ freq
    (fun i _ I hI => (Finset.mem_filter.mp hI).2.1) (fun i _ => Real.rpow_pos_of_pos hZ0 _)
    j k v t X₁ X₂ hX₁ hX₂
  have hsF : ∑ i : F, w i = ∑ i ∈ F, w i := Finset.sum_coe_sort F w
  have hb := hP F (fun i => θ i) (fun i => w i) (fun i => σ i) (fun i => t + freq i) 0 (|t|+V)
    (fun i => hw i) (fun i => hwm i) (fun i => (hσ i).ge) (fun i => (hσ i).le)
    (by positivity)
    (fun i => (abs_add_le _ _).trans (add_le_add le_rfl (hfreq i)))
    1 le_rfl le_rfl Ψ hΨs hΨ
    (reflectionProfiles (by norm_num : (0:ℝ) < 1/4) le_rfl (by norm_num) Wshort hsW j k v t)
    X₁ X₂ hX₁ hX₂ (by rw [hsF]; exact hadm)
  rw [hQ₀, Real.rpow_one] at hb
  have h0 : (1+|(0:ℝ)|+(|t|+V)) = 1+|t|+V := by rw [abs_zero]; ring
  rw [h0] at hb
  refine le_trans (le_of_eq he) ?_
  change energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 _ _ _ _ _ X₁ X₂
    (fun z => initialKeep η Q₀ z ∧ Ψ (‖eisEmbedding z‖^2/Z) ≠ 0) Ψ Z ≤ _
  rw [energy_effective_keep]
  exact hb

end

end
end Qrh.MarkedAnchor.Ordinary.Reference
