/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalDaughterSource
import Candidate.Cycle63.Moment.StateRebase
import Candidate.Cycle63.Moment.LowBranch.WidenedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily HeckePrimeAnnular ConcretePrimeRowBridge CenteredMomentEnergyState
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open Cycle63Moment.LowBranch
local notation "O" => HeckeFamily.O

/-- Change only a state's puncture cap, using the actual norm bound. This
preserves the physical character, radial source, puncture and widths. -/
def actualMaskBound {Z oldMask bΦ : ℝ} (s : NaturalState Z oldMask bΦ)
    (newMask : ℝ) (hmask : (s.puncture.absNorm : ℝ) ≤ Z ^ newMask) :
    NaturalState Z newMask bΦ where
  character := s.character
  fixedModulus := s.fixedModulus
  puncture := s.puncture
  radial := s.radial
  rowWidth := s.rowWidth
  characterWidth := s.characterWidth
  base_ge_one := s.base_ge_one
  row_nonneg := s.row_nonneg
  character_nonneg := s.character_nonneg
  scale_eq := s.scale_eq
  modulus_bound := s.modulus_bound
  puncture_ne_zero := s.puncture_ne_zero
  puncture_bound := hmask
  radial_support := s.radial_support
  row_ne_zero := s.row_ne_zero
  nonexceptional := s.nonexceptional

/-- The actual continuing state, at its native chosen width W. There is
no enlargement beyond W and no modification of the physical character,
puncture, radial scale, row mask or energy. The source-derived mask20
gate is the explicit puncture norm inequality. -/
def nativeContinuationState {Z oldMask bΦ : ℝ} (s : NaturalState Z oldMask bΦ)
    (W : ℝ) (hW : 0 < W) (hwide : s.width ≤ W)
    (hmask : (s.puncture.absNorm : ℝ) ≤ (Z ^ W) ^ (20 : ℝ)) :
    NaturalState (Z ^ W) 20 bΦ :=
  actualMaskBound ((widenState s W hwide).rebase W hW) 20 hmask

theorem nativeContinuationState_width {Z oldMask bΦ : ℝ}
    (s : NaturalState Z oldMask bΦ) (W : ℝ) (hW : 0 < W) (hwide : s.width ≤ W)
    (hmask : (s.puncture.absNorm : ℝ) ≤ (Z ^ W) ^ (20 : ℝ)) :
    (nativeContinuationState s W hW hwide hmask).width = 1 := by
  change ((widenState s W hwide).rebase W hW).width = 1
  rw [NaturalState.rebase_width, widenState_width, div_self hW.ne']

theorem nativeContinuationState_fields {Z oldMask bΦ : ℝ}
    (s : NaturalState Z oldMask bΦ) (W : ℝ) (hW : 0 < W) (hwide : s.width ≤ W)
    (hmask : (s.puncture.absNorm : ℝ) ≤ (Z ^ W) ^ (20 : ℝ)) :
    let next := nativeContinuationState s W hW hwide hmask
    next.character = s.character ∧ next.fixedModulus = s.fixedModulus ∧
      next.puncture = s.puncture ∧ next.radial = s.radial ∧ next.mask = s.mask :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

section Input
variable {ι : Type*} [Fintype ι]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters M H)
variable (Wslot : ℝ → ℂ) (hWslot : Continuous Wslot)
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)
variable (hWs : Function.support Wslot ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z oldMask bΦ ap bp : ℝ} (s : NaturalState Z oldMask bΦ)
variable (unit : ℝ) (hunit : 0 < unit) (hwide : s.width ≤ unit)
variable (hmask : (s.puncture.absNorm : ℝ) ≤ (Z ^ unit) ^ (20 : ℝ))
variable (p : Profiles ap bp) (hap : 0 < ap)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hprod : Y₁ * Y₂ = X₁ * X₂)

/-- The real next affine source. In the LOW continuation, ι is exactly
`↥(ch.indices L alloc \\ R)` and X₁,X₂ are the literal raw daughter scales.
The caller chooses its equal-product comparison from the actual regional
ledger. All remaining ray coefficients/profiles are retained, with only
their exponent unit changed from Z to Z^unit. -/
def nativeContinuationInput : Input ι :=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ Wslot hWslot
    aslot bslot lo hi haslot hWs (fun i => w i / unit) σ freq hσ
    (nativeContinuationState s unit hunit hwide hmask) p hap
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

theorem nativeContinuationInput_matches :
    CenteredMomentAllocatedRayDictionary.Matches M H hH
      (nativeContinuationInput M H hH η₀ θ Wslot hWslot aslot bslot lo hi haslot hWs
        w σ freq hσ s unit hunit hwide hmask p hap t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod)
      η₀ θ (fun i => w i / unit) σ freq Wslot bslot (Z ^ unit) := by
  apply CenteredMomentEnergyNaturalInputMatches.input_matches

/-- Exact source equality for the continuing input. This is proved from
native coefficients and rpow rebasing; it is not a supplied energy identity.
The radial/reciprocal normalization has no new factor. -/
theorem nativeContinuationInput_energy :
    let state := nativeContinuationState s unit hunit hwide hmask
    let inp := nativeContinuationInput M H hH η₀ θ Wslot hWslot aslot bslot lo hi haslot hWs
      w σ freq hσ s unit hunit hwide hmask p hap t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    energy inp.η state.mask 1 inp.t inp.W₁ inp.W₂ inp.slots inp.coefficient inp.P inp.X₁ inp.X₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool M H bslot (Z ^ w i))
      (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        annularWeight Wslot (Z ^ w i) (σ i) (freq i) I)
      (fun i => Z ^ w i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  dsimp only
  change energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool M H bslot ((Z ^ unit) ^ (w i / unit)))
      (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        annularWeight Wslot ((Z ^ unit) ^ (w i / unit)) (σ i) (freq i) I)
      (fun i => (Z ^ unit) ^ (w i / unit)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale = _
  simp only [s.rpow_rebase hunit]

end Input
end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.nativeContinuationState_width
#print axioms OAI.SevenEighths.Cycle153RegionalLow.nativeContinuationInput_energy
