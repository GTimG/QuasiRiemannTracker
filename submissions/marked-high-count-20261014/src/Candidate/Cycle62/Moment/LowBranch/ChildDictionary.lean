import Candidate.Cycle62.Moment.LowBranch.DaughterState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual allocated child is the literal relative prime-ray family on
its surviving labels. Both plain norm cutoffs and the puncture remain exact. -/
theorem child_ray_energy
    (s : Input α) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ v : α → ℝ) (W : ℝ → ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ v W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (χ : Character) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := child s C R B χ t
    energy c.η c.m 1 t c.W₁ c.W₂ c.slots c.toData.coefficient c.P
      c.X₁ c.X₂ keep Φ K =
    energy χ (fixedBadMask*idealGenerator (R*C)) 1 t s.W₁ s.W₂
      (fun j : liveIndices B.val => primePool M H bslot (Z^(w j)))
      (fun (j : liveIndices B.val) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I)
      (fun j : liveIndices B.val => Z^(w j))
      (s.X₁/(B.val (Sum.inr 0)).absNorm) (s.X₂/(B.val (Sum.inr 1)).absNorm)
      keep Φ K := by
  dsimp only
  have hpool : (child s C R B χ t).slots =
      fun j : liveIndices B.val => primePool M H bslot (Z^(w j)) := by
    funext j
    exact hm.pool j
  have hscale : (child s C R B χ t).P =
      fun j : liveIndices B.val => Z^(w j) := by
    funext j
    exact hm.scale j
  have hcoeff : (child s C R B χ t).toData.coefficient =
      fun (j : liveIndices B.val) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I := by
    funext j I
    change s.ν j.val I*s.W j.val ((I.absNorm:ℝ)/s.P j.val) = _
    rw [hm.character,hm.profile,hm.scale]
    rfl
  rw [hpool,hscale,hcoeff]
  rfl

/-- The same dictionary covers the second rectangle without equating its
individual scales to the first rectangle. -/
theorem child_reference_ray_energy
    (s : Input α) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ v : α → ℝ) (W : ℝ → ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ v W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (χ : Character) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := child s C R B χ t
    energy c.η c.m 1 t c.W₁ c.W₂ c.slots c.toData.coefficient c.P
      c.Y₁ c.Y₂ keep Φ K =
    energy χ (fixedBadMask*idealGenerator (R*C)) 1 t s.W₁ s.W₂
      (fun j : liveIndices B.val => primePool M H bslot (Z^(w j)))
      (fun (j : liveIndices B.val) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I)
      (fun j : liveIndices B.val => Z^(w j))
      (s.Y₁/(B.val (Sum.inr 0)).absNorm) (s.Y₂/(B.val (Sum.inr 1)).absNorm)
      keep Φ K := by
  dsimp only
  have hpool : (child s C R B χ t).slots =
      fun j : liveIndices B.val => primePool M H bslot (Z^(w j)) := by
    funext j; exact hm.pool j
  have hscale : (child s C R B χ t).P =
      fun j : liveIndices B.val => Z^(w j) := by
    funext j; exact hm.scale j
  have hcoeff : (child s C R B χ t).toData.coefficient =
      fun (j : liveIndices B.val) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I := by
    funext j I
    change s.ν j.val I*s.W j.val ((I.absNorm:ℝ)/s.P j.val) = _
    rw [hm.character,hm.profile,hm.scale]; rfl
  rw [hpool,hscale,hcoeff]
  rfl

#print axioms child_ray_energy
#print axioms child_reference_ray_energy
end
end OAI.SevenEighths.Cycle62Moment.LowBranch
