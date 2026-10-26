import Candidate.Research.RecursiveAffine.RetainedFCapacity

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle152RetainedFReturn
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedNaturalSource
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentAllocatedChildCapacity

local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A literal residual ideal, one of its actual allocations, and the source
orientation. This is the finite daughter index used before the maximum. -/
abbrev Daughter (Ds : Finset (Ideal O)) :=
  Σ L : Ds, Allocation L.val (Finset.univ : Finset (ι ⊕ Fin 2)) × Bool

def daughterX₁ (s : Data ι) {Ds : Finset (Ideal O)} (d : Daughter (ι:=ι) Ds) : ℝ :=
  if d.2.2 then s.Y₁ else s.X₁

def daughterX₂ (s : Data ι) {Ds : Finset (Ideal O)} (d : Daughter (ι:=ι) Ds) : ℝ :=
  if d.2.2 then s.Y₂ else s.X₂

def daughterF (s : Data ι) {Ds : Finset (Ideal O)}
    (Z : ℝ) (d : Daughter (ι:=ι) Ds) : ℝ :=
  Real.logb Z (formalReductionFactor d.1.val d.2.1 s.P)

def daughterCapacity (s : Data ι) {Ds : Finset (Ideal O)}
    (Z : ℝ) (d : Daughter (ι:=ι) Ds) : ℝ :=
  plainLogs d.1.val d.2.1 Z (daughterX₁ s d) (daughterX₂ s d) +
    remainingLogs d.1.val d.2.1 Z s.P

def LiveDaughter (s : Data ι) {Ds : Finset (Ideal O)}
    (d : Daughter (ι:=ι) Ds) : Prop :=
  ∃ z : O, allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
    d.1.val d.2.1 s.W₁ s.W₂ (daughterX₁ s d) (daughterX₂ s d) ≠ 0

/-- This metadata is attached to an actual surviving daughter, not supplied
as an independent real credit. Its capacity statement is proved natively. -/
theorem live_daughter_capacity (s : Data ι) {Ds : Finset (Ideal O)}
    (Z : ℝ) (hZ : 1 < Z) (d : Daughter (ι:=ι) Ds) (hd : LiveDaughter s d) :
    daughterCapacity s Z d ≤ Real.logb Z (preVolume s) - daughterF s Z d +
      Real.logb Z (max 1 s.b₁ * max 1 s.b₂) := by
  obtain ⟨z, hz⟩ := hd
  have hx₁ : 0 < daughterX₁ s d := by
    unfold daughterX₁
    split <;> first | exact s.Y₁_pos | exact s.X₁_pos
  have hx₂ : 0 < daughterX₂ s d := by
    unfold daughterX₂
    split <;> first | exact s.Y₂_pos | exact s.X₂_pos
  have hp : daughterX₁ s d * daughterX₂ s d = s.X₁ * s.X₂ := by
    unfold daughterX₁ daughterX₂
    cases d.2.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    exact s.same_product
  exact Cycle151RetainedF.supported_residual_total_length_retained s d.1.val d.2.1 Z hZ
    (daughterX₁ s d) (daughterX₂ s d) hx₁ hx₂ hp z hz

/-- The same actual residual reduction is retained in the weighted affine
old-gap cap, not only in total length. The nonnegative remaining-slot
coefficient is charged to the common parent's literal slots. -/
theorem live_daughter_affine_capacity (s : Data ι) {Ds : Finset (Ideal O)}
    (Z κ nominal : ℝ) (hZ : 1 < Z) (hκ : (1 / 6 : ℝ) ≤ κ)
    (hP : ∀ i, 1 ≤ s.P i) (d : Daughter (ι:=ι) Ds) (hd : LiveDaughter s d) :
    plainLogs d.1.val d.2.1 Z (daughterX₁ s d) (daughterX₂ s d) +
        6 * κ * remainingLogs d.1.val d.2.1 Z s.P - nominal ≤
      Real.logb Z (preVolume s) - daughterF s Z d - nominal +
        (6 * κ - 1) * (∑ i, Real.logb Z (s.P i)) +
        Real.logb Z (max 1 s.b₁ * max 1 s.b₂) := by
  have hc := live_daughter_capacity s Z hZ d hd
  change plainLogs d.1.val d.2.1 Z (daughterX₁ s d) (daughterX₂ s d) +
      remainingLogs d.1.val d.2.1 Z s.P ≤ _ at hc
  have hw := mul_le_mul_of_nonneg_left
    (remainingLogs_le d.1.val d.2.1 Z hZ s.P hP)
    (by linarith only [hκ] : 0 ≤ 6 * κ - 1)
  nlinarith only [hc, hw]


example (Ds : Finset (Ideal O)) : Finite (Daughter (ι:=ι) Ds) := inferInstance

end
end OAI.SevenEighths.Cycle152RetainedFReturn

#print axioms OAI.SevenEighths.Cycle152RetainedFReturn.live_daughter_capacity
#print axioms OAI.SevenEighths.Cycle152RetainedFReturn.live_daughter_affine_capacity
