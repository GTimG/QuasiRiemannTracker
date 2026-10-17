import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstReferenceSource

/-! The actual first-source labels stay in the Hilbert index. This bridge
does not supply an analytic energy estimate; it transports jointly proved
estimates to the original physical mass without a label-cardinality loss. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace OAI.SevenEighths.Cycle63JointSource
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstSourceReduction
open CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentExceptionalAmplitudePair

local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev SourceCoordinate (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) :=
  (p : Labels s R seed) ×
    (E : ↥(inactiveSubsets p.val.1 p.val.2)) ×
      SourceBlocks s R seed K Z ξ p E.val

def coordinateBlock (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ)
    (q : SourceCoordinate s R seed K Z ξ) : ℂ :=
  originalBlock s R seed W K Z ξ q.1 q.2.1.val q.2.2

theorem physicalMass_eq_coordinate_sum (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask *
      ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ =
      ∑ q : SourceCoordinate s R seed K Z ξ, ‖coordinateBlock s R seed W K Z ξ q‖ := by
  rw [physicalMass_eq_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Fintype.sum_sigma]
  simpa only [coordinateBlock] using
    (Finset.sum_coe_sort (inactiveSubsets p.val.1 p.val.2)
      (fun E => ∑ n : SourceBlocks s R seed K Z ξ p E,
        ‖originalBlock s R seed W K Z ξ p E n‖)).symm

/-- Ordinary Cauchy applied once to the full label-coordinate index. -/
theorem joint_nonnegative_cauchy {α : Type*} [Fintype α]
    (mass left right : α → ℝ)
    (hmass : ∀ q, 0 ≤ mass q)
    (hleft : ∀ q, 0 ≤ left q) (hright : ∀ q, 0 ≤ right q)
    (hbound : ∀ q, mass q ≤ Real.sqrt (left q) * Real.sqrt (right q)) :
    (∑ q, mass q)^2 ≤ (∑ q, left q) * ∑ q, right q := by
  have hsum : (∑ q, mass q) ≤ ∑ q, Real.sqrt (left q) * Real.sqrt (right q) :=
    Finset.sum_le_sum (fun q _ => hbound q)
  have hnonneg : 0 ≤ ∑ q, mass q := Finset.sum_nonneg (fun q _ => hmass q)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun q => Real.sqrt (left q)) (fun q => Real.sqrt (right q))
  simp only [Real.sq_sqrt (hleft _), Real.sq_sqrt (hright _)] at hc
  exact (pow_le_pow_left₀ hnonneg hsum 2).trans hc

/-- The hypotheses are bounds on the actual blocks. The conclusion remains
conditional until their two joint energies have been established. -/
theorem physicalMass_joint_energy (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ)
    (left right : SourceCoordinate s R seed K Z ξ → ℝ)
    (hleft : ∀ q, 0 ≤ left q) (hright : ∀ q, 0 ≤ right q)
    (hblock : ∀ q, ‖coordinateBlock s R seed W K Z ξ q‖ / volume s.toData ≤
      Real.sqrt (left q) * Real.sqrt (right q)) :
    (physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask *
      ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ / volume s.toData)^2 ≤
      (∑ q, left q) * ∑ q, right q := by
  rw [physicalMass_eq_coordinate_sum, Finset.sum_div]
  exact joint_nonnegative_cauchy _ left right
    (fun q => div_nonneg (norm_nonneg _) (volume_pos s.toData).le) hleft hright hblock

#print axioms physicalMass_eq_coordinate_sum
#print axioms physicalMass_joint_energy
end OAI.SevenEighths.Cycle63JointSource
