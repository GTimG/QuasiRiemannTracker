/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One common presented modulus and two independent fixed coefficient colors.
Both initial keeps agree on the original unmodified row. -/
import Candidate.C092.transport.PairMarkAnnulus
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedRayInducingTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentFixedRayInducingTransport CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentHeckeColumnWindow
namespace QRH.Cycle092.FixedRayPair
local notation "O" => HeckeFamily.O

def commonQ (Q:Ideal O) (ω₁ ω₂:Character) := Q⊓ω₁.modulus⊓ω₂.modulus

theorem commonQ_le (Q:Ideal O) (ω₁ ω₂:Character) :
    commonQ Q ω₁ ω₂≤Q ∧ commonQ Q ω₁ ω₂≤ω₁.modulus ∧ commonQ Q ω₁ ω₂≤ω₂.modulus :=
  ⟨inf_le_left.trans inf_le_left,inf_le_left.trans inf_le_right,inf_le_right⟩

theorem internalQ_product (Q:Ideal O) (base ω:Character) (hq:Q ≤ ω.modulus) :
    internalQ Q (base.product ω)=internalQ Q base := by
  change Q⊓(base.modulus⊓ω.modulus) = Q⊓base.modulus
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hq)))

theorem product_keep (Q:Ideal O) (base old ω:Character) (hq:Q ≤ ω.modulus) (z:O) :
    initialKeep (old.product ω) (internalQ Q (base.product ω)) z ↔
    initialKeep old (internalQ Q base) z := by
  rw [internalQ_product Q base ω hq]
  by_cases hz:z=0
  · simp [hz,initialKeep]
  let m := fixedBadMask*idealGenerator 1
  have hm : m≠0 := mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero)
  have hl : goodLambda∣m := (dvd_mul_right _ _ : goodLambda∣fixedBadMask).trans (dvd_mul_right _ _)
  have ht : (2:O)∣m := (dvd_mul_left _ _ : (2:O)∣fixedBadMask).trans (dvd_mul_right _ _)
  change (z≠0 ∧ ¬FixedInducingRow (old.product ω) (internalQ Q base) m 1 z) ↔ _
  rw [fixedInducingRow_product_iff old ω (internalQ Q base) m 1 z (inf_le_left.trans hq) hm one_ne_zero hz hl ht]
  rfl

theorem both_keeps (Q:Ideal O) (base old ω₁ ω₂:Character) (z:O)
    (h:initialKeep old (internalQ (commonQ Q ω₁ ω₂) base) z) :
    initialKeep (old.product ω₁) (internalQ (commonQ Q ω₁ ω₂) (base.product ω₁)) z ∧
    initialKeep (old.product ω₂) (internalQ (commonQ Q ω₁ ω₂) (base.product ω₂)) z :=
  ⟨(product_keep _ _ _ _ (commonQ_le Q ω₁ ω₂).2.1 z).mpr h,
    (product_keep _ _ _ _ (commonQ_le Q ω₁ ω₂).2.2 z).mpr h⟩

#print axioms both_keeps
end QRH.Cycle092.FixedRayPair
