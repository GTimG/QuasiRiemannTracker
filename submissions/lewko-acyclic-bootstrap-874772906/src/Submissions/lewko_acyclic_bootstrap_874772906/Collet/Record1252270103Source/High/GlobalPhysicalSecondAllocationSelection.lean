/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One genuine second common allocation is chosen from its complete residual
cost. All original residual ideals remain inside that cost during selection. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondResidualAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstAllocationSelectionFinite
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open Record1252270103Source Record1252270103Second Collision
open Admission.JointForced Admission.FirstAllocationSelection
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def secondAllocatedResidualNorm (s : Input ι) (A₁ A₂ D K C R : Ideal O)
    (F : Ideal O→ℂ) (Ls : Finset (Ideal O)) (τ : Character) (t : ℝ) (z : O)
    (B : actualAllocations s.pools C) : ℝ :=
  ∑L∈Ls,‖normalizedRow (child s C R B τ t)
    (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
      (D*C) (K*markedProduct B.val) F) (R*C) L τ t z‖^2

theorem marked_plain_residual_selected_allocation (s : Input ι)
    (A₁ A₂ D K C R seed : Ideal O) (F : Ideal O→ℂ)
    (hC : Supported C) (hseed : seed∣C)
    (Ls : Finset (Ideal O)) (τ : Character) (t : ℝ) (z : O)
    (hne : (∑L∈Ls,‖modifiedPlainColumn s (markedSourceModifier A₁ A₂ D K F)
      C hC R seed L τ t z‖^2)≠0) :
    ∃B:actualAllocations s.pools C,
      frozenCoefficient B.val C R s.ν s.W s.P≠0 ∧
      0<secondAllocatedResidualNorm s A₁ A₂ D K C R F Ls τ t z B ∧
      (∑L∈Ls,‖modifiedPlainColumn s (markedSourceModifier A₁ A₂ D K F)
        C hC R seed L τ t z‖^2)≤
        ((actualAllocations s.pools C).card:ℝ)^2*
          ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
            (volume (child s C R B τ t)/volume s)*
              secondAllocatedResidualNorm s A₁ A₂ D K C R F Ls τ t z B := by
  let frozen:=fun B:actualAllocations s.pools C=>frozenCoefficient B.val C R s.ν s.W s.P
  let cost:=fun B:actualAllocations s.pools C=>
    (volume (child s C R B τ t)/volume s)*secondAllocatedResidualNorm s A₁ A₂ D K C R F Ls τ t z B
  have hc (B):0≤cost B:=mul_nonneg (div_nonneg (volume_pos _).le (volume_pos _).le)
    (Finset.sum_nonneg (fun L _=>sq_nonneg _))
  have hb:=marked_plain_full_residual_allocation s A₁ A₂ D K C R seed F hC hseed Ls τ t z
  change _≤((actualAllocations s.pools C).card:ℝ)*weightedTotal frozen cost at hb
  have ht:weightedTotal frozen cost≠0 := by
    intro h
    rw [h,mul_zero] at hb
    exact hne (le_antisymm hb (Finset.sum_nonneg (fun L _=>sq_nonneg _)))
  obtain ⟨B,hf,hcost,_,hmax⟩:=weighted_full_cost_max frozen cost hc ht
  have hratio:0<volume (child s C R B τ t)/volume s:=div_pos (volume_pos _) (volume_pos _)
  have hnorm:0<secondAllocatedResidualNorm s A₁ A₂ D K C R F Ls τ t z B :=
    (mul_pos_iff_of_pos_left hratio).mp hcost
  refine ⟨B,hf,hnorm,hb.trans ?_⟩
  have hm:=mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg (actualAllocations s.pools C).card)
  simpa only [Fintype.card_coe,frozen,cost,pow_two,mul_assoc] using hm

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_plain_residual_selected_allocation
