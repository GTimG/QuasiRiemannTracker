import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.LowBranch.ChildDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61ChildMatches
noncomputable section
open scoped Classical
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAllocatedRayDictionary
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Common allocation restricts the same relative slot dictionary. Changing
the row character or its height does not change any of these slot data. -/
theorem actual_child_matches
    (s : Input α) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ freq : α → ℝ) (W : ℝ → ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Matches M H hH (child s C R B τ t) η₀
      (fun i => θ i.val) (fun i => w i.val) (fun i => σ i.val)
      (fun i => freq i.val) W bslot Z := by
  exact ⟨fun i I => hm.character i.val I, fun i y => hm.profile i.val y,
    fun i => hm.pool i.val, fun i => hm.scale i.val⟩

/-- Prime extraction preserves the dictionary through both actual allocations;
no claim that the extracted prime divides a final row is used. -/
theorem actual_twice_child_matches
    (s : Input α) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ freq : α → ℝ) (W : ℝ → ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i => θ i.val.val) (fun i => w i.val.val) (fun i => σ i.val.val)
      (fun i => freq i.val.val) W bslot Z := by
  exact actual_child_matches M H hH _ η₀ _ _ _ _ W bslot Z
    (actual_child_matches M H hH s η₀ θ w σ freq W bslot Z hm C R B τ t)
    (Q^k) (R*C) Bp υ v

end
end OAI.SevenEighths.Cycle61ChildMatches
#print axioms OAI.SevenEighths.Cycle61ChildMatches.actual_child_matches
#print axioms OAI.SevenEighths.Cycle61ChildMatches.actual_twice_child_matches
