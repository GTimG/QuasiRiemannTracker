/- The parent of the second step as an input: the second-stage child of a first-stage child, at the child's own
character, restricted to the slots that survive the fixed deletion; its slot dictionary, endpoints, scales and volume
come from the first-stage child. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.SecondSourceControls

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonHeightEnvelope

/-- The input with the slots of `S` only; every other datum is kept. -/
def restrictSlots {ι : Type*} [Fintype ι] (s : Input ι) (S : Finset ι) : Input S where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := fun i => s.slots i.val
  prime := fun i => s.prime i.val
  ν := fun i => s.ν i.val
  W := fun i => s.W i.val
  lo := fun i => s.lo i.val
  hi := fun i => s.hi i.val
  P := fun i => s.P i.val
  lo_pos := fun i => s.lo_pos i.val
  P_pos := fun i => s.P_pos i.val
  support := fun i => s.support i.val
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  M := fun i => s.M i.val
  M_ge_one := fun i => s.M_ge_one i.val
  coefficient_bound := fun i => s.coefficient_bound i.val
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := s.X₁_pos
  X₂_pos := s.X₂_pos
  Y₁_pos := s.Y₁_pos
  Y₂_pos := s.Y₂_pos
  same_product := s.same_product
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := s.plain₁
  plain₂ := s.plain₂
  plain₁_ne := s.plain₁_ne
  plain₂_ne := s.plain₂_ne
  coverage₁ := s.coverage₁
  coverage₂ := s.coverage₂
  ν_bound := fun i => s.ν_bound i.val
  W_bound := fun i => s.W_bound i.val
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i => s.lower_le i.val
  upper_ge := fun i => s.upper_ge i.val

/-- Restricting the slots keeps the slot dictionary of the remaining slots. -/
theorem restrict_matches {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (s : Input ι) (η₀ : Character) (θ : ι → RayQuotient.Characters M H) (w σ freq : ι → ℝ) (W : ℝ → ℂ)
    (bslot Z : ℝ) (hm : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (S : Finset ι) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (restrictSlots s S) η₀ (fun i => θ i.val)
      (fun i => w i.val) (fun i => σ i.val) (fun i => freq i.val) W bslot Z :=
  ⟨fun i I => hm.character i.val I, fun i y => hm.profile i.val y, fun i => hm.pool i.val,
    fun i => hm.scale i.val⟩

/-- Restricting the slots keeps the endpoints. -/
theorem restrict_endpoints {ι : Type*} [Fintype ι] (b b₁ b₂ : ℝ) (s : Input ι) (h : Endpoints b b₁ b₂ s)
    (S : Finset ι) : Endpoints b b₁ b₂ (restrictSlots s S) :=
  ⟨h.1, fun i => h.2.1 i.val, h.2.2⟩

/-- A new character and height keep the slot dictionary. -/
theorem withHeight_matches {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (s : Input ι) (η₀ : Character) (θ : ι → RayQuotient.Characters M H) (w σ freq : ι → ℝ) (W : ℝ → ℂ)
    (bslot Z : ℝ) (hm : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (τ : Character) (v : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (withHeight s τ v) η₀ θ w σ freq W bslot Z :=
  ⟨hm.character, hm.profile, hm.pool, hm.scale⟩

/-- A new character and height keep the endpoints. -/
theorem withHeight_endpoints {ι : Type*} [Fintype ι] (b b₁ b₂ : ℝ) (s : Input ι) (h : Endpoints b b₁ b₂ s)
    (τ : Character) (v : ℝ) : Endpoints b b₁ b₂ (withHeight s τ v) := h

/-- The volume of the restricted input is the original plain volume times the scales of the remaining slots. -/
theorem restrict_volume {ι : Type*} [Fintype ι] (s : Input ι) (S : Finset ι) :
    volume (restrictSlots s S) = s.X₁*s.X₂*∏ i ∈ S, s.P i := by
  change s.X₁*s.X₂*∏ i : S, s.P i.val = _
  rw [Finset.prod_coe_sort S s.P]

/-- The volume of the restricted input times the scales of the removed slots is the volume of the input. -/
theorem restrict_volume_mul {ι : Type*} [Fintype ι] (s : Input ι) (S : Finset ι) :
    volume (restrictSlots s S)*∏ i ∈ Finset.univ \ S, s.P i = volume s := by
  rw [restrict_volume, mul_assoc, mul_comm (∏ i ∈ S, s.P i), Finset.prod_sdiff (Finset.subset_univ S)]
  rfl

/-- The parent of the second step, the second-stage child of the first-stage child `s₁` at the character `σ`
restricted to the surviving slots `S`, keeps the slot dictionary of `s₁` on its slots. -/
theorem depth_two_parent_matches {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (s₁ : Input ι) (η₀ : Character) (θ : ι → RayQuotient.Characters M H) (w σ freq : ι → ℝ) (W : ℝ → ℂ)
    (bslot Z : ℝ) (hm : CenteredMomentAllocatedRayDictionary.Matches M H hH s₁ η₀ θ w σ freq W bslot Z)
    (τ : Character) (v : ℝ) (C R : Ideal O) (B : actualAllocations (withHeight s₁ τ v).pools C)
    (S : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (restrictSlots (child (withHeight s₁ τ v) C R B τ v) S) η₀
      (fun i => θ i.val.val) (fun i => w i.val.val) (fun i => σ i.val.val) (fun i => freq i.val.val) W bslot Z :=
  restrict_matches M H hH _ η₀ _ _ _ _ W bslot Z
    (actual_child_matches M H hH (withHeight s₁ τ v) η₀ θ w σ freq W bslot Z
      (withHeight_matches M H hH s₁ η₀ θ w σ freq W bslot Z hm τ v) C R B τ v) S

/-- The parent of the second step keeps the endpoints of the first-stage child. -/
theorem depth_two_parent_endpoints {ι : Type*} [Fintype ι] (b b₁ b₂ : ℝ) (s₁ : Input ι)
    (h : Endpoints b b₁ b₂ s₁) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations (withHeight s₁ τ v).pools C)
    (S : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Endpoints b b₁ b₂ (restrictSlots (child (withHeight s₁ τ v) C R B τ v) S) :=
  restrict_endpoints b b₁ b₂ _ (endpoints_child b b₁ b₂ _ (withHeight_endpoints b b₁ b₂ s₁ h τ v) C R B τ v) S

/-- The parent of the second step has the character `σ`, the height `v`, the plain profiles, the profile endpoints, the
upper slot window and the slot coefficient bounds of the first-stage child, and at most as many slots. -/
theorem depth_two_parent_data {ι : Type*} [Fintype ι] (s₁ : Input ι) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations (withHeight s₁ τ v).pools C)
    (S : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    let s := restrictSlots (child (withHeight s₁ τ v) C R B τ v) S
    s.η = τ ∧ s.t = v ∧ s.W₁ = s₁.W₁ ∧ s.W₂ = s₁.W₂ ∧ s.b₁ = s₁.b₁ ∧ s.b₂ = s₁.b₂ ∧ s.upper = s₁.upper ∧
      (∀ i, s.M i = s₁.M i.val.val) ∧ Fintype.card S ≤ Fintype.card ι := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_⟩
  exact (Fintype.card_le_of_injective (fun i : S => i.val.val)
    (fun i j h => Subtype.ext (Subtype.ext h)))

end
end OAI.SevenEighths.Cycle63InitialMass
