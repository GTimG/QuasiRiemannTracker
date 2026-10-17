import Candidate.Cycle63.Marked.CommonSupply
import Candidate.Cycle63.Moment.HighCommonExponent

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63CommonSupply
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentSourceLiveColumn
open Cycle63Moment
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem actual_common_live_width (N : ℕ) (a : ℝ) (ha : 0<a)
    (s : Input ι) (hcard : Fintype.card ι≤N) (hs : a≤s.lower)
    (C R : Ideal O) (B : actualAllocations s.pools C)
    (hf : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Z : ℝ) (hZ : 1<Z) :
    (∑i,Real.logb Z (s.P i))-Real.logb Z (C.absNorm:ℝ)+
      (N:ℝ)*Real.logb Z (min 1 a) ≤
      ∑i : liveIndices B.val,Real.logb Z (s.P i) := by
  have hh := common_live_width_lower B.val (alloc_ne s C B) C R
    (allocation_product s C B) s.ν s.W s.P s.P_pos a s.upper ha
    (fun i x hx => ⟨hs.trans (s.slot_support i hx).1,(s.slot_support i hx).2⟩) hf Z hZ
  have hc : (Fintype.card ι:ℝ)≤N := by exact_mod_cast hcard
  have hm : Real.logb Z (min 1 a)≤0 :=
    Real.logb_nonpos hZ (le_min (by norm_num) ha.le) (min_le_left _ _)
  have hp := mul_le_mul_of_nonpos_right hc hm
  linarith

/-- Both actual common allocations preserve the original supplied width,
up to their ideal norms and fixed support padding. -/
theorem actual_two_stage_live_width (N : ℕ) (a : ℝ) (ha : 0<a)
    (s : Input ι) (hcard : Fintype.card ι≤N) (hs : a≤s.lower)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0)
    (χ : Character) (t : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (hf₂ : let first := child s C₁ R₁ B₁ χ t
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0)
    (Z : ℝ) (hZ : 1<Z) :
    (∑i,Real.logb Z (s.P i))-Real.logb Z (C₁.absNorm:ℝ)-
      Real.logb Z (C₂.absNorm:ℝ)+2*(N:ℝ)*Real.logb Z (min 1 a) ≤
      ∑i : liveIndices B₂.val,Real.logb Z (s.P i.val.val) := by
  have h₁ := actual_common_live_width N a ha s hcard hs C₁ R₁ B₁ hf₁ Z hZ
  have h₂ := actual_common_live_width N a ha (child s C₁ R₁ B₁ χ t)
    ((live_card_le B₁.val).trans hcard) hs C₂ R₂ B₂ hf₂ Z hZ
  change (∑i : liveIndices B₁.val,Real.logb Z (s.P i))-
    Real.logb Z (C₂.absNorm:ℝ)+(N:ℝ)*Real.logb Z (min 1 a) ≤
    ∑i : liveIndices B₂.val,Real.logb Z (s.P i.val.val) at h₂
  linarith

theorem eventually_two_stage_width_padding (N : ℕ) (a ε : ℝ)
    (ha : 0<a) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ -ε≤2*(N:ℝ)*Real.logb Z (min 1 a) := by
  have hm : 0<min 1 a := lt_min zero_lt_one ha
  have hb : 1≤(min 1 a)⁻¹ := (one_le_inv₀ hm).mpr (min_le_left _ _)
  filter_upwards [eventually_two_stage_padding N (min 1 a)⁻¹ ε hb hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  rw [Real.logb_inv] at hZ
  linarith [hZ.2]

/-- The support threshold is fixed before the input and both allocations.
The width statement is expressed in the original canonical exponents. -/
theorem eventual_two_stage_supplied_width (N : ℕ) (a ε : ℝ)
    (ha : 0<a) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀(s : Input ι),Fintype.card ι≤N → a≤s.lower →
    ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
    frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
    ∀(χ : Character)(t : ℝ)(C₂ R₂ : Ideal O)
      (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂),
    (let first := child s C₁ R₁ B₁ χ t;
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
    ∀w : ι→ℝ,(∀i,s.P i=Z^(w i)) →
    (∑i,w i)-Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (C₂.absNorm:ℝ)-ε ≤
      ∑i : liveIndices B₂.val,w i.val.val := by
  filter_upwards [eventually_two_stage_width_padding N a ε ha hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ w hw
  have hh := actual_two_stage_live_width N a ha s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ Z hZ.1
  simp_rw [hw,Real.logb_rpow (zero_lt_one.trans hZ.1) hZ.1.ne'] at hh
  linarith [hZ.2]

end
end OAI.SevenEighths.Cycle63CommonSupply
#print axioms OAI.SevenEighths.Cycle63CommonSupply.actual_two_stage_live_width
#print axioms OAI.SevenEighths.Cycle63CommonSupply.eventual_two_stage_supplied_width
