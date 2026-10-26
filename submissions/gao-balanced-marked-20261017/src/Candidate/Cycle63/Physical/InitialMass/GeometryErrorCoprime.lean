import Candidate.Cycle63.Physical.InitialMass.SecondSourceControls
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationSlotGap

set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAllocatedRayDictionary CenteredMomentAmplificationSlotGap
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open HeckePrimeAnnular ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance errorCoprimeFiniteQuotient : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The full stored prime pool has an annulus cap, including entries where
the smooth slot profile vanishes. -/
theorem actual_full_slot_norm_cap {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(η₀ : Character)(θ : α→RayQuotient.Characters M H)
    (w σ v : α→ℝ)(W : ℝ→ℂ)(b Z eta : ℝ)(hZ : 1≤Z)
    (hm : Matches M H hH s η₀ θ w σ v W b Z)(hw : ∀i,w i≤eta) :
    ∀i I,I∈s.slots i→Prime I ∧ (I.absNorm:ℝ)≤max 1 b*Z^eta := by
  intro i I hI
  rw [hm.pool i] at hI
  have hmem := Finset.mem_filter.mp hI
  refine ⟨hmem.2.1,?_⟩
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have ha := hmem.1
  change I∈idealsUpTo ⌊max 1 b*Z^(w i)⌋₊ at ha
  have hn : (I.absNorm:ℝ)≤max 1 b*Z^(w i) :=
    (Nat.cast_le.mpr (mem_idealsUpTo.mp ha).2).trans (Nat.floor_le (by positivity))
  exact hn.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hw i)) (le_max_of_le_left (by norm_num)))

/-- A genuine amplifier-prime gap separates it from all stored original
slots. No nonzero-profile restriction is used. -/
theorem actual_full_slot_coprime {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(η₀ : Character)(θ : α→RayQuotient.Characters M H)
    (w σ v : α→ℝ)(W : ℝ→ℂ)(b Z eta ell : ℝ)(hZ : 1≤Z)
    (hm : Matches M H hH s η₀ θ w σ v W b Z)(hw : ∀i,w i≤eta)
    (Q : Ideal O)(hQ : Prime Q)(hQN : Z^ell≤(Q.absNorm:ℝ))
    (hgap : max 1 b*Z^eta<Z^ell) :
    ∀i I,I∈s.slots i→IsCoprime Q I := by
  intro i I hI
  have hc := actual_full_slot_norm_cap M H hH s η₀ θ w σ v W b Z eta hZ hm hw i I hI
  exact ((HeckeInverseAmplification.prime_coprime_iff ⟨Q,hQ⟩ I).mpr
    (amplifier_not_dvd_slot Q I hQ hc.1 Z ell eta (max 1 b) hgap hQN hc.2)).symm

/-- Common allocation deletes slots, so full-pool coprimality is inherited
by the unpruned first child used in the extracted-source formalization. -/
theorem actual_child_full_slot_coprime {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(Q : Ideal O)(hc : ∀i I,I∈s.slots i→IsCoprime Q I)
    (C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ) :
    ∀i I,I∈(child s C R B χ t).slots i→IsCoprime Q I := by
  intro i I hI
  exact hc i.val I hI

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_full_slot_norm_cap
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_full_slot_coprime
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_child_full_slot_coprime
