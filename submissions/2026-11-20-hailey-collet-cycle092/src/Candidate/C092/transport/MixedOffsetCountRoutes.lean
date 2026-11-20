/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite route partition after the entire original same-zero bank is fixed. -/
import Candidate.C092.transport.MixedOffsetCountUnion
import Candidate.C092.transport.MixedOffsetCountAllLong
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows
open QRH.Cycle092.MixedOffsetBank
local notation "O" => HeckeFamily.O

/-- None is all-long. Some(j,true) is a sufficient-count class at the first
short index; Some(j,false) retains the first-short mixed class. This is a
logical partition of already frozen descriptors, not a new detector choice. -/
def bankRoute {Label : Type*} {L : ℕ} (U q₀ : ℝ) (deficit : Descriptor Label L→ℝ)
    (σ : Descriptor Label L) : Option (Offset×Bool) :=
  (firstShort (inverseLength U σ)).map (fun j=>(j,decide (4*q₀/3 ≤ deficit σ)))

/-- Every descriptor appears exactly once, preserving its whole original
class weight. The route labels add no extra multiplicity to the union. -/
theorem route_partition {Label : Type*} [Fintype Label] {L : ℕ} (U q₀ : ℝ)
    (deficit : Descriptor Label L→ℝ) (weight : Descriptor Label L→ℝ) :
    (∑σ : Descriptor Label L,weight σ)=
      ∑route : Option (Offset×Bool),
        ∑σ∈(Finset.univ.filter (fun σ=>bankRoute U q₀ deficit σ=route)),weight σ := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (g:=bankRoute U q₀ deficit) (fun _ _=>Finset.mem_univ _) weight

theorem route_none {Label : Type*} {L : ℕ} (U q₀ : ℝ) (deficit : Descriptor Label L→ℝ)
    (σ : Descriptor Label L) (h : bankRoute U q₀ deficit σ=none) :
    ∀j : Offset,1 ≤ inverseLength U σ j := by
  have hf : firstShort (inverseLength U σ)=none := by
    cases he : firstShort (inverseLength U σ) with
    | none => rfl
    | some j => simp [bankRoute,he] at h
  exact (firstShort_none _).mp hf

theorem route_some {Label : Type*} {L : ℕ} (U q₀ : ℝ) (deficit : Descriptor Label L→ℝ)
    (σ : Descriptor Label L) (j : Offset) (large : Bool)
    (h : bankRoute U q₀ deficit σ=some (j,large)) :
    firstShort (inverseLength U σ)=some j ∧
      (large=true ↔ 4*q₀/3 ≤ deficit σ) := by
  cases he : firstShort (inverseLength U σ) with
  | none => simp [bankRoute,he] at h
  | some k =>
    have hh : (k,decide (4*q₀/3 ≤ deficit σ))=(j,large) := by
      simpa only [bankRoute,he,Option.map_some,Option.some.injEq] using h
    have hk : k=j:=congrArg Prod.fst hh
    subst k
    refine ⟨rfl,?_⟩
    have hb : decide (4*q₀/3 ≤ deficit σ)=large:=congrArg Prod.snd hh
    rw [←hb]
    simp only [decide_eq_true_eq]

section Native
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
local instance c092LocalInst_Candidate_C092_transport_MixedOffsetCountRoutes_cc86be8adebfdb3c_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {S : Finset (Ideal O)} {hS : SourceExclusions S} {η : Character} {rows : Finset FreeRow}
variable {U a ε t₀ γ T allowance : ℝ} {i : ℕ}
variable {Slot : Type*} {B : SourceBank M H hH S hS η rows U a ε t₀ γ T allowance i}

/-- The all-long route really has an amplified last native fiber. -/
theorem BankLayout.last_long (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (hall : firstShort (inverseLength U σ)=none) :
    1 ≤ (L.fiber σ hne ⟨65536,by omega⟩).r := by
  rw [(L.fiber_lengths σ hne _).1]
  exact (firstShort_none _).mp hall _

/-- The current and preceding native fibers retain their actual bank
indices. At j=0 the prior-long gate is discharged by the index alternative. -/
theorem BankLayout.first_short (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) (hf : firstShort (inverseLength U σ)=some j) :
    (L.fiber σ hne j).r<1 ∧
      (j.val=0 ∨ 1 ≤ (L.fiber σ hne (previous j)).r) := by
  rw [(L.fiber_lengths σ hne j).1]
  refine ⟨(firstShort_some _ j hf).1,?_⟩
  by_cases hj : j.val=0
  · exact Or.inl hj
  · refine Or.inr ?_
    rw [(L.fiber_lengths σ hne _).1]
    exact previous_long _ j hf (Nat.pos_of_ne_zero hj)
end Native

#print axioms route_partition
#print axioms route_some
#print axioms BankLayout.first_short
#print axioms BankLayout.last_long
end
end QRH.Cycle092.MixedOffsetCount
