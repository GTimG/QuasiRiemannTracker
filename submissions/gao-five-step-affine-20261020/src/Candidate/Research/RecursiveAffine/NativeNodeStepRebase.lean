/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeNodeStep
import Candidate.Research.RecursiveAffine.NativeSlotFlatten

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands
open Cycle63FinalLow Cycle63InitialMass Cycle153RegionalLow

/-- The actual clipped plain length scales exactly under a positive
change of base. This is an identity, not a bound for a desired child. -/
theorem native_length_rebase {Z u X : ℝ} (hZ : 1<Z) (hu : 0<u) :
    u*length (Z^u) X=length Z X := by
  unfold length
  exact unit_mul_logb_rebase hZ hu

/-- Literal total length, including all original slot weights, is
invariant in the original global unit. -/
theorem native_total_length_rebase {ι : Type*} [Fintype ι]
    (weight : ι→ℝ) {Z parentUnit u X₁ X₂ : ℝ}
    (hZ : 1<Z) (hparent : 0<parentUnit) (hu : 0<u) :
    (parentUnit*u)*(length (Z^u) X₁+length (Z^u) X₂+
      ∑i,weight i/(parentUnit*u)) =
    parentUnit*(length Z X₁+length Z X₂)+∑i,weight i := by
  rw [←Finset.sum_div]
  calc
    _ = parentUnit*(u*length (Z^u) X₁)+parentUnit*(u*length (Z^u) X₂)+∑i,weight i := by
      field_simp [ne_of_gt hparent,ne_of_gt hu]
      <;> ring
    _ = _ := by rw [native_length_rebase hZ hu,native_length_rebase hZ hu];ring

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- Flatten the SAME original remaining slots and rebase the measured
physical daughter to its actual chosen unit. This provides the literal
`hlen` and `hslots` expressions needed by the real child-geometry
constructor; no energy, capacity or future-model fact is assumed. -/
theorem actual_native_child_length_rebase (N : ReachableNode C j)
    (s : Input N.slots) (ch : Chain s) (χ : Character) (t : ℝ)
    (n : ℕ) (b Mrow omega xi reserve : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (Rdel : Finset N.slots) :
    let r := nativeNodeStepValues N s ch χ t n b Mrow omega xi reserve g second L alloc Rdel
    let slots := nativeSurvivingSlots N.slots (ch.indices L alloc) Rdel
    0<r.u →
    (∑i : slots,C.originalWeight i)=r.childSlots ∧
    (N.unit*r.u)*(length (N.localBase^r.u) (rawDaughterScale (ch.final χ t) second L alloc 0)+
      length (N.localBase^r.u) (rawDaughterScale (ch.final χ t) second L alloc 1)+
      ∑i : slots,C.originalWeight i/(N.unit*r.u))=r.childA := by
  intro r slots hu
  have hslots : (∑i : slots,C.originalWeight i)=
      ∑i∈ch.indices L alloc\Rdel,C.originalWeight i := by
    rw [native_surviving_sum]
    exact Finset.sum_coe_sort (ch.indices L alloc\Rdel) (fun i : N.slots=>C.originalWeight i)
  refine ⟨hslots,?_⟩
  have hlen := native_total_length_rebase (fun i : slots=>C.originalWeight i)
    (X₁:=rawDaughterScale (ch.final χ t) second L alloc 0)
    (X₂:=rawDaughterScale (ch.final χ t) second L alloc 1)
    N.localBase_gt_one N.unit_pos hu
  rw [hlen,hslots]
  change N.unit*(length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
    length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1))+
    (∑i∈ch.indices L alloc\Rdel,C.originalWeight i)=
    N.unit*(length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
      length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
      ∑i∈ch.indices L alloc\Rdel,C.originalWeight i/N.unit)
  rw [←Finset.sum_div,mul_add]
  field_simp [ne_of_gt N.unit_pos]
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_native_child_length_rebase
