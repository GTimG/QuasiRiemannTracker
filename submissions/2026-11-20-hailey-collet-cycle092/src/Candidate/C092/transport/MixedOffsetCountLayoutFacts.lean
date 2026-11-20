/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original physical slots and source data on every frozen bank fiber. -/
import Candidate.C092.transport.MixedOffsetCountPhaseUnion
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount.BankLayout
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorPhysicalSelection
open QRH.Cycle092.MixedOffsetBank
local notation "O" => HeckeFamily.O
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
local instance c092LocalInst_Candidate_C092_transport_MixedOffsetCountLayoutFacts_4a5a223cd4de685b_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {S : Finset (Ideal O)} {hS : SourceExclusions S} {η : Character} {rows : Finset FreeRow}
variable {U a ε t₀ γ T allowance : ℝ} {i : ℕ}
variable {Slot : Type*} {B : SourceBank M H hH S hS η rows U a ε t₀ γ T allowance i}

theorem physical_fields (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) :
    (L.fiber σ hne j).slots=L.slots ∧ (L.fiber σ hne j).profile=L.profile ∧
    (L.fiber σ hne j).upper=L.upper ∧ (L.fiber σ hne j).widths=L.widths ∧
    (L.fiber σ hne j).external=L.external ∧ (L.fiber σ hne j).binWidth=L.binWidth :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem source_fields (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) :
    (L.fiber σ hne j).rowData=sourceMomentData M H hH S hS.prime η σ.1 ∧
    (L.fiber σ hne j).reverse=sourceMomentReverse M H σ.1 := ⟨rfl,rfl⟩

theorem physical_product (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) (selected : Finset Slot) (u : FreeRow) :
    (L.fiber σ hne j).physicalProduct selected u=
      ∏s∈selected,physical M H (fun u:FreeRow=>u.val) L.profile L.upper L.widths L.external U u s := rfl

/-- The original FULL amplitude mean is shared at every native cutoff and
on every common row, independent of the numerator error-slot mask. -/
theorem original_full_mean (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) (u : FreeRow) (hu : u∈L.common σ) :
    rowMean L.slots U ((2*a-1)/2) L.binWidth L.widths
      (physical M H (fun u:FreeRow=>u.val) L.profile L.upper L.widths L.external U) u=
      (L.fiber σ hne j).q := by
  have hrow : u∈rows:=class_subset rows L.labels (fun j u=>(L.witness j u).left)
    (fun j u=>(L.witness j u).right) σ hu
  have hamp : u∈amplitudeRows rows L.slots U ((2*a-1)/2) L.binWidth L.binWidth_pos L.widths
      (physical M H (fun u:FreeRow=>u.val) L.profile L.upper L.widths L.external U) L.bin :=
    Finset.mem_filter.mpr ⟨hrow,L.fixed_phase u hrow⟩
  rw [L.fiber_mean σ hne j]
  exact rowMean_eq rows L.slots U ((2*a-1)/2) L.binWidth L.binWidth_pos L.widths _ L.bin u hamp

#print axioms physical_product
#print axioms original_full_mean
end
end QRH.Cycle092.MixedOffsetCount.BankLayout
