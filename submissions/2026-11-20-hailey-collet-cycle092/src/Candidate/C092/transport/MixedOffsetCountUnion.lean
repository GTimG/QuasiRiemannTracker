/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal native bank classes retain original physical amplitude labels and weights. -/
import Candidate.C092.transport.MixedOffsetCountBank
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorFiberPartition HeckeDetectorAmplitudeFirst HeckeDetectorPhysicalSelection
open QRH.Cycle092.MixedOffsetBank
local notation "O" => HeckeFamily.O
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
local instance c092LocalInst_Candidate_C092_transport_MixedOffsetCountUnion_9844a63bf630fa01_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {S : Finset (Ideal O)} {hS : SourceExclusions S} {η : Character} {rows : Finset FreeRow}
variable {U a ε t₀ γ T allowance : ℝ} {i : ℕ}

/-- The slots and original physical phase label are shared across all
cutoffs. `fixed_phase` is an exact amplitude-cell membership identity,
not a numerical amplitude estimate or a count/moment assumption. -/
structure BankLayout {Slot : Type*}
    (B : SourceBank M H hH S hS η rows U a ε t₀ γ T allowance i) where
  u₀ : FreeRow
  member : u₀∈rows
  row_norm : ∀u∈rows,rowNorm u≤U
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0 ≤ mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀s∈slots,0<widths s
  widths_mesh : ∀s∈slots,widths s ≤ mesh
  supply : 7/37 ≤ ∑s∈slots,widths s
  bin : BinLabel slots ((2*a-1)/2) binWidth
  fixed_phase : ∀u∈rows,amplitudeLabel slots U ((2*a-1)/2) binWidth binWidth_pos widths
    (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) u=bin

namespace BankLayout
variable {Slot : Type*} {B : SourceBank M H hH S hS η rows U a ε t₀ γ T allowance i}

def batch (L : BankLayout (Slot:=Slot) B) (j : Offset) :=
  nativeBatch B L.u₀ L.member L.row_norm L.slots L.profile L.upper L.widths L.external L.mesh L.binWidth
    L.mesh_nonneg L.binWidth_pos L.widths_pos L.widths_mesh L.supply j

def family (L : BankLayout (Slot:=Slot) B) := (L.batch 0).family

def witness (L : BankLayout (Slot:=Slot) B) (j : Offset) (u : FreeRow) :
    SupportedWitness (L.family u) U a ε (cutoff t₀ γ j) T allowance i :=
  (L.batch j).witness u

def labels (L : BankLayout (Slot:=Slot) B) (u : FreeRow) := (L.witness 0 u).label

def common (L : BankLayout (Slot:=Slot) B) (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U)) :=
  classRows rows L.labels (fun j u=>(L.witness j u).left) (fun j u=>(L.witness j u).right) σ

theorem fixed_label (L : BankLayout (Slot:=Slot) B) (j : Offset) (u : FreeRow) :
    (L.witness j u).label=L.labels u :=
  (native_common_presentation B L.u₀ L.member L.row_norm L.slots L.profile L.upper L.widths L.external
    L.mesh L.binWidth L.mesh_nonneg L.binWidth_pos L.widths_pos L.widths_mesh L.supply j 0 u).2.1

theorem fixed_zero (L : BankLayout (Slot:=Slot) B) (j k : Offset) (u : FreeRow) :
    (L.witness j u).zero=(L.witness k u).zero :=
  (native_common_presentation B L.u₀ L.member L.row_norm L.slots L.profile L.upper L.widths L.external
    L.mesh L.binWidth L.mesh_nonneg L.binWidth_pos L.widths_pos L.widths_mesh L.supply j k u).2.2

/-- The common class is inside the literal native fiber with the ORIGINAL
physical phase bin, at every offset. Source mean and physical slots are not
recomputed on error masks or selected prime subproducts. -/
theorem common_subset_fiber (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U)) (j : Offset) :
    L.common σ ⊆ (L.batch j).fiberRows L.bin σ.1 (σ.2.1 j) (σ.2.2 j) :=
  class_subset_fiber rows L.family U a ε t₀ γ T allowance i L.witness L.labels
    (fun k u _=>L.fixed_label k u) L.slots L.binWidth L.binWidth_pos L.widths
    (physical M H (fun u:FreeRow=>u.val) L.profile L.upper L.widths L.external U) L.bin L.fixed_phase σ j

def fiber (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) :=
  (L.batch j).fiber L.bin σ.1 (σ.2.1 j) (σ.2.2 j) (hne.mono (L.common_subset_fiber σ j))

theorem common_subset (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) : L.common σ⊆(L.fiber σ hne j).rows :=
  L.common_subset_fiber σ j

theorem fiber_mean (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) :
    (L.fiber σ hne j).q=classMean L.slots ((2*a-1)/2) L.binWidth L.widths L.bin := rfl

theorem fiber_lengths (L : BankLayout (Slot:=Slot) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))
    (hne : (L.common σ).Nonempty) (j : Offset) :
    (L.fiber σ hne j).r=inverseLength U σ j ∧ (L.fiber σ hne j).m=ordinaryLength U σ j := ⟨rfl,rfl⟩

/-- This equality preserves the complete physical integrand and its row
weights in the original order. No positivity or discarded tail is used. -/
theorem weighted_union (L : BankLayout (Slot:=Slot) B) (weight : FreeRow→ℝ) :
    (∑u∈rows,weight u)=∑σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U),
      ∑u∈L.common σ,weight u :=
  weighted_partition rows L.labels (fun j u=>(L.witness j u).left) (fun j u=>(L.witness j u).right) weight

/-- Complete all-offset descriptor multiplicity, on one original phase bin. -/
theorem descriptor_multiplicity :
    Fintype.card (Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U))=
      Fintype.card (Sum Bool (RayQuotient.Characters M H))*(dyadicLength U)^65537*(dyadicLength U)^65537 :=
  descriptor_count _

end BankLayout
#print axioms BankLayout.common_subset_fiber
#print axioms BankLayout.fiber_mean
#print axioms BankLayout.weighted_union
end
end QRH.Cycle092.MixedOffsetCount
