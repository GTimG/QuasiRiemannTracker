/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Every bank offset is a genuine native source Batch on exactly the same rows. -/
import Candidate.C092.transport.MixedOffsetBankSource
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetBank
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorSupportedWitness HeckeDetectorBatch
local notation "O" => HeckeFamily.O
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
local instance c092LocalInst_Candidate_C092_transport_MixedOffsetBankNative_c36429a75b954c10_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {S : Finset (Ideal O)} {hS : SourceExclusions S} {η : Character} {rows : Finset FreeRow}
variable {U a ε t₀ γ T allowance : ℝ} {i : ℕ}

/-- Widths, original slot profiles and physical heights are shared by all
cutoffs. Only the auxiliary inverse/ordinary witness changes with offset. -/
def nativeBatch {Slot : Type*}
    (B : SourceBank M H hH S hS η rows U a ε t₀ γ T allowance i)
    (u₀ : FreeRow) (hu₀ : u₀∈rows) (hrow : ∀u∈rows,rowNorm u≤U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0 ≤ mesh) (hb : 0<binWidth)
    (hwp : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s ≤ mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) (j : Offset) :
    Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε (cutoff t₀ γ j) T allowance i :=
  retainedSourceBatch M H hH S hS η rows u₀ hu₀ U a ε (cutoff t₀ γ j) T allowance i
    (fun u hu=>B.witness j ⟨u,hu⟩) hrow slots profile upper widths external mesh binWidth hm hb hwp hwm hsupply

theorem native_same_zero {Slot : Type*}
    (B : SourceBank M H hH S hS η rows U a ε t₀ γ T allowance i)
    (u₀ : FreeRow) (hu₀ : u₀∈rows) (hrow : ∀u∈rows,rowNorm u≤U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0 ≤ mesh) (hb : 0<binWidth)
    (hwp : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s ≤ mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) (j : Offset) (u : FreeRow) (hu : u∈rows) :
    let N:=nativeBatch B u₀ hu₀ hrow slots profile upper widths external mesh binWidth hm hb hwp hwm hsupply j
    N.rows=rows ∧ N.data=sourceMomentData M H hH S hS.prime η ∧
    N.reverse=sourceMomentReverse M H ∧
    (N.witness u).label=B.label ⟨u,hu⟩ ∧ (N.witness u).zero=B.zero ⟨u,hu⟩ := by
  dsimp [nativeBatch,retainedSourceBatch]
  have he : (⟨retainedProjection rows u₀ u,retainedProjection_mem rows u₀ hu₀ u⟩ : rows)=⟨u,hu⟩ :=
    Subtype.ext (retainedProjection_of_mem rows u₀ u hu)
  exact ⟨rfl,rfl,rfl,(B.fixed_label j _).trans (congrArg B.label he),
    (B.fixed_zero j _).trans (congrArg B.zero he)⟩

/-- The native extension outside the retained rows is also shared across
all offsets. It does not introduce an independent choice of presentation. -/
theorem native_common_presentation {Slot : Type*}
    (B : SourceBank M H hH S hS η rows U a ε t₀ γ T allowance i)
    (u₀ : FreeRow) (hu₀ : u₀∈rows) (hrow : ∀u∈rows,rowNorm u≤U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0 ≤ mesh) (hb : 0<binWidth)
    (hwp : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s ≤ mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) (j k : Offset) (u : FreeRow) :
    let Nj:=nativeBatch B u₀ hu₀ hrow slots profile upper widths external mesh binWidth hm hb hwp hwm hsupply j
    let Nk:=nativeBatch B u₀ hu₀ hrow slots profile upper widths external mesh binWidth hm hb hwp hwm hsupply k
    Nj.family u=Nk.family u ∧
    (Nj.witness u).label=(Nk.witness u).label ∧ (Nj.witness u).zero=(Nk.witness u).zero := by
  dsimp [nativeBatch,retainedSourceBatch]
  exact ⟨rfl,(B.fixed_label j _).trans (B.fixed_label k _).symm,
    (B.fixed_zero j _).trans (B.fixed_zero k _).symm⟩

#print axioms native_common_presentation
#print axioms native_same_zero
end
end QRH.Cycle092.MixedOffsetBank
