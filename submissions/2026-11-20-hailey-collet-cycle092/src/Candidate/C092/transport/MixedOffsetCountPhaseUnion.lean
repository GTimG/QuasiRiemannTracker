/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original phase-label and full same-zero bank descriptor reconstruction. -/
import Candidate.C092.transport.MixedOffsetCountUnion
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic ProbePhysical ProbeHighRowFamily HeckeDetectorWitnessRows
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Cycle092.MixedOffsetBank
local notation "O" => HeckeFamily.O
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
local instance c092LocalInst_Candidate_C092_transport_MixedOffsetCountPhaseUnion_5569411d853dfcd4_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {S : Finset (Ideal O)} {hS : SourceExclusions S} {η : Character}

/-- At the literal original amplitude cell the phase label is PROVED from
membership. It is not a per-row phase or analytic amplitude hypothesis.
All widths/profile/height data are copied into every native bank offset. -/
def BankLayout.ofAmplitudeCell {Slot : Type*}
    (originalRows : Finset FreeRow) (U a ε t₀ γ T allowance : ℝ) (i : ℕ)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0 ≤ mesh) (hb : 0<binWidth)
    (hwp : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s ≤ mesh)
    (hsupply : 7/37 ≤ ∑s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth)
    (B : SourceBank M H hH S hS η
      (amplitudeRows originalRows slots U ((2*a-1)/2) binWidth hb widths
        (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) bin)
      U a ε t₀ γ T allowance i)
    (hne : (amplitudeRows originalRows slots U ((2*a-1)/2) binWidth hb widths
        (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) bin).Nonempty)
    (hrow : ∀u∈amplitudeRows originalRows slots U ((2*a-1)/2) binWidth hb widths
        (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) bin,rowNorm u≤U) :
    BankLayout (Slot:=Slot) B where
  u₀:=hne.choose
  member:=hne.choose_spec
  row_norm:=hrow
  slots:=slots
  profile:=profile
  upper:=upper
  widths:=widths
  external:=external
  mesh:=mesh
  binWidth:=binWidth
  mesh_nonneg:=hm
  binWidth_pos:=hb
  widths_pos:=hwp
  widths_mesh:=hwm
  supply:=hsupply
  bin:=bin
  fixed_phase:=fun _ hu=>(Finset.mem_filter.mp hu).2

/-- The ORIGINAL phase labels are exhausted with the original scalar row
weights. Physical contour choices and every coefficient/tail in `weight`
are retained literally and in order. -/
theorem weighted_phase_partition {Slot : Type*} (originalRows : Finset FreeRow)
    (slots : Finset Slot) (U a binWidth : ℝ) (hb : 0<binWidth) (widths : Slot→ℝ)
    (physical : FreeRow→Slot→ℂ) (weight : FreeRow→ℝ) :
    (∑u∈originalRows,weight u)=∑bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∑u∈amplitudeRows originalRows slots U ((2*a-1)/2) binWidth hb widths physical bin,weight u := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (g:=amplitudeLabel slots U ((2*a-1)/2) binWidth hb widths physical)
    (fun u hu=>Finset.mem_univ _) weight

/-- Two exact finite reconstructions: all original phase labels, then ALL
dyads of ALL 65,537 offsets, with one common zero/presentation per row.
Empty original phase cells contribute exactly zero and require no bank. -/
theorem original_phase_descriptor_union {Slot : Type*}
    (originalRows : Finset FreeRow) (slots : Finset Slot) (U a ε T allowance : ℝ) (i : ℕ)
    (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (binWidth : ℝ) (hb : 0<binWidth)
    (t₀ γ : BinLabel slots ((2*a-1)/2) binWidth→ℝ)
    (banks : ∀bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀hne : (amplitudeRows originalRows slots U ((2*a-1)/2) binWidth hb widths
        (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) bin).Nonempty,
      SourceBank M H hH S hS η
        (amplitudeRows originalRows slots U ((2*a-1)/2) binWidth hb widths
          (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) bin)
        U a ε (t₀ bin) (γ bin) T allowance i)
    (layouts : ∀bin hne,BankLayout (Slot:=Slot) (banks bin hne)) (weight : FreeRow→ℝ) :
    (∑u∈originalRows,weight u)=
      ∑bin : BinLabel slots ((2*a-1)/2) binWidth,
        if hne : (amplitudeRows originalRows slots U ((2*a-1)/2) binWidth hb widths
            (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) bin).Nonempty then
          ∑σ : Descriptor (Sum Bool (RayQuotient.Characters M H)) (dyadicLength U),
            ∑u∈(layouts bin hne).common σ,weight u
        else 0 := by
  trans ∑bin : BinLabel slots ((2*a-1)/2) binWidth,
    ∑u∈amplitudeRows originalRows slots U ((2*a-1)/2) binWidth hb widths
      (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) bin,weight u
  · exact weighted_phase_partition originalRows slots U a binWidth hb widths
      (physical M H (fun u:FreeRow=>u.val) profile upper widths external U) weight
  apply Finset.sum_congr rfl
  intro bin _
  split_ifs with hne
  · exact (layouts bin hne).weighted_union weight
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

#print axioms BankLayout.ofAmplitudeCell
#print axioms weighted_phase_partition
#print axioms original_phase_descriptor_union
end
end QRH.Cycle092.MixedOffsetCount
