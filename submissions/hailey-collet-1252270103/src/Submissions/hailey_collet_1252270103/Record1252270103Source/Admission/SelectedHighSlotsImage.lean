/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The final live slots after three actual allocations retain their original indices.
Finite large-slot conservation reuses Gao's original-slot and discard definitions. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedForcedGeometryData
import Submissions.hailey_collet_1252270103.Record12518109Natural.OriginalSlotPartition
import Submissions.hailey_collet_1252270103.Record12518109Natural.SmallSlotDiscard
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighSlots
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentAddedZeroUniform CenteredMomentCommonRadialData
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open Record12518109Natural CommonSupply MarkedPlain QRH.Record1252270103Low
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- The three actual child constructions take nested subtypes of original slots. -/
def finalEmbedding (B₁ : Tuple ι) (B₂ : Tuple (liveIndices B₁))
    (B₃ : Tuple (liveIndices B₂)) : liveIndices B₃ ↪ ι :=
  ⟨fun i=>i.val.val.val,fun _ _ h=>Subtype.ext (Subtype.ext (Subtype.ext h))⟩

def finalImage (B₁ : Tuple ι) (B₂ : Tuple (liveIndices B₁))
    (B₃ : Tuple (liveIndices B₂)) : Finset ι := originalSlots (finalEmbedding B₁ B₂ B₃)

/-- This is exactly the original image already used by the full singleton dictionary. -/
theorem finalImage_eq_slotRange (B₁ : Tuple ι) (B₂ : Tuple (liveIndices B₁))
    (B₃ : Tuple (liveIndices B₂)) :
    finalImage B₁ B₂ B₃ = slotRange (FirstFamily.childEmbedding B₁
      (FirstFamily.childEmbedding B₂ (FirstFamily.childEmbedding B₃ (Function.Embedding.refl _)))) := rfl

theorem finalImage_eq_map (B₁ : Tuple ι) (B₂ : Tuple (liveIndices B₁))
    (B₃ : Tuple (liveIndices B₂)) :
    finalImage B₁ B₂ B₃ = Finset.univ.map (finalEmbedding B₁ B₂ B₃) := by
  simp only [finalImage,originalSlots,Finset.map_eq_image]

/-- The full slot product in the literal third child retains every final image factor. -/
theorem third_child_slot_product (s : Input ι) (C₁ R : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (τ₁ : Character) (t₁ : ℝ)
    (C₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ : ℝ) (C₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).pools C₃)
    (τ₃ : Character) (t₃ : ℝ) :
    (∏i,(child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
      C₃ ((R*C₁)*C₂) B₃ τ₃ t₃).P i)=∏i∈finalImage B₁.val B₂.val B₃.val,s.P i :=
  prod_originalSlots (finalEmbedding B₁.val B₂.val B₃.val)
    (finalEmbedding B₁.val B₂.val B₃.val).injective s.P

/-- This monotonicity applies to every collision singleton subset, with its actual cutoff. -/
theorem largeSlots_mono (full T : Finset ι) (w : ι→ℝ) (wmin : ℝ) (hT : T⊆full) :
    largeSlots T w wmin ⊆ largeSlots full w wmin := by
  intro i hi
  obtain ⟨hi,hw⟩:=Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hT hi,hw⟩

/-- Nonnegative widths give the original upper budget for every large singleton subset. -/
theorem subset_large_widths (full T : Finset ι) (w : ι→ℝ) (wmin b : ℝ)
    (hT : T⊆full) (hw : ∀i,0≤w i) (hb : (∑i,w i)≤b) :
    0≤∑i∈largeSlots T w wmin,w i ∧
    (∑i∈largeSlots T w wmin,w i)≤∑i∈largeSlots full w wmin,w i ∧
    (∑i∈largeSlots full w wmin,w i)≤b := by
  exact ⟨Finset.sum_nonneg (fun i _=>hw i),
    Finset.sum_le_sum_of_subset_of_nonneg (largeSlots_mono full T w wmin hT) (fun i _ _=>hw i),
    (Finset.sum_le_univ_sum_of_nonneg hw).trans hb⟩

/-- A collision subset pays its full width; the remaining large width is
charged only to its complement in the final original image. -/
theorem subset_width_conservation (full T : Finset ι) (w : ι→ℝ) (wmin : ℝ)
    (hT : T⊆full) (hw : ∀i,0≤w i) :
    (∑i∈T,w i)+((∑i∈largeSlots full w wmin,w i)-(∑i∈largeSlots T w wmin,w i))≤
      ∑i∈full,w i := by
  have hlarge:=largeSlots_mono full T w wmin hT
  have hrem : largeSlots full w wmin \ largeSlots T w wmin ⊆ full \ T := by
    intro i hi
    obtain ⟨hif,hin⟩:=Finset.mem_sdiff.mp hi
    obtain ⟨hif,hwi⟩:=Finset.mem_filter.mp hif
    exact Finset.mem_sdiff.mpr ⟨hif,fun hit=>hin (Finset.mem_filter.mpr ⟨hit,hwi⟩)⟩
  have hh:=Finset.sum_le_sum_of_subset_of_nonneg hrem (fun i _ _=>hw i)
  have h₁:=Finset.sum_sdiff (f:=w) hlarge
  have h₂:=Finset.sum_sdiff (f:=w) hT
  linarith only [hh,h₁,h₂]

end
end QRH.Record1252270103Source.Admission.SelectedHighSlots
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.finalImage_eq_slotRange
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.finalImage_eq_map
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.third_child_slot_product
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.largeSlots_mono
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.subset_large_widths
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.subset_width_conservation
