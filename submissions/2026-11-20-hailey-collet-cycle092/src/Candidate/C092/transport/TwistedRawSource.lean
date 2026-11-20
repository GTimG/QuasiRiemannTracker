/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Independent ordinary colors in the literal signed raw source. The two colors
   are never divided, and native mark-only ν is not silently enlarged. -/
import Candidate.C092.transport.RawSidesZeroTailSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentCommonProfile
open CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationBox
open QRH.SilDensitySplit.CubeFree.FP
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) subtypeDecEq {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {ι : Type*} [Fintype ι]

/-- The two fixed ordinary factors, on their actual allocated ideals. -/
def ordinaryColor (ω₁ ω₂ : Id → ℂ) (v : Tuple ι) : ℂ :=
  ω₁ (v (Sum.inr 0)) * ω₂ (v (Sum.inr 1))

@[simp] theorem ordinaryColor_remaining (ω₁ ω₂ : Id → ℂ) (B u : Tuple ι) :
    ordinaryColor ω₁ ω₂ (remainingTuple B u) = ordinaryColor ω₁ ω₂ u := rfl

/-- Multiplicativity uses no inverse, including when an allocated ideal is
    ramified for either character. -/
theorem ordinaryColor_allocation (ω₁ ω₂ : Id →*₀ ℂ) (B u : Tuple ι) :
    ordinaryColor ω₁ ω₂ (fun i => B i * u i) =
      ordinaryColor ω₁ ω₂ B * ordinaryColor ω₁ ω₂ (remainingTuple B u) := by
  simp only [ordinaryColor, map_mul, remainingTuple_plain]
  ring

/-- The literal cube-free source projection is retained before aggregation. -/
def coloredTuple (H : Id) (ω₁ ω₂ : Id → ℂ) (F : Tuple ι → ℂ)
    (v : Tuple ι) : ℂ :=
  MixedCommonCoefficient.tupleWeight H v * ordinaryColor ω₁ ω₂ v * F v

def coloredColumn (S : Finset (Tuple ι)) (H : Id) (ω₁ ω₂ : Id → ℂ)
    (F : Tuple ι → ℂ) : Id → ℂ :=
  finiteColumnCoefficient S (coloredTuple H ω₁ ω₂ F)

/-- Exact finite source identity for any subsequent row kernel. This is also
    valid for distinct ordinary characters and their true zero values. -/
theorem colored_root_eq_columns (S : Finset (Tuple ι)) (H : Id)
    (ω₁ ω₂ : Id → ℂ) (F : Tuple ι → ℂ) (row : Id → ℂ) :
    (∑ v ∈ S, coloredTuple H ω₁ ω₂ F v * row (finiteTupleProduct v)) =
      ∑ I ∈ finiteColumns S, coloredColumn S H ω₁ ω₂ F I * row I := by
  symm
  unfold coloredColumn finiteColumnCoefficient
  simp_rw [Finset.sum_mul]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := finiteColumns S) (g := finiteTupleProduct)
    (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    (fun v => coloredTuple H ω₁ ω₂ F v * row (finiteTupleProduct v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro v hv
  rw [(Finset.mem_filter.mp hv).2]

/-- Setting both ordinary colors to one recovers precisely the native source. -/
@[simp] theorem coloredColumn_one (S : Finset (Tuple ι)) (H : Id)
    (F : Tuple ι → ℂ) :
    coloredColumn S H (fun _ => 1) (fun _ => 1) F =
      finiteColumnCoefficient S (fun v => MixedCommonCoefficient.tupleWeight H v * F v) := by
  unfold coloredColumn
  congr 1
  funext v
  simp [coloredTuple, ordinaryColor]

/-- Independent ordinary characters retain their actual zero at a ramified
    ordinary coordinate; no quotient convention can turn it into a unit. -/
theorem coloredTuple_zero (H : Id) (ω₁ ω₂ : Id → ℂ) (F : Tuple ι → ℂ)
    (v : Tuple ι) (hz : ω₁ (v (Sum.inr 0)) = 0 ∨ ω₂ (v (Sum.inr 1)) = 0) :
    coloredTuple H ω₁ ω₂ F v = 0 := by
  rcases hz with hz | hz <;> simp [coloredTuple, ordinaryColor, hz]

/-- An arbitrary frozen marked tuple and ordinary rectangle has the exact two
    signed pieces, with the same independent factors on each piece. -/
theorem independent_signed_rectangle (S₁ S₂ : Finset Id) (ω₁ ω₂ : Id → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    (∑ I ∈ S₁, ∑ J ∈ S₂, ω₁ I * ω₂ J *
      CenteredMomentRectangle.idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)) =
      (∑ I ∈ S₁, ω₁ I * W₁ ((Ideal.absNorm (B₁*I) : ℝ)/X₁)) *
        (∑ J ∈ S₂, ω₂ J * W₂ ((Ideal.absNorm (B₂*J) : ℝ)/X₂)) -
      (∑ I ∈ S₁, ω₁ I * W₁ ((Ideal.absNorm (B₁*I) : ℝ)/Y₁)) *
        (∑ J ∈ S₂, ω₂ J * W₂ ((Ideal.absNorm (B₂*J) : ℝ)/Y₂)) := by
  simp only [CenteredMomentRectangle.idealRectangle, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro I hI <;>
    apply Finset.sum_congr rfl <;> intro J hJ <;> ring

/-- Actual common extraction, including cube-free/injective source projection,
    frozen marked profiles and shortened ordinary rectangle. Both live colors
    survive on the residual source. The row multiplier F is arbitrary. -/
theorem colored_residual_source
    (H : Id) (S : (ι ⊕ Fin 2) → Finset Id)
    (hS : ∀ j, ∀ I ∈ S j, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ S (Sum.inl i), Prime I)
    (C R seed : Id) (hC : C ≠ 0) (hsC : seed ∣ C)
    (B : CenteredMomentCommonAllocationSum.actualAllocations S C)
    (ω₁ ω₂ : Id →*₀ ℂ) (ν : ι → Id → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id)
    (F : Tuple (liveIndices B.val) → ℂ) :
    let hB := (CenteredMomentCommonAllocationSum.allocation_data S C B
      (Finset.mem_filter.mp B.property).1).1
    (∑ u ∈ residualBoxes S C B.val hB,
      coloredTuple H ω₁ ω₂
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed)
        (fun i => B.val i * u i) * F (remainingTuple B.val u)) =
      (MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val *
        frozenCoefficient B.val C R ν Wslot P) *
      ∑ v ∈ liveBox S B.val hB,
        coloredTuple H ω₁ ω₂
          (liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) v * F v := by
  dsimp only
  let hB := (CenteredMomentCommonAllocationSum.allocation_data S C B
    (Finset.mem_filter.mp B.property).1).1
  have hh := residual_source_profile S hp B.val hB C R seed
    (Finset.mem_filter.mp B.property).2 hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂
    (fun v => MixedCommonCoefficient.tupleWeight H v * ordinaryColor ω₁ ω₂ v * F v)
  rw [ite_eq_left (allocation_frozen_gate S hp C B.val
    (Finset.mem_filter.mp B.property).1)] at hh
  calc
    _ = (MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val) *
      ∑ u ∈ residualBoxes S C B.val hB,
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed
          (fun i => B.val i * u i) *
          (MixedCommonCoefficient.tupleWeight H (remainingTuple B.val u) *
            ordinaryColor ω₁ ω₂ (remainingTuple B.val u) * F (remainingTuple B.val u)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      unfold coloredTuple
      rw [MixedCommonCoefficient.actual_weight_split H S hS C hC B u hu hp,
        ordinaryColor_allocation]
      ring
    _ = _ := by
      rw [hh, ← mul_assoc]
      congr 1
      unfold liveBox liveProfile coloredTuple
      apply Finset.sum_congr
      · ext v
        simp only [Fintype.mem_piFinset]
      · intro v hv
        ring

#print axioms colored_root_eq_columns
#print axioms ordinaryColor_allocation
#print axioms independent_signed_rectangle
#print axioms colored_residual_source
end
end QRH.Cycle092.TwistedRawSource
