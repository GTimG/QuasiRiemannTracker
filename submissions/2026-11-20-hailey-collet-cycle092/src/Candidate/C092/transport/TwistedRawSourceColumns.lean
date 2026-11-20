/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Literal independently colored raw coefficients through every actual common
   allocation. Native divisor and puncture restrictions remain in the source. -/
import Candidate.C092.transport.TwistedRawSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentCommonProfile
open CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum
open CenteredMomentSourceRow CenteredMomentFirstSectorTransform
open CenteredMomentHeckeExpansion CenteredMomentFirstSectors
open QRH.SilDensitySplit.CubeFree.FP
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) subtypeColumnsDecEq {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
local instance (priority := 2000) sumColumnsDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _
variable {ι : Type*} [Fintype ι]

/-- Every original ordinary allocation extracts both fixed characters, while
    keeping both fixed characters on the live ordinary coordinates. -/
theorem colored_column_allocations
    (H : Id) (S : (ι ⊕ Fin 2) → Finset Id)
    (hS : ∀ j, ∀ I ∈ S j, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ S (Sum.inl i), Prime I)
    (C R seed a : Id) (hC : C ≠ 0) (ha : a ≠ 0)
    (hCa : IsCoprime C a) (hsC : seed ∣ C)
    (ω₁ ω₂ : Id →*₀ ℂ) (ν : ι → Id → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    coloredColumn (Fintype.piFinset S) H ω₁ ω₂
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed) (C*a) =
      ∑ B : actualAllocations S C,
        (MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val *
          frozenCoefficient B.val C R ν Wslot P) *
        coloredColumn
          (liveBox S B.val (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          H ω₁ ω₂
          (liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  unfold coloredColumn finiteColumnCoefficient
  simp only [Finset.sum_filter]
  have halloc := original_coefficient_allocated S hS C a hC ha hCa
    (coloredTuple H ω₁ ω₂
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed))
  change (∑ v ∈ Fintype.piFinset S, if finiteTupleProduct v = C*a then
    coloredTuple H ω₁ ω₂
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed) v else 0) = _ at halloc
  rw [halloc]
  apply Finset.sum_congr rfl
  intro B hmem
  let hB := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hh := colored_residual_source H S hS hp C R seed hC hsC B ω₁ ω₂ ν
    Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (fun v => if finiteTupleProduct v = a then 1 else 0)
  dsimp only at hh
  calc
    _ = ∑ u ∈ residualBoxes S C B.val hB,
      coloredTuple H ω₁ ω₂
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed)
        (fun i => B.val i * u i) *
        (if finiteTupleProduct (remainingTuple B.val u) = a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hf : ∀ i, B.val (Sum.inl i) ≠ 1 → u (Sum.inl i) = 1 := by
        intro i hi
        have hui := hu
        simp only [residualBoxes, Fintype.mem_piFinset] at hui
        exact prime_residual_frozen B.val hB S hp i hi _
          (Finset.mem_filter.mp (hui (Sum.inl i))).1
      have hp := remaining_product B.val u hf
      change (∏ i, u i) = finiteTupleProduct (remainingTuple B.val u) at hp
      rw [hp]
      split_ifs <;> simp
    _ = _ := hh.trans (by
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      split_ifs <;> simp)

/-- Actual native source with two independent ordinary colors. The original
    literal coefficient, including the true signed rectangle, is multiplied. -/
def sourceColumn {a b : ℝ} (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (seed : Id) : Id → ℂ :=
  finiteColumnCoefficient (Fintype.piFinset (MixedPrincipalAllocations.tuplePools s))
    (fun v => MixedOriginalSecondZero.originalTuple s ha seed v * ordinaryColor ω₁ ω₂ v)

@[simp] theorem sourceColumn_one {a b : ℝ}
    (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a) (seed : Id) :
    sourceColumn s ha (fun _ => 1) (fun _ => 1) seed =
      MixedPrincipalWindow.sourceCoefficient s ha seed := by
  unfold sourceColumn MixedPrincipalWindow.sourceCoefficient MixedHeightEnergy.originalColumn
  simp only [ordinaryColor, mul_one]
  rfl

/-- The original pair's independently colored tuple root is exactly this
    aggregate, with no unproved source-energy replacement. -/
theorem source_root_eq_columns {a b : ℝ}
    (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (seed : Id) (row : Id → ℂ) :
    (∑ v ∈ Fintype.piFinset (MixedPrincipalAllocations.tuplePools s),
      MixedOriginalSecondZero.originalTuple s ha seed v * ordinaryColor ω₁ ω₂ v *
        row (finiteTupleProduct v)) =
      ∑ I ∈ MixedPrincipalWindow.sourceColumns s, sourceColumn s ha ω₁ ω₂ seed I * row I := by
  unfold sourceColumn MixedPrincipalWindow.sourceColumns finiteColumnCoefficient
  simp_rw [Finset.sum_mul]
  symm
  have h := Finset.sum_fiberwise_of_maps_to
    (s := Fintype.piFinset (MixedPrincipalAllocations.tuplePools s))
    (t := finiteColumns (Fintype.piFinset (MixedPrincipalAllocations.tuplePools s)))
    (g := finiteTupleProduct)
    (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    (fun v => MixedOriginalSecondZero.originalTuple s ha seed v * ordinaryColor ω₁ ω₂ v *
      row (finiteTupleProduct v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro v hv
  rw [(Finset.mem_filter.mp hv).2]

/-- Authentic first Poisson/sector reconstruction with the colored original
    source. η can be the principal character, avoiding any character quotient. -/
theorem source_energy_fixed_transforms {a b : ℝ}
    (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (seed : Id) (η : Character) (m A : HeckeFamily.O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2 : HeckeFamily.O) ∣ m)
    (W : SchwartzMap ℝ ℂ) (K : ℝ) (hK : 0 < K) :
    finiteHeckeEnergy η m A t (MixedPrincipalWindow.sourceColumns s)
      (sourceColumn s ha ω₁ ω₂ seed) W K =
      ∑ p : commonLabels (supportedColumns (MixedPrincipalWindow.sourceColumns s))
        (supportedColumns (MixedPrincipalWindow.sourceColumns s)),
        rowWeight η m A 1 t p.val.1 * star (rowWeight η m A 1 t p.val.2) *
          sectorFixedTransform η m A t (MixedPrincipalWindow.sourceColumns s)
            (sourceColumn s ha ω₁ ω₂ seed) p.val.1 p.val.2
            (commonLabels_supported _ p).1 (commonLabels_supported _ p).2 W K := by
  exact energy_fixed_transforms η m A t hmLam hm2 _ _ W K hK

#print axioms colored_column_allocations
#print axioms sourceColumn_one
#print axioms source_root_eq_columns
#print axioms source_energy_fixed_transforms
end
end QRH.Cycle092.TwistedRawSource
