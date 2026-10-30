/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalSelectedNormContract
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeInverseAmplification ProbeHighRowFamily
local notation "O" => ActualEisensteinCubic.O
/-- Aggregate original-slot inlet. Individual cells and inactive-slot
padding are internal to its derivation from NaturalSelectedCellNorm. -/
def FineNaturalAggregateNormBound (N : ℕ) (Z A P mesh Cslot smin δ K : ℝ) : Prop :=
  ∀ (d : SelectedSlotData N) (cores : Finset FreeRow) (S : Finset (Ideal O)) (Y L : ℝ),
    d.Bounded Z mesh Cslot → smin ≤ ∑ i, d.width i →
    (∀ u ∈ cores, Z^(δ*∑ i, d.width i) ≤ ∏ i, ‖d.polynomial i u.val‖^2) →
    1 ≤ Y → Y ≤ Z^A → (∀ u ∈ cores, rowNorm u ≤ Y) →
    1 ≤ L → L ≤ Z^P → (∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L) →
    selectedNorm (cores.image Subtype.val) S ≤ K*(L+Y^(1-δ)*L^δ)

def FineNaturalAggregateSlotNorm : Prop :=
  ∀ A P loss : ℝ, 0 < A → 3*A+1 ≤ P → 0 < loss →
  ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot smin : ℝ),
    1 ≤ Cslot → 0 < smin → ∃ C Z₀ : ℝ, 0 < C ∧
    ∀ Z mesh δ : ℝ, Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
      (500001/1000000:ℝ) ≤ δ → δ ≤ 3/4 →
      FineNaturalAggregateNormBound N Z A P mesh Cslot smin δ (C*Z^loss)

end
end Qrh.JointDetector
