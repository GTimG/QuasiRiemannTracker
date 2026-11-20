/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact finite assembly for the actual ordinary/inverse ticket classes.
This is summation algebra; genuine source application remains explicit.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafCount
import Candidate.C092.transport.RegularColoredTerminalLeafNative
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open QRH.Cycle092.TerminalActualRow

/-- Applied source packets may select different finite native indices on
each occupied class. Summing their fixed coefficients is uniform in the
actual class choices. Only the genuine ticket dictionary costs U^loss. -/
theorem terminal_actual_branch_aggregate {Slot Key Idx : Type}
    [Fintype Slot] [Fintype Key] [DecidableEq Key] [Fintype Idx]
    (T : Finset Slot) (rows : Finset FreeRow) (key : rows → Key)
    (ordinary : Key → Prop) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot → FreeRow → ℂ)
    (U exponent loss K : ℝ) (hU : 0<U) (hK : 0≤K)
    (hcard : (Fintype.card Key:ℝ)≤K*U^loss)
    (Co Ci : Idx → ℝ) (hCo : ∀k,0≤Co k) (hCi : ∀k,0≤Ci k)
    (ho : ∀tag,ordinary tag → (classRows rows key tag).Nonempty →
      ∃k,StrongPair.finiteEnergyOn T (classRows rows key tag) η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark≤Co k*U^exponent)
    (hi : ∀tag,¬ordinary tag → (classRows rows key tag).Nonempty →
      ∃k,StrongPair.finiteEnergyOn T (classRows rows key tag) η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark≤Ci k*U^exponent) :
    StrongPair.finiteEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark≤
      K*(∑ k,(Co k+Ci k))*U^(exponent+loss) := by
  classical
  let C := ∑ k,(Co k+Ci k)
  have hC : 0≤C := Finset.sum_nonneg (fun k _=>add_nonneg (hCo k) (hCi k))
  have hcm (k : Idx) : Co k≤C ∧ Ci k≤C := by
    have h := Finset.single_le_sum (fun k _=>add_nonneg (hCo k) (hCi k)) (Finset.mem_univ k)
    exact ⟨(le_add_of_nonneg_right (hCi k)).trans h,(le_add_of_nonneg_left (hCo k)).trans h⟩
  have he : 0≤U^exponent := Real.rpow_nonneg hU.le _
  have hclass (tag : Key) : StrongPair.finiteEnergyOn T (classRows rows key tag) η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark≤C*U^exponent := by
    by_cases hn : (classRows rows key tag).Nonempty
    · by_cases hOrd : ordinary tag
      · obtain ⟨k,hk⟩:=ho tag hOrd hn
        exact hk.trans (mul_le_mul_of_nonneg_right (hcm k).1 he)
      · obtain ⟨k,hk⟩:=hi tag hOrd hn
        exact hk.trans (mul_le_mul_of_nonneg_right (hcm k).2 he)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      simp only [StrongPair.finiteEnergyOn,Finset.sum_empty]
      exact mul_nonneg hC he
  rw [terminal_class_energy_partition T rows key η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark]
  calc
    _ ≤ ∑_ : Key,C*U^exponent := Finset.sum_le_sum (fun tag _=>hclass tag)
    _ = (Fintype.card Key:ℝ)*(C*U^exponent) := by simp
    _ ≤ (K*U^loss)*(C*U^exponent) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hC he)
    _ = _ := by rw [Real.rpow_add hU];dsimp [C];ring

#print axioms terminal_actual_branch_aggregate
end
end QRH.Cycle092.RegularColoredForward
