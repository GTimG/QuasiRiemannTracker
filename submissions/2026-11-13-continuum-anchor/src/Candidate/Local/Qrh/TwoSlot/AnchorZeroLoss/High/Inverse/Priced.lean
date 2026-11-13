/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Convert the actual inverse HIGH leaf into the child-energy contract on an
arbitrary admissible rectangle, using its complete scalar price comparison. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.Contract

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section
variable [shift : WitnessShift]
open scoped Classical BigOperators
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Inverse.Leaf
open OAI OAI.SevenEighths

/-- No stage table is needed by the physical inverse HIGH consumer. -/
theorem inverse_high_energy_of_priced {fam : SlotClass → Prop} {ρ : AnchorRect}
    {a0 a1 k wlo excess : ℝ} (hP : InverseHighPriced fam a0 a1 k wlo)
    (hρ : ρ.Pmax≤1)
    (hledger : ∀P S : ℝ,ρ.Admissible P S 1 → highPriceFW a0 a1 k wlo P S 1≤excess) :
    InverseHighEnergy fam ρ k excess := by
  intro ε hε
  obtain ⟨mesh,hmesh,h⟩ := hP ε hε
  refine ⟨mesh,hmesh,fun K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data=>?_⟩
  obtain ⟨degree,c,C,Z₀,hc,hC,hZ₀,hb⟩ := h K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data
  refine ⟨degree,c,C,Z₀,hc,hC,hZ₀,fun Z hZ=>?_⟩
  intro ι _ _ hK L ell bc hv hv0 hcl g1 g2 g3 g4 g5 g6 P hadm rows hrows θ
  have hprice := hledger P (∑i,ell i) hadm
  have hP1 : P≤1 := by have := hadm.2.1; rw [mul_one] at this; exact this.trans hρ
  refine (hb Z hZ hK L ell bc hv hv0 hcl g1 g2 g3 g4 g5 g6 P hadm.1 hP1 rows hrows θ).trans ?_
  have hZ1 : 1≤Z := hZ₀.le.trans hZ
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)) hC.le

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.inverse_high_energy_of_priced
