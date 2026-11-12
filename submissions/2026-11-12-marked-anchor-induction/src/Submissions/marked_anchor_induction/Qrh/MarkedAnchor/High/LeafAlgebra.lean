/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Cofactor.Lift

/-!
# High.LeafAlgebra

Finite-product and scalar bookkeeping of the HIGH leaf `high_branch_mesh`:
* `whole_row_prod_le` — `∏ₓ nsₓ ≤ A^#T Z^(ν ∑ w)` from `nsₓ ≤ A Z^(ν wₓ)` (slots paid pointwise);
* `raw_batch_le` — one regular core batch: the pointwise row bound, small slots paid pointwise,
  large slots replaced by the raw slots, the raw/core comparison and the core detector bound;
* `rowNorm_le_coreWidth` — a core of a raw row of norm `≤ Z^M` has norm `≤ Z^(coreWidth Z M B)`;
* `height_factor_le` — the detector height `2π Y + 3 i y + x` is `≤ Ch (1+x) y`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths

/-- Slots paid pointwise. -/
theorem whole_row_prod_le {α : Type*} (T : Finset α) (ns w : α → ℝ) (A Z ν : ℝ) (hZ : 0 < Z)
    (hns0 : ∀ x ∈ T, 0 ≤ ns x) (hns : ∀ x ∈ T, ns x ≤ A * Z^(ν * w x)) :
    ∏ x ∈ T, ns x ≤ A^T.card * Z^(ν * ∑ x ∈ T, w x) := by
  calc ∏ x ∈ T, ns x ≤ ∏ x ∈ T, (A * Z^(ν * w x)) := Finset.prod_le_prod₀ hns0 hns
    _ = A^T.card * Z^(ν * ∑ x ∈ T, w x) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.rpow_sum_of_pos hZ, Finset.mul_sum]

/-- **One regular core batch, raw side.** -/
theorem raw_batch_le {R α : Type*} [DecidableEq α] (F : Finset R) (T big : Finset α)
    (row : R → ℝ) (ns : R → α → ℝ) (rawQ coreQ : R → α → ℂ) (K1 Zp Cs Rc : ℝ)
    (hK1 : 0 ≤ K1) (hZp : 0 ≤ Zp) (hCs : 1 ≤ Cs) (hbigT : big ⊆ T)
    (hns : ∀ u ∈ F, ∀ x ∈ T, 0 ≤ ns u x)
    (hrow : ∀ u ∈ F, row u ≤ K1 * Zp * ∏ x ∈ T, ns u x)
    (hsmall : ∀ u ∈ F, ∀ x ∈ T, x ∉ big → ns u x ≤ Cs)
    (hbig : ∀ u ∈ F, ∀ x ∈ big, ns u x ≤ max 1 (‖rawQ u x‖^2))
    (hcomp : ∑ u ∈ F, ∏ x ∈ big, max 1 (‖rawQ u x‖^2) ≤
      4^big.card * ∑ u ∈ F, ∏ x ∈ big, max 1 (‖coreQ u x‖^2))
    (hcore : (∑ u ∈ F, ∏ x ∈ big, max 1 (‖coreQ u x‖^2)) * Zp ≤ Rc) :
    ∑ u ∈ F, row u ≤ K1 * Cs^(T \ big).card * 4^big.card * Rc := by
  have hCs0 : 0 ≤ Cs := zero_le_one.trans hCs
  have hpt : ∀ u ∈ F, row u ≤ (K1 * Cs^(T \ big).card * Zp) * ∏ x ∈ big, max 1 (‖rawQ u x‖^2) := by
    intro u hu
    have hsplit := Finset.prod_sdiff hbigT (f := ns u)
    have hs1 : ∏ x ∈ T \ big, ns u x ≤ Cs^(T \ big).card := by
      calc ∏ x ∈ T \ big, ns u x ≤ ∏ _x ∈ T \ big, Cs :=
            Finset.prod_le_prod₀ (fun x hx => hns u hu x (Finset.mem_sdiff.mp hx).1)
              (fun x hx => hsmall u hu x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2)
        _ = Cs^(T \ big).card := Finset.prod_const _
    have hs2 : ∏ x ∈ big, ns u x ≤ ∏ x ∈ big, max 1 (‖rawQ u x‖^2) :=
      Finset.prod_le_prod₀ (fun x hx => hns u hu x (hbigT hx)) (fun x hx => hbig u hu x hx)
    have hs20 : 0 ≤ ∏ x ∈ big, ns u x := Finset.prod_nonneg fun x hx => hns u hu x (hbigT hx)
    have hprod : ∏ x ∈ T, ns u x ≤ Cs^(T \ big).card * ∏ x ∈ big, max 1 (‖rawQ u x‖^2) := by
      rw [← hsplit]
      exact mul_le_mul hs1 hs2 hs20 (pow_nonneg hCs0 _)
    calc row u ≤ K1 * Zp * ∏ x ∈ T, ns u x := hrow u hu
      _ ≤ K1 * Zp * (Cs^(T \ big).card * ∏ x ∈ big, max 1 (‖rawQ u x‖^2)) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg hK1 hZp)
      _ = _ := by ring
  have hc0 : 0 ≤ K1 * Cs^(T \ big).card * Zp := by positivity
  calc ∑ u ∈ F, row u ≤ ∑ u ∈ F, (K1 * Cs^(T \ big).card * Zp) * ∏ x ∈ big, max 1 (‖rawQ u x‖^2) :=
        Finset.sum_le_sum hpt
    _ = (K1 * Cs^(T \ big).card * Zp) * ∑ u ∈ F, ∏ x ∈ big, max 1 (‖rawQ u x‖^2) := by
        rw [Finset.mul_sum]
    _ ≤ (K1 * Cs^(T \ big).card * Zp) *
          (4^big.card * ∑ u ∈ F, ∏ x ∈ big, max 1 (‖coreQ u x‖^2)) :=
        mul_le_mul_of_nonneg_left hcomp hc0
    _ = (K1 * Cs^(T \ big).card * 4^big.card) *
          ((∑ u ∈ F, ∏ x ∈ big, max 1 (‖coreQ u x‖^2)) * Zp) := by ring
    _ ≤ (K1 * Cs^(T \ big).card * 4^big.card) * Rc :=
        mul_le_mul_of_nonneg_left hcore (by positivity)

/-- A core of a raw row of norm `≤ Z^M` lies below the core width. -/
theorem rowNorm_le_coreWidth {Z M : ℝ} (hZ : 1 < Z) (u : HeckeInverseAmplification.FreeRow)
    (B : HeckeInverseAmplification.NonzeroIdeal)
    (h : ProbeHighRowFamily.rowNorm u * (B.val.absNorm : ℝ)^6 ≤ Z^M) :
    ProbeHighRowFamily.rowNorm u ≤ Z^(Cofactor.coreWidth Z M B) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hN0 : 0 < (B.val.absNorm : ℝ) := by
    have hp : 0 < B.val.absNorm :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    exact_mod_cast hp
  have h6 : Z^(6 * Real.logb Z (B.val.absNorm : ℝ)) = (B.val.absNorm : ℝ)^6 := by
    rw [mul_comm, Real.rpow_mul hZ0.le, Real.rpow_logb hZ0 hZ.ne' hN0]
    norm_cast
  unfold Cofactor.coreWidth
  rw [Real.rpow_sub hZ0, h6, le_div_iff₀ (by positivity)]
  exact h

/-- The detector height bound. -/
theorem height_factor_le {Y y x : ℝ} {i h B : ℕ} (hY : Y ≤ y) (hy : 1 ≤ y) (hx : 0 ≤ x)
    (hi : (i : ℝ) ≤ ((B : ℝ) + 1) * ((h : ℝ) + 1)) (hh : (h : ℝ) ≤ x + 1) :
    1 + (2 * Real.pi * Y + ((3 * i : ℕ) : ℝ) * y + x) ≤ (8 + 6 * ((B : ℝ) + 1)) * (1 + x) * y := by
  have hpi : Real.pi < 7/2 := by linarith [Real.pi_lt_d2]
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hB : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have h1 : 2 * Real.pi * Y ≤ 7 * y := by nlinarith
  have h2 : ((3 * i : ℕ) : ℝ) * y ≤ 6 * ((B : ℝ) + 1) * (1 + x) * y := by
    push_cast
    have : (i : ℝ) ≤ 2 * ((B : ℝ) + 1) * (1 + x) := by nlinarith
    nlinarith
  have h3 : 1 + x ≤ (1 + x) * y := by nlinarith
  nlinarith

end
end Qrh.MarkedAnchor.High
