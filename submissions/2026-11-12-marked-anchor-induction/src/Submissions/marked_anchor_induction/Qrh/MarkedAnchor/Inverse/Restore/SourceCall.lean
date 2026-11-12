/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Collide

/-!
# Inverse.Restore.SourceCall — the child source on an injective slot product

**`source_inj_bound`**: from the child source at one scale (`InverseRectAt cls ρ Φ K mesh 1 1 ε Z
data deg C`: FULL slot products of every slot vector of the class), the INJECTIVE slot
product times the child inverse polynomial and a bounded row weight `w` (the small-slot factor, or
the trivially bounded column) has row moment
`≤ collisionProjectionCost 1 256 K · Cw² · C Z^(1+ε) ((1+‖θ‖+hv)^deg)²`
(`Collide.inj_le_full_energy`; every sub-embedding of the slots must be in the class and is
admitted by downward shortening of the slot width).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open OAI.SevenEighths.InverseMoment (childLogTest)
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

theorem source_inj_bound {cls : SlotClass} {ρ : AnchorRect} {Φ : ℝ → ℂ} {K : ℕ}
    {mesh ε Z : ℝ} {data : RowData} {deg : ℕ} {C : ℝ}
    (hsrc : InverseRectAt cls ρ Φ K mesh 1 1 ε Z data deg C) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    {ι : Type} [Fintype ι] [DecidableEq ι] (hK : Fintype.card ι ≤ K)
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (hv : ℝ) (hv0 : 0 ≤ hv)
    (hcls : ∀ (J : Type) [Fintype J] (f : J ↪ ι),
      cls J data (fun j => L (f j)) (fun j => ell (f j)) (fun j => β (f j)) Z hv)
    (h1 : ∀ i, 0 ≤ ell i) (h2 : ∀ i, ell i ≤ mesh) (h3 : ∀ i, ∀ P ∈ L i, Prime P)
    (h5 : ∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Set.Icc (1 : ℝ) 2)
    (h6 : ∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1)
    (h7 : ∀ i, (((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℕ) : ℝ)
      < Z^(ell i))
    (r : ℝ) (hadm : ρ.Admissible r (∑ i, ell i) 1)
    (rows : Finset NonzeroElement)
    (hrows : ∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z^(1:ℝ)) (θ : ℝ)
    (w : NonzeroElement → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw) (hw : ∀ u ∈ rows, ‖w u‖ ≤ Cw) :
    ∑ u ∈ rows, ‖polynomial (data.character u) true (childLogTest Φ θ) (Z^r) 0 0 * w u *
        injSlots u.val L β (fun i => Z^(ell i))‖^2 ≤
      QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
        (Cw^2 * (C * Z^((1:ℝ)+ε) * ((1+‖θ‖+hv)^deg)^2)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hE : 0 ≤ Cw^2 * (C * Z^((1:ℝ)+ε) * ((1+‖θ‖+hv)^deg)^2) := by positivity
  have hX : ∀ i, 1 ≤ Z^(ell i) := fun i => Real.one_le_rpow hZ (h1 i)
  have hp : ∀ i, ∀ p ∈ L i, p ≠ 0 := fun i p hp => (h3 i p hp).ne_zero
  have hN : ∀ i, ∀ p ∈ L i, (p.absNorm : ℝ) ≤ 2 * Z^(ell i) := by
    intro i p hp
    have := (h5 i p hp).2
    rwa [div_le_iff₀ (Real.rpow_pos_of_pos hZ0 _)] at this
  refine inj_le_full_energy rows (fun u => u.val)
    (fun u => polynomial (data.character u) true (childLogTest Φ θ) (Z^r) 0 0 * w u)
    L β (fun i => Z^(ell i)) _ hE K hK hX h6 hp hN ?_
  intro J _ f
  have hKJ : Fintype.card J ≤ K := (Fintype.card_le_of_embedding f).trans hK
  have hsum : (∑ j, ell (f j)) ≤ ∑ i, ell i := by
    rw [← Finset.sum_map Finset.univ f ell]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => h1 i)
  have hadm' : ρ.Admissible r (∑ j, ell (f j)) 1 :=
    AnchorRect.admissible_downward hadm hadm.1 le_rfl
      (Finset.sum_nonneg (fun j _ => h1 (f j))) hsum
  have hbd := hsrc hKJ (fun j => L (f j)) (fun j => ell (f j)) (fun j => β (f j)) hv hv0
    (hcls J f) (fun j => h1 (f j)) (fun j => h2 (f j)) (fun j => h3 (f j)) (fun j => h5 (f j))
    (fun j => h6 (f j)) (fun j => h7 (f j)) 1 le_rfl le_rfl r hadm' rows hrows θ
  unfold inverseMarkedSum at hbd
  calc ∑ v ∈ rows, ‖(polynomial (data.character v) true (childLogTest Φ θ) (Z^r) 0 0 * w v) *
        ∏ j, directSlot v.val (L (f j)) (β (f j)) (Z^(ell (f j)))‖^2
      ≤ ∑ v ∈ rows, Cw^2 * ‖polynomial (data.character v) true (childLogTest Φ θ) (Z^r) 0 0 *
          ∏ j, directSlot v.val (L (f j)) (β (f j)) (Z^(ell (f j)))‖^2 := by
        apply Finset.sum_le_sum
        intro v hv
        rw [show (polynomial (data.character v) true (childLogTest Φ θ) (Z^r) 0 0 * w v) *
            ∏ j, directSlot v.val (L (f j)) (β (f j)) (Z^(ell (f j))) =
            w v * (polynomial (data.character v) true (childLogTest Φ θ) (Z^r) 0 0 *
            ∏ j, directSlot v.val (L (f j)) (β (f j)) (Z^(ell (f j)))) by ring,
          norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hw v hv) 2)
          (sq_nonneg _)
    _ = Cw^2 * ∑ v ∈ rows, ‖polynomial (data.character v) true (childLogTest Φ θ) (Z^r) 0 0 *
          ∏ j, directSlot v.val (L (f j)) (β (f j)) (Z^(ell (f j)))‖^2 := by
        rw [Finset.mul_sum]
    _ ≤ Cw^2 * (C * Z^((1:ℝ)+ε) * ((1+‖θ‖+hv)^deg)^2) :=
        mul_le_mul_of_nonneg_left hbd (sq_nonneg _)

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.source_inj_bound
