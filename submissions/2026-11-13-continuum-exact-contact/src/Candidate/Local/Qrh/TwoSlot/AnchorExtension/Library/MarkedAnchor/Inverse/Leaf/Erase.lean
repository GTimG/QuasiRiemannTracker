/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Leaf.HighInput
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.Choice

/-!
# Inverse.Leaf.Erase

Finite tools of the LOW inverse leaf:

* `SubClosed` — a slot class closed under passing to a sub-collection of WHOLE slots (the index
  type shrinks to a subtype `↥F`; no slot is ever cut). `canonicalSlots` and `canonicalFamily`
  are closed (a sub-collection of canonical slots is canonical).
* `inverseMarkedSum_restrict` — the marked sum of the sub-collection `↥F` is the sum with the
  product over `F`.
* `inverseMarkedSum_split` — splitting the rows by a predicate.
* `erase_row`, `low_erasure` — whole-slot erasure for the cofactor `M_v` (the actual inverse
  polynomial): `‖D ∏_univ s‖² ≤ (∏_{univ\F} pay) ‖D ∏_F s‖²` (HC
  `LowErasure.cofactor_product_erasure` for `D = M_v`, reproved here for the inverse sum), and
  summed over LOW rows, with the retained sum extended to ALL rows of the ball (positivity).
* `erasure_payment_le` — `∏_E c Z^(k ell + lam) ≤ (max 1 c)^K Z^(k ∑_E ell + K lam)`.
* `erasure_choice` — a fixed retained sub-collection `F` of whole slots with
  `∑_F ell ≤ Sp` and erased width `∑_{univ\F} ell ≤ max 0 (S - Sp + mesh)` (greedy, `Select.Choice`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Leaf
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-! ## Sub-collections of whole slots -/

/-- A slot class closed under sub-collections of whole slots. -/
def SubClosed (cls : SlotClass) : Prop :=
  ∀ (ι : Type) (data : RowData) (L : ι → Finset (Ideal O)) (ell : ι → ℝ)
    (β : ι → Ideal O → ℂ) (Z hv : ℝ) (F : Finset ι),
    cls ι data L ell β Z hv →
      cls F data (fun i => L i.val) (fun i => ell i.val) (fun i => β i.val) Z hv

theorem canonicalSlots_subClosed (W : ℝ → ℂ) (σ : ℝ) : SubClosed (canonicalSlots W σ) := by
  intro ι data L ell β Z hv F hc
  obtain ⟨rayM, hne, H, hH, θ, v, hvb, h⟩ := hc
  exact ⟨rayM, hne, H, hH, fun i => θ i.val, fun i => v i.val, fun i => hvb i.val,
    fun i => h i.val⟩

theorem canonicalFamily_subClosed : ∀ cls, canonicalFamily cls → SubClosed cls := by
  rintro cls ⟨W, _, _, rayM, hne, G, hH, rfl⟩
  intro ι data L ell β Z hv F hc
  exact canonicalSlotsRay_restrict W _ rayM G hH ι data L ell β Z hv F hc

theorem anySlots_subClosed : SubClosed anySlots :=
  fun _ _ _ _ _ _ _ _ _ => trivial

/-- The marked sum of a sub-collection. -/
theorem inverseMarkedSum_restrict (data : RowData) (Φ : ℝ → ℂ) {ι : Type} [Fintype ι]
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (F : Finset ι)
    (rows : Finset HeckeInverseAmplification.NonzeroElement) (Z r θ : ℝ) :
    inverseMarkedSum data Φ (fun i : F => L i.val) (fun i : F => ell i.val)
        (fun i : F => β i.val) rows Z r θ =
      ∑ u ∈ rows, ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0 *
        (∏ i ∈ F, directSlot u.val (L i) (β i) (Z^(ell i)))‖^2 := by
  unfold inverseMarkedSum
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.prod_coe_sort F (fun i => directSlot u.val (L i) (β i) (Z^(ell i)))]

/-- Splitting the rows by a predicate. -/
theorem inverseMarkedSum_split (data : RowData) (Φ : ℝ → ℂ) {ι : Type} [Fintype ι]
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ)
    (rows : Finset HeckeInverseAmplification.NonzeroElement) (Z r θ : ℝ)
    (p : HeckeInverseAmplification.NonzeroElement → Prop) :
    inverseMarkedSum data Φ L ell β rows Z r θ =
      inverseMarkedSum data Φ L ell β (rows.filter p) Z r θ +
        inverseMarkedSum data Φ L ell β (rows.filter (fun u => ¬ p u)) Z r θ := by
  unfold inverseMarkedSum
  exact (Finset.sum_filter_add_sum_filter_not rows p _).symm

theorem inverseMarkedSum_nonneg (data : RowData) (Φ : ℝ → ℂ) {ι : Type} [Fintype ι]
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ)
    (rows : Finset HeckeInverseAmplification.NonzeroElement) (Z r θ : ℝ) :
    0 ≤ inverseMarkedSum data Φ L ell β rows Z r θ :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ## Erasure -/

/-- Whole-slot erasure for an arbitrary cofactor `D` (here the actual inverse polynomial). -/
theorem erase_row {ι : Type} [Fintype ι] [DecidableEq ι] (D : ℂ) (s : ι → ℂ) (F : Finset ι)
    (pay : ι → ℝ) (hpay : ∀ i ∈ Finset.univ \ F, ‖s i‖^2 ≤ pay i) :
    ‖D * ∏ i, s i‖^2 ≤ (∏ i ∈ Finset.univ \ F, pay i) * ‖D * ∏ i ∈ F, s i‖^2 := by
  have he : D * ∏ i, s i = (∏ i ∈ Finset.univ \ F, s i) * (D * ∏ i ∈ F, s i) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ F)]
    ring
  rw [he, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) hpay

/-- **LOW erasure.** On rows where every erased slot is bounded by `pay`, the marked sum is at
most `∏_{erased} pay` times the marked sum of the retained sub-collection `F` over ALL rows. -/
theorem low_erasure (data : RowData) (Φ : ℝ → ℂ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ)
    (rows low : Finset HeckeInverseAmplification.NonzeroElement) (hlow : low ⊆ rows)
    (Z r θ : ℝ) (F : Finset ι) (pay : ι → ℝ) (hpay0 : ∀ i, 0 ≤ pay i)
    (hpay : ∀ u ∈ low, ∀ i ∈ Finset.univ \ F,
      ‖directSlot u.val (L i) (β i) (Z^(ell i))‖^2 ≤ pay i) :
    inverseMarkedSum data Φ L ell β low Z r θ ≤
      (∏ i ∈ Finset.univ \ F, pay i) *
        inverseMarkedSum data Φ (fun i : F => L i.val) (fun i : F => ell i.val)
          (fun i : F => β i.val) rows Z r θ := by
  rw [inverseMarkedSum_restrict]
  have hP0 : 0 ≤ ∏ i ∈ Finset.univ \ F, pay i := Finset.prod_nonneg (fun i _ => hpay0 i)
  unfold inverseMarkedSum
  calc ∑ u ∈ low, ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0 *
          (∏ i, directSlot u.val (L i) (β i) (Z^(ell i)))‖^2
      ≤ ∑ u ∈ low, (∏ i ∈ Finset.univ \ F, pay i) *
          ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0 *
            (∏ i ∈ F, directSlot u.val (L i) (β i) (Z^(ell i)))‖^2 :=
        Finset.sum_le_sum (fun u hu => erase_row _ _ F pay (hpay u hu))
    _ = (∏ i ∈ Finset.univ \ F, pay i) * ∑ u ∈ low,
          ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0 *
            (∏ i ∈ F, directSlot u.val (L i) (β i) (Z^(ell i)))‖^2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hP0
        exact Finset.sum_le_sum_of_subset_of_nonneg hlow (fun _ _ _ => sq_nonneg _)

/-- The erasure payment of the slots `E` at price `c Z^(k ell + lam)` per slot. -/
theorem erasure_payment_le {ι : Type} (E : Finset ι) (ell : ι → ℝ) (c k lam Z : ℝ) (K : ℕ)
    (hc : 0 ≤ c) (hlam : 0 ≤ lam) (hZ : 1 ≤ Z) (hE : E.card ≤ K) :
    ∏ i ∈ E, (c * Z^(k * ell i + lam)) ≤
      (max 1 c)^K * Z^(k * (∑ i ∈ E, ell i) + K * lam) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.rpow_sum_of_pos hZ0,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have h1 : c^E.card ≤ (max 1 c)^K :=
    (pow_le_pow_left₀ hc (le_max_right 1 c) _).trans
      (pow_le_pow_right₀ (le_max_left 1 c) hE)
  have hEK : (E.card : ℝ) * lam ≤ K * lam :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hE) hlam
  have h2 : Z^(k * (∑ i ∈ E, ell i) + E.card * lam) ≤ Z^(k * (∑ i ∈ E, ell i) + K * lam) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hZ0.le _) (by positivity)

/-- The retained sub-collection: whole slots of total width `≤ Sp`, erased width
`≤ max 0 (S - Sp + mesh)` where `S` is the total width. -/
theorem erasure_choice {ι : Type} [Fintype ι] [DecidableEq ι] (ell : ι → ℝ) (mesh Sp : ℝ)
    (hell : ∀ i, 0 ≤ ell i) (hmesh : ∀ i, ell i ≤ mesh) (hSp : 0 ≤ Sp) :
    ∃ F : Finset ι, (∑ i ∈ F, ell i) ≤ Sp ∧
      (∑ i ∈ Finset.univ \ F, ell i) ≤ max 0 ((∑ i, ell i) - Sp + mesh) := by
  obtain ⟨F, -, hFS, hF⟩ := greedy_selection ell mesh Finset.univ (fun i _ => hell i)
    (fun i _ => hmesh i) Sp hSp
  refine ⟨F, hFS, ?_⟩
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ F)]
  rcases hF with hF | rfl
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left (by simp)

end
end Qrh.MarkedAnchor.Inverse.Leaf

#print axioms Qrh.MarkedAnchor.Inverse.Leaf.low_erasure
#print axioms Qrh.MarkedAnchor.Inverse.Leaf.erasure_choice
