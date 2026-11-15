/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Batch

/-!
# High.BatchAbs

The batch bound of `High.Batch` at an absolute scale `dU` (`U = Z^dU`), for the HIGH leaf:

* `detEx_homog`: `detEx … (M x) (M y) M = M · detEx … x y 1` for `M > 0`;
* `anchor_batch_abs`: the per-bin cutoffs come from `exists_cutoff` at the absolute point
  `(P, dU·S, dU)`. The result is
  `(∑ ‖∏Q‖²) · U^(ν P/dU) ≤ K · U^((dU + highPriceF a0 a1 k P (dU S) dU + ε')/dU + losses)`;
* `AnchorFiberMoments.congr_family`: change the detector family off the fiber rows;
* `AnchorFiberMoments.scale_slots`: multiply the slots by constants in `[0,1]`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles

theorem detEx_homog [shift : WitnessShift] (a0 a1 ν e w x y M : ℝ) (hM : 0 < M) :
    detEx a0 a1 ν e w (M*x) (M*y) M = M * detEx a0 a1 ν e w x y 1 := by
  have h1 : min (M*y) (M*sig a0 a1 w) = M * min y (sig a0 a1 w) :=
    (mul_min_of_nonneg _ _ hM.le).symm
  have hA : M - ν*M*w - e*(M*min y (sig a0 a1 w)) =
      M*(1 - ν*1*w - e*min y (1*sig a0 a1 w)) := by rw [one_mul]; ring
  have hB : M/6 + (5/6-ν)*M*(3*w/2 + WitnessShift.value) =
      M*(1/6 + (5/6-ν)*1*(3*w/2 + WitnessShift.value)) := by ring
  unfold detEx shortCnt longCnt
  rw [h1, hA, hB, ← mul_max_of_nonneg _ _ hM.le]
  ring

/-- **Batch bound at an absolute scale.** -/
theorem anchor_batch_abs {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (dU U a ε T allowance mesh binWidth εm C height a0 a1 k P ε' : ℝ) (i : ℕ)
    (hdU : 0 < dU) (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1≤3/4) (hk0 : 0 ≤ k) (hk : k ≤ 2*a-1)
    (hε0 : 0≤ε) (hε : ε≤1/1000000000000) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hC : 0≤C) (hheight : 0≤height) (hε' : 0 < ε')
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤mesh)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2)
    (hwit : ∀ t : ℝ, 1 ≤ t → t ≤ 3/2 →
      Nonempty (∀u,SupportedWitness (χ u) U a ε t T allowance i))
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀ w ∈ cutoffs, ∀ wit : (∀ u, SupportedWitness (χ u) U a ε (3*w/2+1/1000000000000) T allowance i),
      ∀ F : Finset Row, F ⊆ rows → ∀ (j : Label) (J K : Fin (dyadicLength U)),
      (∀ u ∈ F, (wit u).label = j ∧ (wit u).left = J ∧ (wit u).right = K) →
      AnchorFiberMoments F slots χ Q widths U a ε (3*w/2+1/1000000000000) a0 a1 w εm C height j J K) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) * U^((2*a-1)*(P/dU)) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^((dU + highPriceF a0 a1 k P (dU*∑s∈slots,widths s) dU + ε')/dU +
        (154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s))) := by
  have hL : 0 ≤ ∑s∈slots,widths s := Finset.sum_nonneg (fun s hs => (hw s hs).le)
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hν0 : 0 ≤ 2*a-1 := by linarith
  let cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ := fun bin =>
    if h : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        ∈ classes k then
      Classical.choose (exists_cutoff (a0 := a0) (a1 := a1) hk0 h P (dU*∑s∈slots,widths s) dU hε')
    else cutLo
  have hcut : ∀ bin, cut bin ∈ cutoffs := by
    intro bin
    by_cases h : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        ∈ classes k
    · simp only [cut, dif_pos h]
      exact (Classical.choose_spec (exists_cutoff (a0 := a0) (a1 := a1) hk0 h P
        (dU*∑s∈slots,widths s) dU hε')).1
    · simp only [cut, dif_neg h]; exact cutLo_mem
  have hcutspec : ∀ bin, (2*a-1, 2*weightedMean slots widths
      (binValue slots ((2*a-1)/2) binWidth bin)) ∈ classes k →
      detEx a0 a1 (2*a-1) (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        (cut bin) P (dU*∑s∈slots,widths s) dU <
        highPriceF a0 a1 k P (dU*∑s∈slots,widths s) dU + ε' := by
    intro bin h
    simp only [cut, dif_pos h]
    exact (Classical.choose_spec (exists_cutoff (a0 := a0) (a1 := a1) hk0 h P
      (dU*∑s∈slots,widths s) dU hε')).2
  have ht : ∀ bin, 1 ≤ 3*cut bin/2+1/1000000000000 ∧ 3*cut bin/2+1/1000000000000 ≤ 3/2 := by
    intro bin
    obtain ⟨h1, h2⟩ := hcut bin
    unfold cutLo at h1; unfold cutHi at h2
    constructor <;> linarith
  let witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000000000) T allowance i :=
    fun bin => Classical.choice (hwit _ (ht bin).1 (ht bin).2)
  have hsum := anchor_weighted_row_sum rows slots χ Q widths U a ε T allowance mesh binWidth εm C
    height a0 a1 (1 - (2*a-1)*(P/dU) +
      (highPriceF a0 a1 k P (dU*∑s∈slots,widths s) dU + ε')/dU) i hU ha hν
    hε0 hε hmesh hbin hC hheight hfreq hw hwm hL ha1 ha1' cut hcut witness hQ
    (fun bin j J K => hmom (cut bin) (hcut bin) (witness bin) _ (Finset.filter_subset _ _) j J K
      (fun u hu => by
        obtain ⟨-, h1, h2, h3, -⟩ := anchorFiber_fields rows slots widths Q χ U a ε T allowance
          binWidth i hbin cut witness bin j J K u hu
        exact ⟨h1, h2, h3⟩))
    (by
      intro bin hex
      obtain ⟨u, -, hocc⟩ := hex
      obtain ⟨hm0, hm1⟩ := occupied_bin_mean slots widths hw U (2*a-1) binWidth hν0 bin
        (Q u) hocc
      have hcl : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
          ∈ classes k := ⟨hk, hν, by linarith, by linarith⟩
      have h1 := hcutspec bin hcl
      have h2 := fiberTarget_add_eq a0 a1 (2*a-1)
        (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)) (cut bin) (P/dU)
        (∑s∈slots,widths s)
      have h3 := detEx_homog a0 a1 (2*a-1)
        (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)) (cut bin) (P/dU)
        (∑s∈slots,widths s) dU hdU
      rw [mul_div_cancel₀ _ hdU.ne'] at h3
      rw [h3] at h1
      have h4 : detEx a0 a1 (2*a-1)
          (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)) (cut bin)
          (P/dU) (∑s∈slots,widths s) 1 <
          (highPriceF a0 a1 k P (dU*∑s∈slots,widths s) dU + ε')/dU := by
        rw [lt_div_iff₀ hdU]; linarith
      linarith)
  have hP : 0 ≤ U^((2*a-1)*(P/dU)) := Real.rpow_nonneg hU0.le _
  refine (mul_le_mul_of_nonneg_right hsum hP).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.rpow_add hU0]
  congr 2
  simp only [add_div, div_self hdU.ne']
  ring

/-- The cutoff of one class against the detector price alone. -/
theorem exists_cutoff_det {a0 a1 k : ℝ} (hk0 : 0 ≤ k) {p : ℝ × ℝ} (hp : p ∈ classes k)
    (P s M : ℝ) {ε' : ℝ} (hε : 0 < ε') :
    ∃ w ∈ cutoffs, detEx a0 a1 p.1 p.2 w P s M < max 0 (detPrice a0 a1 k P s M) + ε' := by
  have h1 := infW_le_detPrice (a0 := a0) (a1 := a1) hk0 hp P s M
  have h2 := le_max_right 0 (detPrice a0 a1 k P s M)
  exact exists_lt_infW (by linarith)

/-- **Detector-only variant**: the same with `max 0 (detPrice a0 a1 k P S 1)` (no tiny-core term)
in place of `highPriceF a0 a1 k P S 1`; used for core scales `d > 1`. -/
theorem anchor_batch_det {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth εm C height a0 a1 k P ε' : ℝ) (i : ℕ)
    (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1≤3/4) (hk0 : 0 ≤ k) (hk : k ≤ 2*a-1)
    (hε0 : 0≤ε) (hε : ε≤1/1000000000000) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hC : 0≤C) (hheight : 0≤height) (hε' : 0 < ε')
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤mesh)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2)
    (hwit : ∀ t : ℝ, 1 ≤ t → t ≤ 3/2 →
      Nonempty (∀u,SupportedWitness (χ u) U a ε t T allowance i))
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀ w ∈ cutoffs, ∀ wit : (∀ u, SupportedWitness (χ u) U a ε (3*w/2+1/1000000000000) T allowance i),
      ∀ F : Finset Row, F ⊆ rows → ∀ (j : Label) (J K : Fin (dyadicLength U)),
      (∀ u ∈ F, (wit u).label = j ∧ (wit u).left = J ∧ (wit u).right = K) →
      AnchorFiberMoments F slots χ Q widths U a ε (3*w/2+1/1000000000000) a0 a1 w εm C height j J K) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) * U^((2*a-1)*P) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(1 + max 0 (detPrice a0 a1 k P (∑s∈slots,widths s) 1) + ε' +
        (154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s))) := by
  have hL : 0 ≤ ∑s∈slots,widths s := Finset.sum_nonneg (fun s hs => (hw s hs).le)
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hν0 : 0 ≤ 2*a-1 := by linarith
  -- cutoffs per bin
  let cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ := fun bin =>
    if h : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        ∈ classes k then
      Classical.choose (exists_cutoff_det (a0 := a0) (a1 := a1) hk0 h P (∑s∈slots,widths s) 1 hε')
    else cutLo
  have hcut : ∀ bin, cut bin ∈ cutoffs := by
    intro bin
    by_cases h : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        ∈ classes k
    · simp only [cut, dif_pos h]
      exact (Classical.choose_spec (exists_cutoff_det (a0 := a0) (a1 := a1) hk0 h P
        (∑s∈slots,widths s) 1 hε')).1
    · simp only [cut, dif_neg h]; exact cutLo_mem
  have hcutspec : ∀ bin, (2*a-1, 2*weightedMean slots widths
      (binValue slots ((2*a-1)/2) binWidth bin)) ∈ classes k →
      detEx a0 a1 (2*a-1) (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        (cut bin) P (∑s∈slots,widths s) 1 <
        max 0 (detPrice a0 a1 k P (∑s∈slots,widths s) 1) + ε' := by
    intro bin h
    simp only [cut, dif_pos h]
    exact (Classical.choose_spec (exists_cutoff_det (a0 := a0) (a1 := a1) hk0 h P
      (∑s∈slots,widths s) 1 hε')).2
  have ht : ∀ bin, 1 ≤ 3*cut bin/2+1/1000000000000 ∧ 3*cut bin/2+1/1000000000000 ≤ 3/2 := by
    intro bin
    obtain ⟨h1, h2⟩ := hcut bin
    unfold cutLo at h1; unfold cutHi at h2
    constructor <;> linarith
  let witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000000000) T allowance i :=
    fun bin => Classical.choice (hwit _ (ht bin).1 (ht bin).2)
  have hsum := anchor_weighted_row_sum rows slots χ Q widths U a ε T allowance mesh binWidth εm C
    height a0 a1 (1 - (2*a-1)*P + max 0 (detPrice a0 a1 k P (∑s∈slots,widths s) 1) + ε') i hU ha hν
    hε0 hε hmesh hbin hC hheight hfreq hw hwm hL ha1 ha1' cut hcut witness hQ
    (fun bin j J K => hmom (cut bin) (hcut bin) (witness bin) _ (Finset.filter_subset _ _) j J K
      (fun u hu => by
        obtain ⟨-, h1, h2, h3, -⟩ := anchorFiber_fields rows slots widths Q χ U a ε T allowance
          binWidth i hbin cut witness bin j J K u hu
        exact ⟨h1, h2, h3⟩))
    (by
      intro bin hex
      obtain ⟨u, -, hocc⟩ := hex
      obtain ⟨hm0, hm1⟩ := occupied_bin_mean slots widths hw U (2*a-1) binWidth hν0 bin
        (Q u) hocc
      have hcl : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
          ∈ classes k := ⟨hk, hν, by linarith, by linarith⟩
      have h1 := hcutspec bin hcl
      have h2 := fiberTarget_add_eq a0 a1 (2*a-1)
        (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)) (cut bin) P
        (∑s∈slots,widths s)
      linarith)
  have hP : 0 ≤ U^((2*a-1)*P) := Real.rpow_nonneg hU0.le _
  refine (mul_le_mul_of_nonneg_right hsum hP).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.rpow_add hU0]
  congr 2
  ring


theorem AnchorFiberMoments.congr_family {Row Label Slot : Type*} {rows : Finset Row}
    {slots : Finset Slot} {χ χ' : Row→Label→Character} {Q : Row→Slot→ℂ} {widths : Slot→ℝ}
    {U a ε tstar a0 a1 w εm C height : ℝ} {label : Label} {J K : Fin (dyadicLength U)}
    (h : ∀ u ∈ rows, χ' u = χ u)
    (hm : AnchorFiberMoments rows slots χ Q widths U a ε tstar a0 a1 w εm C height label J K) :
    AnchorFiberMoments rows slots χ' Q widths U a ε tstar a0 a1 w εm C height label J K := by
  refine ⟨hm.inverseUnmarked, ?_, ?_, ?_⟩
  · intro j k hjk σ hσ freq hfreq
    rw [Finset.sum_congr rfl (fun u hu => by rw [h u hu])]
    exact hm.plainUnmarked j k hjk σ hσ freq hfreq
  · intro h1 h2 sel hsel hz n hn σ hσ freq hfreq
    rw [Finset.sum_congr rfl (fun u hu => by rw [h u hu])]
    exact hm.inverseMarked h1 h2 sel hsel hz n hn σ hσ freq hfreq
  · intro h1 h2 sel hsel hz j k hjk σ hσ freq hfreq
    rw [Finset.sum_congr rfl (fun u hu => by rw [h u hu])]
    exact hm.plainMarked h1 h2 sel hsel hz j k hjk σ hσ freq hfreq

theorem norm_mul_scaled_le {Slot : Type*} (sel : Finset Slot) (c : Slot → ℝ)
    (hc0 : ∀ s, 0 ≤ c s) (hc1 : ∀ s, c s ≤ 1) (x : ℂ) (q : Slot → ℂ) :
    ‖x * ∏ s ∈ sel, ((c s : ℂ) * q s)‖^2 ≤ ‖x * ∏ s ∈ sel, q s‖^2 := by
  rw [Finset.prod_mul_distrib, ← mul_assoc, mul_comm x, mul_assoc, norm_mul]
  have h0 : ‖∏ s ∈ sel, (c s : ℂ)‖ ≤ 1 := by
    rw [norm_prod]
    calc ∏ s ∈ sel, ‖(c s : ℂ)‖ ≤ ∏ s ∈ sel, (1:ℝ) :=
          Finset.prod_le_prod₀ (fun s _ => norm_nonneg _) (fun s _ => by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 s)]
            exact hc1 s)
      _ = 1 := Finset.prod_const_one
  have h1 : 0 ≤ ‖x * ∏ s ∈ sel, q s‖ := norm_nonneg _
  have h2 : ‖∏ s ∈ sel, (c s : ℂ)‖ * ‖x * ∏ s ∈ sel, q s‖ ≤ ‖x * ∏ s ∈ sel, q s‖ := by
    nlinarith [norm_nonneg (∏ s ∈ sel, (c s : ℂ))]
  have h3 : 0 ≤ ‖∏ s ∈ sel, (c s : ℂ)‖ * ‖x * ∏ s ∈ sel, q s‖ := by positivity
  nlinarith

theorem AnchorFiberMoments.scale_slots {Row Label Slot : Type*} {rows : Finset Row}
    {slots : Finset Slot} {χ : Row→Label→Character} {Q : Row→Slot→ℂ} {widths : Slot→ℝ}
    {U a ε tstar a0 a1 w εm C height : ℝ} {label : Label} {J K : Fin (dyadicLength U)}
    (c : Slot → ℝ) (hc0 : ∀ s, 0 ≤ c s) (hc1 : ∀ s, c s ≤ 1)
    (hm : AnchorFiberMoments rows slots χ Q widths U a ε tstar a0 a1 w εm C height label J K) :
    AnchorFiberMoments rows slots χ (fun u s => (c s : ℂ) * Q u s) widths U a ε tstar a0 a1 w εm
      C height label J K := by
  refine ⟨hm.inverseUnmarked, hm.plainUnmarked, ?_, ?_⟩
  · intro h1 h2 sel hsel hz n hn σ hσ freq hfreq
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) (hm.inverseMarked h1 h2 sel hsel hz n hn σ hσ
      freq hfreq)
    exact norm_mul_scaled_le sel c hc0 hc1 _ (Q u)
  · intro h1 h2 sel hsel hz j k hjk σ hσ freq hfreq
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) (hm.plainMarked h1 h2 sel hsel hz j k hjk σ
      hσ freq hfreq)
    exact norm_mul_scaled_le sel c hc0 hc1 _ (Q u)

end
end Qrh.TwoSlot.AnchorZeroLoss.High
