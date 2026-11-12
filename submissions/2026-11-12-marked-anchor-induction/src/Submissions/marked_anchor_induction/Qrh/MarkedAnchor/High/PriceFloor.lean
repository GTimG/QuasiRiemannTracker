/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Gates

/-!
# High.PriceFloor

The HIGH price with a CUTOFF FLOOR `wlo`.

The short branch of the detector at cutoff `w` needs marked sources at every witness width
`r ≥ w`; at stage `n` they exist only for `r > R n` (earlier anchors). So the
price may only use cutoffs `w ≥ wlo := R n + 10^-6`. We implement this by evaluating the detector
excess at the floored cutoff `fl wlo w = max w (clampLo wlo)`, `clampLo wlo = min (max wlo cutLo) cutHi`:

* `detPriceW a0 a1 k wlo P s M = ⨆_{classes} ⨅_{w ∈ cutoffs} detEx … (fl wlo w) P s M`,
* `highPriceFW a0 a1 k wlo P s M = max 0 (max (tinyEx P s M) (detPriceW …))`,
* `highPriceW a0 a1 k wlo` : the `CubeFree.Price`.

Facts: all the price lemmas of `High.Price` (nonneg, mono, Lipschitz, `antitoneM`, ledger form
`highPriceFW_le_of` with `wlo ≤ w`, leaf form `exists_cutoffW` giving cutoffs `≥ wlo`),
`highPriceF_le_highPriceFW` (the floor only raises the price), `highPriceFW_eq` (no floor for
`wlo ≤ 2/3`), and the chain ledger `chain_highPriceW_le` at `wlo = R n + 10^-6` (chain cutoffs
`fw ≥ R n + 10^-6`, `Stg.R_le_w`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open Qrh.MarkedAnchor.Anchor ChainData ChainCheck

/-- The floor, clamped into the cutoff interval. -/
def clampLo (wlo : ℝ) : ℝ := min (max wlo cutLo) cutHi

/-- The floored cutoff. -/
def fl (wlo w : ℝ) : ℝ := max w (clampLo wlo)

theorem clampLo_mem (wlo : ℝ) : clampLo wlo ∈ cutoffs := by
  unfold clampLo
  refine ⟨le_min (le_max_right _ _) (by norm_num [cutLo, cutHi]), min_le_right _ _⟩

theorem fl_mem {wlo w : ℝ} (hw : w ∈ cutoffs) : fl wlo w ∈ cutoffs :=
  ⟨hw.1.trans (le_max_left _ _), max_le hw.2 (clampLo_mem wlo).2⟩

theorem fl_of_le {wlo w : ℝ} (hw : w ∈ cutoffs) (h : wlo ≤ w) : fl wlo w = w := by
  unfold fl clampLo
  exact max_eq_left ((min_le_left _ _).trans (max_le h hw.1))

theorem le_fl {wlo w : ℝ} (hlo : wlo ≤ cutHi) : wlo ≤ fl wlo w := by
  unfold fl clampLo
  refine le_trans ?_ (le_max_right _ _)
  exact le_min (le_max_left _ _) hlo

/-- The floored detector price. -/
def detPriceW (a0 a1 k wlo P s M : ℝ) : ℝ :=
  supC k (fun p => infW (fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P s M))

/-- The floored HIGH price. -/
def highPriceFW (a0 a1 k wlo P s M : ℝ) : ℝ :=
  max 0 (max (tinyEx P s M) (detPriceW a0 a1 k wlo P s M))

section
variable {a0 a1 k wlo : ℝ}

theorem infW_detExW_le (hk0 : 0 ≤ k) {p : ℝ × ℝ} (hp : p ∈ classes k) (P s M : ℝ) :
    infW (fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P s M) ≤ bnd a0 a1 P s M :=
  (infW_le (fun w hw => (detEx_bounds hk0 hp (fl_mem hw) P s M).1) cutLo_mem).trans
    (detEx_bounds hk0 hp (fl_mem cutLo_mem) P s M).2

theorem infW_le_detPriceW (hk0 : 0 ≤ k) {p : ℝ × ℝ} (hp : p ∈ classes k) (P s M : ℝ) :
    infW (fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P s M) ≤ detPriceW a0 a1 k wlo P s M :=
  le_supC (F := fun p => infW fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P s M)
    (fun q hq => infW_detExW_le hk0 hq P s M) hp

theorem detPriceW_le_add (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P s M P' s' M' c : ℝ}
    (h : ∀ p ∈ classes k, ∀ w ∈ cutoffs,
      detEx a0 a1 p.1 p.2 w P' s' M' ≤ detEx a0 a1 p.1 p.2 w P s M + c) :
    detPriceW a0 a1 k wlo P' s' M' ≤ detPriceW a0 a1 k wlo P s M + c := by
  refine supC_le hk1 fun p hp => ?_
  have h1 : infW (fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P' s' M') ≤
      infW (fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P s M) + c :=
    infW_le_add (fun w hw => (detEx_bounds hk0 hp (fl_mem hw) P' s' M').1)
      (fun w hw => h p hp _ (fl_mem hw))
  have h2 := infW_le_detPriceW (a0 := a0) (a1 := a1) (wlo := wlo) hk0 hp P s M
  linarith

theorem detPriceW_le_of (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P s M c : ℝ}
    (h : ∀ p ∈ classes k, ∃ w ∈ cutoffs, wlo ≤ w ∧ detEx a0 a1 p.1 p.2 w P s M ≤ c) :
    detPriceW a0 a1 k wlo P s M ≤ c := by
  refine supC_le hk1 fun p hp => ?_
  obtain ⟨w, hw, hlo, hle⟩ := h p hp
  refine (infW_le (fun w hw => (detEx_bounds hk0 hp (fl_mem hw) P s M).1) hw).trans ?_
  simp only [fl_of_le hw hlo]
  exact hle

theorem highPriceFW_nonneg (a0 a1 k wlo P s M : ℝ) : 0 ≤ highPriceFW a0 a1 k wlo P s M :=
  le_max_left _ _

theorem tinyEx_le_highPriceFW (a0 a1 k wlo P s M : ℝ) :
    tinyEx P s M ≤ highPriceFW a0 a1 k wlo P s M :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem detPriceW_le_highPriceFW (a0 a1 k wlo P s M : ℝ) :
    detPriceW a0 a1 k wlo P s M ≤ highPriceFW a0 a1 k wlo P s M :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem highPriceFW_le_add (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P s M P' s' M' c : ℝ} (hc : 0 ≤ c)
    (ht : tinyEx P' s' M' ≤ tinyEx P s M + c)
    (h : ∀ p ∈ classes k, ∀ w ∈ cutoffs,
      detEx a0 a1 p.1 p.2 w P' s' M' ≤ detEx a0 a1 p.1 p.2 w P s M + c) :
    highPriceFW a0 a1 k wlo P' s' M' ≤ highPriceFW a0 a1 k wlo P s M + c := by
  have hd := detPriceW_le_add (wlo := wlo) hk0 hk1 h
  unfold highPriceFW
  refine max_le (by linarith [le_max_left 0 (max (tinyEx P s M) (detPriceW a0 a1 k wlo P s M))])
    (max_le ?_ ?_)
  · linarith [le_max_left (tinyEx P s M) (detPriceW a0 a1 k wlo P s M),
      le_max_right 0 (max (tinyEx P s M) (detPriceW a0 a1 k wlo P s M))]
  · linarith [le_max_right (tinyEx P s M) (detPriceW a0 a1 k wlo P s M),
      le_max_right 0 (max (tinyEx P s M) (detPriceW a0 a1 k wlo P s M))]

/-- **Ledger form** (cutoffs at or above the floor). -/
theorem highPriceFW_le_of (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P s M c : ℝ}
    (ht : tinyEx P s M ≤ c)
    (h : ∀ p ∈ classes k, ∃ w ∈ cutoffs, wlo ≤ w ∧ detEx a0 a1 p.1 p.2 w P s M ≤ c) :
    highPriceFW a0 a1 k wlo P s M ≤ max 0 c :=
  max_le_max le_rfl (max_le ht (detPriceW_le_of hk0 hk1 h))

/-- **Leaf form**: every class has a cutoff `≥ wlo` (if `wlo ≤ 79/100`) within `ε'` of the price. -/
theorem exists_cutoffW (hk0 : 0 ≤ k) (hlo : wlo ≤ cutHi) {p : ℝ × ℝ} (hp : p ∈ classes k)
    (P s M : ℝ) {ε' : ℝ} (hε : 0 < ε') :
    ∃ w ∈ cutoffs, wlo ≤ w ∧ detEx a0 a1 p.1 p.2 w P s M < highPriceFW a0 a1 k wlo P s M + ε' := by
  have h1 := infW_le_detPriceW (a0 := a0) (a1 := a1) (wlo := wlo) hk0 hp P s M
  have h2 := detPriceW_le_highPriceFW a0 a1 k wlo P s M
  obtain ⟨w, hw, hlt⟩ := exists_lt_infW (f := fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P s M)
    (show _ < highPriceFW a0 a1 k wlo P s M + ε' by linarith)
  exact ⟨fl wlo w, fl_mem hw, le_fl hlo, hlt⟩

/-- The same against the detector part only (used for core scales `> 1`). -/
theorem exists_cutoffW_det (hk0 : 0 ≤ k) (hlo : wlo ≤ cutHi) {p : ℝ × ℝ} (hp : p ∈ classes k)
    (P s M : ℝ) {ε' : ℝ} (hε : 0 < ε') :
    ∃ w ∈ cutoffs, wlo ≤ w ∧
      detEx a0 a1 p.1 p.2 w P s M < max 0 (detPriceW a0 a1 k wlo P s M) + ε' := by
  have h1 := infW_le_detPriceW (a0 := a0) (a1 := a1) (wlo := wlo) hk0 hp P s M
  have h2 := le_max_right 0 (detPriceW a0 a1 k wlo P s M)
  obtain ⟨w, hw, hlt⟩ := exists_lt_infW (f := fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P s M)
    (show _ < max 0 (detPriceW a0 a1 k wlo P s M) + ε' by linarith)
  exact ⟨fl wlo w, fl_mem hw, le_fl hlo, hlt⟩

/-- The floor only raises the price. -/
theorem highPriceF_le_highPriceFW (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (P s M : ℝ) :
    highPriceF a0 a1 k P s M ≤ highPriceFW a0 a1 k wlo P s M := by
  have hd : detPrice a0 a1 k P s M ≤ detPriceW a0 a1 k wlo P s M := by
    refine supC_le hk1 fun p hp => ?_
    refine (le_infW fun w hw => ?_).trans (infW_le_detPriceW (wlo := wlo) hk0 hp P s M)
    exact (infW_le (fun w hw => (detEx_bounds hk0 hp hw P s M).1) (fl_mem hw))
  unfold highPriceF highPriceFW
  exact max_le_max le_rfl (max_le_max le_rfl hd)

/-- No floor below `2/3`. -/
theorem highPriceFW_eq (hlo : wlo ≤ cutLo) (P s M : ℝ) :
    highPriceFW a0 a1 k wlo P s M = highPriceF a0 a1 k P s M := by
  have hfl : ∀ w ∈ cutoffs, fl wlo w = w := fun w hw => fl_of_le hw (hlo.trans hw.1)
  have hd : detPriceW a0 a1 k wlo P s M = detPrice a0 a1 k P s M := by
    unfold detPriceW detPrice infW
    congr 1; funext p; congr 1; funext w
    show detEx a0 a1 p.1 p.2 (fl wlo w.1) P s M = detEx a0 a1 p.1 p.2 w.1 P s M
    rw [hfl w.1 w.2]
  unfold highPriceFW highPriceF
  rw [hd]

theorem highPriceFW_mono (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P P' s s' : ℝ} (M : ℝ) (hP : P' ≤ P)
    (hs : s' ≤ s) : highPriceFW a0 a1 k wlo P' s' M ≤ highPriceFW a0 a1 k wlo P s M := by
  have := highPriceFW_le_add (a0 := a0) (a1 := a1) (wlo := wlo) (P := P) (s := s) (M := M)
    (P' := P') (s' := s') (M' := M) hk0 hk1 le_rfl (by unfold tinyEx; linarith) (fun p hp w hw => by
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have eP := detEx_P a0 a1 p.1 p.2 w P' s' M (P - P')
      rw [show P' + (P - P') = P by ring] at eP
      have hνP : 0 ≤ p.1 * (P - P') := mul_nonneg (hk0.trans h1) (by linarith)
      obtain ⟨l, -⟩ := detEx_s (a0 := a0) (a1 := a1) (ν := p.1) (w := w) h3 P s' M (s - s')
        (by linarith)
      rw [show s' + (s - s') = s by ring] at l
      linarith)
  linarith

theorem highPriceFW_lipP (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    highPriceFW a0 a1 k wlo (P + δ) s M ≤ highPriceFW a0 a1 k wlo P s M + lipH a0 a1 * δ := by
  have hL := lipH_ge_one a0 a1
  refine highPriceFW_le_add hk0 hk1 (by positivity) (by rw [tinyEx_P]; nlinarith)
    fun p hp w _ => ?_
  obtain ⟨h1, h2, -, -⟩ := hp
  rw [detEx_P]
  nlinarith

theorem highPriceFW_lipS (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    highPriceFW a0 a1 k wlo P (s + δ) M ≤ highPriceFW a0 a1 k wlo P s M + lipH a0 a1 * δ := by
  have hL := lipH_ge_one a0 a1
  refine highPriceFW_le_add hk0 hk1 (by positivity) (by rw [tinyEx_s]; nlinarith)
    fun p hp w _ => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨-, u⟩ := detEx_s (a0 := a0) (a1 := a1) (ν := p.1) (w := w) h3 P s M δ hδ
  have : p.2 * δ ≤ lipH a0 a1 * δ := by nlinarith
  linarith

theorem highPriceFW_lipM (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (P s M δ : ℝ) :
    highPriceFW a0 a1 k wlo P s (M + δ) ≤ highPriceFW a0 a1 k wlo P s M + lipH a0 a1 * |δ| := by
  have hL := lipH_ge_one a0 a1
  refine highPriceFW_le_add hk0 hk1 (by positivity) ?_ fun p hp w hw => ?_
  · rw [tinyEx_M]
    have := neg_abs_le δ
    nlinarith [abs_nonneg δ]
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    have := detEx_M (a0 := a0) (a1 := a1) (hk0.trans h1) h2 h3 (h4.trans h2) hw P s M δ
    linarith [le_abs_self (detEx a0 a1 p.1 p.2 w P s (M + δ) - detEx a0 a1 p.1 p.2 w P s M)]

/-- Larger radius (`k ≥ 1/6`), as `highPriceF_antitoneM`. -/
theorem highPriceFW_antitoneM (hk0 : 1 / 6 ≤ k) (hk1 : k ≤ 3 / 4) (P s : ℝ) {M M' : ℝ}
    (hM : M ≤ M') : highPriceFW a0 a1 k wlo P s M' ≤ highPriceFW a0 a1 k wlo P s M := by
  have key : ∀ p ∈ classes k, ∀ w ∈ cutoffs,
      detEx a0 a1 p.1 p.2 w P s M' ≤ detEx a0 a1 p.1 p.2 w P s M + 0 := by
    intro p hp w hw
    obtain ⟨h1, h2, h3, h4⟩ := hp
    obtain ⟨hw1, hw2⟩ := hw
    unfold cutLo at hw1; unfold cutHi at hw2
    have hσ := sig_nonneg a0 a1 w
    rw [detEx_eq, detEx_eq]
    generalize sig a0 a1 w = σ at hσ ⊢
    have hmin : min s (M * σ) ≤ min s (M' * σ) :=
      min_le_min le_rfl (mul_le_mul_of_nonneg_right hM hσ)
    have hs : -(p.1 * M' * w) - p.2 * min s (M' * σ) ≤ -(p.1 * M * w) - p.2 * min s (M * σ) := by
      have : p.1 * M * w ≤ p.1 * M' * w := by
        have : 0 ≤ p.1 * w := mul_nonneg (by linarith) (by linarith)
        nlinarith
      nlinarith
    have hl : M' * (1 / 6 + (5 / 6 - p.1) * (3 * w / 2 + 1 / 1000000) - 1) ≤
        M * (1 / 6 + (5 / 6 - p.1) * (3 * w / 2 + 1 / 1000000) - 1) := by
      have hc : 1 / 6 + (5 / 6 - p.1) * (3 * w / 2 + 1 / 1000000) - 1 ≤ 0 := by nlinarith
      nlinarith
    have := max_le_max hs hl
    linarith
  have := highPriceFW_le_add (a0 := a0) (a1 := a1) (wlo := wlo) (P := P) (s := s) (M := M)
    (P' := P) (s' := s) (M' := M') (by linarith) hk1 le_rfl (by unfold tinyEx; linarith) key
  linarith

end

/-- **The floored HIGH price** as an exponential leaf price. -/
def highPriceW (a0 a1 k wlo : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) :
    QRH.SilDensitySplit.CubeFree.Price where
  f _ P s M := highPriceFW a0 a1 k wlo P s M
  nonneg _ P s M := highPriceFW_nonneg a0 a1 k wlo P s M
  mono _ P P' s s' M hP hs := highPriceFW_mono hk0 hk1 M hP hs
  lip := lipH a0 a1
  lip_nonneg := zero_le_one.trans (lipH_ge_one a0 a1)
  lipP _ P s M δ hδ := highPriceFW_lipP hk0 hk1 P s M δ hδ
  lipS _ P s M δ hδ := highPriceFW_lipS hk0 hk1 P s M δ hδ
  lipM _ P s M δ := highPriceFW_lipM hk0 hk1 P s M δ

theorem highPriceW_f (a0 a1 k wlo : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (w P s M : ℝ) :
    (highPriceW a0 a1 k wlo hk0 hk1).f w P s M = highPriceFW a0 a1 k wlo P s M := rfl

/-- The stage ledger with the floor `R + 10^-6` (the chain cutoffs lie above it, `R_le_w`). -/
theorem Stg.highPriceFW_le {d : Stg} (h : d.Hyp) :
    highPriceFW d.a0 d.a1 d.k (d.R + 1/1000000) d.r d.s d.H ≤ d.u := by
  have hk0 : 0 ≤ d.k := h.k_pos.le
  have := highPriceFW_le_of (a0 := d.a0) (a1 := d.a1) (wlo := d.R + 1/1000000) hk0 h.k_hi
    ((Stg.tiny_le h).trans (by linarith)) (fun p hp => ⟨d.w p.1, Stg.w_mem h hp.1 hp.2.1,
      Stg.R_le_w h hp.1, Stg.detEx_le h hp.1 hp.2.1 hp.2.2.1 hp.2.2.2⟩)
  exact this.trans (max_le h.u_nonneg le_rfl)

/-- **The floored HIGH price of chain stage `n` is at most `u` on the whole stage**
(`ChainHighLedger` for `highPriceW … (R n + 10^-6)`). -/
theorem chain_highPriceW_le (n : ℕ) (hn : n < 176) (r : ℝ) (h1 : (left n : ℝ) ≤ r)
    (h2 : r ≤ R n) :
    highPriceFW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) r (fs (R n : ℝ) (gain n) (cut n) r)
      (fH (R n : ℝ) r) ≤ fu (R n : ℝ) r := by
  have h := Stg.highPriceFW_le (chain_hyp n hn r h1 h2)
  rw [chainStg_r n hn, chainStg_s n hn, chainStg_H n hn, chainStg_u n hn] at h
  exact h

/-- The floor `R n + 10^-6` lies below `79/100`. -/
theorem chain_floor_le (n : ℕ) (hn : n < 176) : (R n : ℝ) + 1/1000000 ≤ cutHi := by
  have hlr : left n ≤ R n := by
    rw [R_eq, left_eq]
    have : (n : ℚ) / 4000 ≤ ((n : ℚ) + 1) / 4000 := by
      apply div_le_div_of_nonneg_right <;> linarith
    linarith
  have h := chain_hyp n hn (R n) (by exact_mod_cast hlr) le_rfl
  have hk := (chain_cut_mem n hn)
  have h1 := Stg.R_le_w h (le_refl (cut n : ℝ))
  have h2 := (Stg.w_mem h (le_refl (cut n : ℝ)) hk.2).2
  exact h1.trans h2

end
end Qrh.MarkedAnchor.High
