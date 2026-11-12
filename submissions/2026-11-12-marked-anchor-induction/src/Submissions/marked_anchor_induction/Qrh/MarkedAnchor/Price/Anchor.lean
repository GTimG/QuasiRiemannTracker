/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.sil_density_split_20261026.CubeFree.Price
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Price
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.PriceFloor
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Anchor.ChainData

/-!
# Price.Anchor

The leaf price of one ordinary anchor step, as an exponential leaf
price in the sense of sil-density-split `CubeFree.Price` (nonnegative, monotone in `P, s`,
globally Lipschitz in `P, s, M`).

* `maxPrice p q` — the pointwise maximum of two prices (LOW rows and HIGH rows are bounded
  separately and the leaf energy is their sum).
* LOW part: `k · deletionNeed B₁ ℓ c₁ P s M`, i.e. sil-density-split's
  `parentPrice k B₁ ℓ c₁` at the cut `k`, for the face `G(B₁, ℓ, c₁)` with
  `B₁ = R - δ₁`, `c₁ = S_R - δ₁`, `ℓ > 0` small. This face is a restriction of the previous
  anchor `GlobalSource (R-δ₁) 0 (S_R-δ₁)` (raising the marked budget `0 → ℓ` shrinks the face), so
  the hard wall `P ≤ R M` of the rectangle is replaced by the Lipschitz wall
  `P + ℓ s ≤ (R-δ₁) M`; the need is Lipschitz with constant `needLip ≈ 1/ℓ`. The "delete
  everything" fallback (zero-slot native bound) is built into `deletionNeed`.
* HIGH part: an abstract `Price` (in the chain: the floored `High.highPriceW a0 a1 k (R+10^-6)`).
* `HighAt high R z k r` — the three properties of the HIGH price that the stage ledger uses
  (antitone in the radius, the stage ledger at `(r, s, H)`, and vanishing on empty slot width);
  `highAt_highPriceW` (floored price, ledger `High.chain_highPriceW_le`) and `highAt_highPrice`
  (unfloored price, ledger `High.Gates.chain_highPrice_le`) verify them given the stage ledger.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Price
noncomputable section
open QRH.SilDensitySplit.CubeFree
open Qrh.MarkedAnchor.Anchor.ChainData

/-! ### The maximum of two prices -/

theorem max_le_max_add' {a b a' b' e : ℝ} (ha : a' ≤ a + e) (hb : b' ≤ b + e) :
    max a' b' ≤ max a b + e :=
  max_le (by linarith [le_max_left a b]) (by linarith [le_max_right a b])

/-- The pointwise maximum of two leaf prices. -/
def maxPrice (p q : QRH.SilDensitySplit.CubeFree.Price) : QRH.SilDensitySplit.CubeFree.Price where
  f w P s M := max (p.f w P s M) (q.f w P s M)
  nonneg w P s M := le_max_of_le_left (p.nonneg w P s M)
  mono w P P' s s' M hP hs := max_le_max (p.mono w P P' s s' M hP hs) (q.mono w P P' s s' M hP hs)
  lip := max p.lip q.lip
  lip_nonneg := le_max_of_le_left p.lip_nonneg
  lipP w P s M δ hδ := by
    have h1 := p.lipP w P s M δ hδ
    have h2 := q.lipP w P s M δ hδ
    have e1 : p.lip*δ ≤ max p.lip q.lip*δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    have e2 : q.lip*δ ≤ max p.lip q.lip*δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
    exact max_le_max_add' (by linarith) (by linarith)
  lipS w P s M δ hδ := by
    have h1 := p.lipS w P s M δ hδ
    have h2 := q.lipS w P s M δ hδ
    have e1 : p.lip*δ ≤ max p.lip q.lip*δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    have e2 : q.lip*δ ≤ max p.lip q.lip*δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
    exact max_le_max_add' (by linarith) (by linarith)
  lipM w P s M δ := by
    have h1 := p.lipM w P s M δ
    have h2 := q.lipM w P s M δ
    have hδ := abs_nonneg δ
    have e1 : p.lip*|δ| ≤ max p.lip q.lip*|δ| := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    have e2 : q.lip*|δ| ≤ max p.lip q.lip*|δ| := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
    exact max_le_max_add' (by linarith) (by linarith)

theorem maxPrice_f (p q : QRH.SilDensitySplit.CubeFree.Price) (w P s M : ℝ) :
    (maxPrice p q).f w P s M = max (p.f w P s M) (q.f w P s M) := rfl

/-! ### The anchor price -/

/-- **The anchor price**: `max (k · deletionNeed B₁ ℓ c₁) high`. -/
def anchorPrice (k B₁ ℓ c₁ : ℝ) (hk : 0 ≤ k) (hℓ : 0 < ℓ)
    (high : QRH.SilDensitySplit.CubeFree.Price) : QRH.SilDensitySplit.CubeFree.Price :=
  maxPrice (parentPrice k B₁ ℓ c₁ hk hℓ) high

theorem anchorPrice_f (k B₁ ℓ c₁ : ℝ) (hk : 0 ≤ k) (hℓ : 0 < ℓ)
    (high : QRH.SilDensitySplit.CubeFree.Price) (w P s M : ℝ) :
    (anchorPrice k B₁ ℓ c₁ hk hℓ high).f w P s M =
      max (k * deletionNeed B₁ ℓ c₁ P s M) (high.f w P s M) := rfl

/-- The deletion need decreases when the radius grows (nonnegative face parameters). -/
theorem deletionNeed_antiM {B₀ L₀ c₀ P s M M' : ℝ} (hL : 0 < L₀) (hB : 0 ≤ B₀) (hc : 0 ≤ c₀)
    (hM : M ≤ M') : deletionNeed B₀ L₀ c₀ P s M' ≤ deletionNeed B₀ L₀ c₀ P s M := by
  rw [deletionNeed_eq, deletionNeed_eq]
  apply clip_mono le_rfl (by nlinarith)
  exact div_le_div_of_nonneg_right (by nlinarith) hL.le

/-- The clipped need is at most the positive part of the larger defect. -/
theorem deletionNeed_le_max (B₀ L₀ c₀ P s M : ℝ) :
    deletionNeed B₀ L₀ c₀ P s M ≤ max 0 (max (s - c₀*M) ((P + L₀*s - B₀*M)/L₀)) :=
  max_le_max le_rfl (min_le_right _ _)

/-! ### What the stage ledger needs from the HIGH price -/

/-- The properties of the HIGH price used by the ledger of the stage step at the point `r`
(stage data `R`, entry gain `z`, cut `k`): it does not increase with the radius, it is paid by
`u = fu R r` at the stage point `(r, s, H) = (r, fs R z k r, fH R r)` (the HIGH child), and it
vanishes when no slot width is retained. -/
structure HighAt (high : QRH.SilDensitySplit.CubeFree.Price) (R z k r : ℝ) : Prop where
  antiM : ∀ w P s M M', M ≤ M' → high.f w P s M' ≤ high.f w P s M
  ledger : ∀ w, high.f w r (fs R z k r) (fH R r) ≤ fu R r
  empty : ∀ w, high.f w r 0 (fH R r) ≤ 0

/-- The HIGH price `High.highPriceF` vanishes on rows without retained slot width: cutoff
`w = R + 10^-4` (short branch `ν(r - H w) ≤ 0`; long branch negative since `k ≥ .363656`,
`R ≤ .7775`), tiny cores negative for `H ≥ 1/2`. -/
theorem highPriceF_empty {a0 a1 k R r : ℝ} (hk : 45457/125000 ≤ k) (hk1 : k ≤ 3/4)
    (hR0 : 7/10 ≤ R) (hR1 : R ≤ 311/400) (hH : 1/2 ≤ r/R) :
    High.highPriceF a0 a1 k r 0 (r/R) ≤ 0 := by
  have hRpos : 0 < R := by linarith
  set H := r/R with hHdef
  have hr' : r = H*R := by rw [hHdef, div_mul_cancel₀ r hRpos.ne']
  have h := High.highPriceF_le_of (a0 := a0) (a1 := a1) (k := k) (P := r) (s := 0) (M := H)
    (c := 0) (by linarith) hk1 ?tiny ?det
  · simpa using h
  case tiny =>
    unfold High.tinyEx
    rw [hr']
    nlinarith
  case det =>
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨R + 1/10000, ⟨by unfold High.cutLo; linarith, by unfold High.cutHi; linarith⟩, ?_⟩
    have hσ : 0 ≤ H * High.sig a0 a1 (R + 1/10000) :=
      mul_nonneg (by linarith) (High.sig_nonneg _ _ _)
    unfold High.detEx High.shortCnt High.longCnt
    rw [min_eq_left hσ]
    have hRA : R - (3*(R + 1/10000)/2 + 1/1000000) < 0 := by linarith
    have hν : p.1*(R - (3*(R + 1/10000)/2 + 1/1000000)) ≤
        (45457/125000)*(R - (3*(R + 1/10000)/2 + 1/1000000)) :=
      mul_le_mul_of_nonpos_right (by linarith) hRA.le
    have hbr : p.1*(R - (3*(R + 1/10000)/2 + 1/1000000)) + 1/6 +
        5*(3*(R + 1/10000)/2 + 1/1000000)/6 - 1 ≤ 0 := by linarith
    have hshort : H - p.1*H*(R + 1/10000) - p.2*0 ≤ H - p.1*r := by
      rw [hr']
      have : 0 ≤ p.1*H := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hlong : H/6 + (5/6 - p.1)*H*(3*(R + 1/10000)/2 + 1/1000000) ≤ H - p.1*r := by
      have key : H/6 + (5/6 - p.1)*H*(3*(R + 1/10000)/2 + 1/1000000) - (H - p.1*r) =
          H*(p.1*(R - (3*(R + 1/10000)/2 + 1/1000000)) + 1/6 +
            5*(3*(R + 1/10000)/2 + 1/1000000)/6 - 1) := by
        rw [hr']; ring
      have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ H by linarith) hbr
      linarith
    have := max_le hshort hlong
    linarith

/-- The floored HIGH price (`High.highPriceW`) vanishes on rows without retained slot width: cutoff
`w = R + 10^-4` (short branch `ν(r - H w) ≤ 0`; long branch negative since `k ≥ .363656`,
`R ≤ .7775`), tiny cores negative for `H ≥ 1/2`. -/
theorem highPriceFW_empty {a0 a1 k wlo R r : ℝ} (hk : 45457/125000 ≤ k) (hk1 : k ≤ 3/4)
    (hR0 : 7/10 ≤ R) (hR1 : R ≤ 311/400) (hH : 1/2 ≤ r/R) (hwlo : wlo ≤ R + 1/10000) :
    High.highPriceFW a0 a1 k wlo r 0 (r/R) ≤ 0 := by
  have hRpos : 0 < R := by linarith
  set H := r/R with hHdef
  have hr' : r = H*R := by rw [hHdef, div_mul_cancel₀ r hRpos.ne']
  have h := High.highPriceFW_le_of (a0 := a0) (a1 := a1) (k := k) (wlo := wlo) (P := r) (s := 0) (M := H)
    (c := 0) (by linarith) hk1 ?tiny ?det
  · simpa using h
  case tiny =>
    unfold High.tinyEx
    rw [hr']
    nlinarith
  case det =>
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨R + 1/10000, ⟨by unfold High.cutLo; linarith, by unfold High.cutHi; linarith⟩, hwlo, ?_⟩
    have hσ : 0 ≤ H * High.sig a0 a1 (R + 1/10000) :=
      mul_nonneg (by linarith) (High.sig_nonneg _ _ _)
    unfold High.detEx High.shortCnt High.longCnt
    rw [min_eq_left hσ]
    have hRA : R - (3*(R + 1/10000)/2 + 1/1000000) < 0 := by linarith
    have hν : p.1*(R - (3*(R + 1/10000)/2 + 1/1000000)) ≤
        (45457/125000)*(R - (3*(R + 1/10000)/2 + 1/1000000)) :=
      mul_le_mul_of_nonpos_right (by linarith) hRA.le
    have hbr : p.1*(R - (3*(R + 1/10000)/2 + 1/1000000)) + 1/6 +
        5*(3*(R + 1/10000)/2 + 1/1000000)/6 - 1 ≤ 0 := by linarith
    have hshort : H - p.1*H*(R + 1/10000) - p.2*0 ≤ H - p.1*r := by
      rw [hr']
      have : 0 ≤ p.1*H := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hlong : H/6 + (5/6 - p.1)*H*(3*(R + 1/10000)/2 + 1/1000000) ≤ H - p.1*r := by
      have key : H/6 + (5/6 - p.1)*H*(3*(R + 1/10000)/2 + 1/1000000) - (H - p.1*r) =
          H*(p.1*(R - (3*(R + 1/10000)/2 + 1/1000000)) + 1/6 +
            5*(3*(R + 1/10000)/2 + 1/1000000)/6 - 1) := by
        rw [hr']; ring
      have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ H by linarith) hbr
      linarith
    have := max_le hshort hlong
    linarith

/-- The HIGH price `High.highPrice` satisfies `HighAt` at a stage point, given its stage ledger. -/
theorem highAt_highPrice {a0 a1 R z k r : ℝ} (hk0 : 0 ≤ k) (hk : 45457/125000 ≤ k)
    (hk1 : k ≤ 3/4) (hR0 : 7/10 ≤ R) (hR1 : R ≤ 311/400) (hH : 1/2 ≤ r/R)
    (hled : High.highPriceF a0 a1 k r (fs R z k r) (fH R r) ≤ fu R r) :
    HighAt (High.highPrice a0 a1 k hk0 hk1) R z k r where
  antiM w P s M M' hM := High.highPriceF_antitoneM (by linarith) hk1 P s hM
  ledger w := hled
  empty w := highPriceF_empty hk hk1 hR0 hR1 hH

/-- The floored HIGH price `High.highPriceW` satisfies `HighAt` at a stage point, given its stage ledger
(`High.chain_highPriceW_le`), for a floor `wlo ≤ R + 10^-4`. -/
theorem highAt_highPriceW {a0 a1 R z k r wlo : ℝ} (hk0 : 0 ≤ k) (hk : 45457/125000 ≤ k)
    (hk1 : k ≤ 3/4) (hR0 : 7/10 ≤ R) (hR1 : R ≤ 311/400) (hH : 1/2 ≤ r/R)
    (hwlo : wlo ≤ R + 1/10000)
    (hled : High.highPriceFW a0 a1 k wlo r (fs R z k r) (fH R r) ≤ fu R r) :
    HighAt (High.highPriceW a0 a1 k wlo hk0 hk1) R z k r where
  antiM w P s M M' hM := High.highPriceFW_antitoneM (by linarith) hk1 P s hM
  ledger w := hled
  empty w := highPriceFW_empty hk hk1 hR0 hR1 hH hwlo

end
end Qrh.MarkedAnchor.Price
