/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Price.Anchor
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.StepData
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.ChainCheck
import Mathlib.Tactic.LinearCombination

/-!
# Price.Gates

Per-stage step data and step gates of the ordinary anchor step, for the forked cube-free step of
`Ordinary.StepData`.

Stage point: established anchor `(R, z)` (`R = R n`, `z = gain n`), cut `k = cut n`, a point
`r ∈ [left n, R n]`, and an anchor decrement `β ∈ (0, 1/1000]`. With `u* = fu R r`,
`S_R = (1-R)/2 + z` and `δ = 4·10^-8`:
* `B = r - β`, `L = 0`, `c = (1-r)/2 + (Y(r) - δ) - β` — exactly `anchorRect r (Y(r) - δ) β` of
  `Interface.Contract` (so `GlobalSource B L c` is `OrdinaryRectSource (anchorRect r (Y-δ) β)`);
* parent `G(B₀,L₀,c₀)`: a `ParentFace` (in the chain the PR103-type face `pr103Face`),
  `s₀ = (B₀-B)/L₀`;
* `κ = 3/4`, `Hmin = 1/2`, `Hmax = 3`, `sel ε w = min u* w`, `lref = 7/50`, `alpha = 3/5`,
  `Pref = 2/3`;
* price `anchorPrice k (R-δ₁) (β/4) (S_R-δ₁) high` with `δ₁ = min δ β / 4`.

The decrement `β` is forced: at the worst side `P/H = r/(r/R) = R` exactly, which the previous
anchor (only known with decrements) does not cover; with `B = r - β` the worst side has
`P/H ≤ R - β R/r + o(1)`.

`stageGates`: `StepGates` from the scalar stage facts `StageHyp` (gates 2, 4, 6 of
`ChainCheck`, `u* ≤ 10^-4`, `S_R ≤ .137`, `k ≥ .363656`, `z ≥ 0`) and the HIGH facts `HighAt`.
`stageHyp_chain`: `StageHyp` at every stage `n < 256` and every real `r ∈ [left n, R n]`
(endpoint gates of `ChainCheck`, interpolated). The LOW ledger has the strict reserve
`k(δ + β - H δ₁ - c₁(tl+6 mesh)) > 0` (`k·need - u* = -k·δ` up to `β`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Price
noncomputable section
open QRH.SilDensitySplit.CubeFree
open Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.TwoSlot.AnchorExtension.ChainCheck

/-! ### Parent face -/

/-- The parent face `G(B₀,L₀,c₀)` of the step (inheritance below the crossing). -/
structure ParentFace where
  B₀ : ℝ
  L₀ : ℝ
  c₀ : ℝ
  hB : 7/9 < B₀ ∧ B₀ < 1
  hL : 0 < L₀
  hc : 0 < c₀ ∧ c₀ < 1/6
  /-- the crossing `s₀ = (B₀ - r + β)/L₀` stays below the cap for `r ≥ 1467/2000`, `β ≤ 1/1000` -/
  hcross : B₀ - 1467/2000 + 1/1000 ≤ c₀*L₀

/-- The fixed PR103-type parent face: `B = 1-10^-12`, `L = 2+10^-11`, `c = .15`. -/
def pr103Face : ParentFace where
  B₀ := 1 - 1/10^12
  L₀ := 2 + 1/10^11
  c₀ := 3/20
  hB := by norm_num
  hL := by norm_num
  hc := by norm_num
  hcross := by norm_num

/-! ### Scalar stage facts -/

/-- The stage decrement `δ = 4·10^-8`. -/
def stageDelta : ℝ := 1/25000000

/-- The decrement of the previous anchor used by the LOW leaf. -/
def del1 (β : ℝ) : ℝ := min stageDelta β / 4

theorem del1_pos {β : ℝ} (hβ : 0 < β) : 0 < del1 β :=
  div_pos (lt_min (by norm_num [stageDelta]) hβ) (by norm_num)

theorem del1_le_delta (β : ℝ) : del1 β ≤ stageDelta/4 :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem del1_le_beta (β : ℝ) : del1 β ≤ β/4 :=
  div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

/-- The scalar facts of a stage point used by the gates (all from `ChainCheck`). -/
structure StageHyp (R z k r : ℝ) : Prop where
  hR : 7/10 ≤ R ∧ R ≤ 7/9
  hr : 1467/2000 ≤ r ∧ r ≤ R
  hk : 45457/125000 ≤ k ∧ k < 1/2
  hz : 0 ≤ z
  hSR : (1-R)/2 + z ≤ 137/1000
  hu : fu R r ≤ 1/10000
  g2 : 0 < 137/1000 - fS R z k r
  g4 : 0 < 9/10 - r - fS R z k r - 4*fu R r
  g6 : 0 < 5/6 + 21/250 - r - fS R z k r - 3*fu R r - 1/100

namespace StageHyp
variable {R z k r : ℝ} (h : StageHyp R z k r)
include h

theorem R_pos : 0 < R := by linarith [h.hR.1]

theorem k_pos : 0 < k := by linarith [h.hk.1]

theorem u_nonneg : 0 ≤ fu R r := by
  have hR := h.R_pos
  unfold fu
  have : r/R ≤ 1 := (div_le_one hR).mpr h.hr.2
  linarith

theorem H_eq : fH R r = 1 - 6*fu R r := by unfold fH fu; ring

theorem H_le_one : fH R r ≤ 1 := by rw [h.H_eq]; linarith [h.u_nonneg]

theorem H_ge : 1 - 6/10000 ≤ fH R r := by rw [h.H_eq]; linarith [h.hu]

theorem RH : R * fH R r = r := by
  have hR : R ≠ 0 := h.R_pos.ne'
  unfold fH; field_simp

theorem Y_nonneg : 0 ≤ fY R z k r := by
  unfold fY
  have hR := h.R_pos
  have hk := h.k_pos
  have h1 : 0 ≤ r/R*z := mul_nonneg (div_nonneg (by linarith [h.hr.1]) hR.le) h.hz
  have h2 : 2 < 1/k := by rw [lt_one_div (by norm_num) hk]; linarith [h.hk.2]
  have h3 : 0 ≤ (1/k - 2)*fu R r := mul_nonneg (by linarith) h.u_nonneg
  linarith

theorem S_lower : (1-r)/2 ≤ fS R z k r := by unfold fS; linarith [h.Y_nonneg]

/-- `s = H S_R + u/k`. -/
theorem s_identity : fs R z k r = fH R r * ((1-R)/2 + z) + fu R r / k := by
  have hR := h.R_pos.ne'
  have hk := h.k_pos.ne'
  unfold fs fS fY fH fu
  field_simp
  ring

end StageHyp

/-! ### Step data -/

/-- **Per-stage step data** of the ordinary anchor step at `r` with decrement `β`. -/
def stageData (F : ParentFace) (R z k r β : ℝ) (high : QRH.SilDensitySplit.CubeFree.Price)
    (hk : 0 ≤ k) (hβ : 0 < β) : Ordinary.StepData where
  B₀ := F.B₀
  L₀ := F.L₀
  c₀ := F.c₀
  B := r - β
  L := 0
  c := (1-r)/2 + (fY R z k r - stageDelta) - β
  κ := 3/4
  s₀ := (F.B₀ - (r - β))/F.L₀
  Hmin := 1/2
  Hmax := 3
  sel := fun _ w => min (fu R r) w
  price := anchorPrice k (R - del1 β) (β/4) ((1-R)/2 + z - del1 β) hk (div_pos hβ (by norm_num))
    high
  lref := 7/50
  alpha := 3/5
  Pref := 2/3

section Gates
variable (F : ParentFace) {R z k r : ℝ} (hS : StageHyp R z k r)
  (high : QRH.SilDensitySplit.CubeFree.Price) (hH : HighAt high R z k r) (hk0 : 0 ≤ k)
  {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000)

/-- The target width `c` in terms of `fS`. -/
theorem stage_c_eq : (stageData F R z k r β high hk0 hβ0).c = fS R z k r - stageDelta - β := by
  show (1-r)/2 + (fY R z k r - stageDelta) - β = fS R z k r - stageDelta - β
  unfold fS; ring

include hS hβ0 hβ1 in
/-- The reference gates of the fork with reserve `ρ = 1/100` (gates 2, 4, 6). -/
theorem stage_reference : Ordinary.ReferenceAt (stageData F R z k r β high hk0 hβ0) (1/100) := by
  have hc := stage_c_eq F high hk0 (r := r) (z := z) (R := R) hβ0
  have hd : (0:ℝ) < stageDelta := by norm_num [stageDelta]
  have hu0 := hS.u_nonneg
  have g2 := hS.g2
  have g4 := hS.g4
  have g6 := hS.g6
  have hu := hS.hu
  refine ⟨by norm_num, show (0:ℝ) < 7/50 by norm_num, show 2*(7/50:ℝ) < 2/3 by norm_num,
    show (0:ℝ) < 3/5 by norm_num, show (3/5:ℝ) < 2/3 by norm_num, ?_, ?_, ?_⟩
  · show (1:ℝ)/100 ≤ 1 - (r - β); linarith [hS.hr.2, hS.hR.2]
  · show (1:ℝ)/100 ≤ 1 - (r - β) - (1 - 0)*(stageData F R z k r β high hk0 hβ0).c
    rw [hc]; linarith
  · intro ε _ S hs0 hSc
    rw [hc] at hSc
    have hsel : min (fu R r) S ≤ fu R r := min_le_left _ _
    refine ⟨?_, ?_, ?_⟩
    · show (1:ℝ)/100 ≤ 5/6 + 3/5*(7/50) - (r - β) - (1 - 0)*S - 3*min (fu R r) S
      linarith
    · show (1:ℝ)/100 ≤ 5/6 - 2/3 - S - 3*min (fu R r) S
      linarith
    · show (1:ℝ)/100 ≤ (1 - (r - β)) + (0 - 1)*S - 4*min (fu R r) S
      linarith

include hS hH hβ0 hβ1 in
/-- **The ledger** `price ≤ u + ε/16` at every side above the floor `ε/12`, with mesh and
frequency tolerance `≤ min (β/64) (ε/(256(lip+1)))`. -/
theorem stage_ledger (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ × ℝ × ℝ, Ordinary.LedgerAt (stageData F R z k r β high hk0 hβ0) ε p.1 p.2.1 p.2.2 := by
  have hlip := high.lip_nonneg
  set m : ℝ := min (β/64) (ε/(256*(high.lip+1))) with hmdef
  have hm0 : 0 < m := lt_min (div_pos hβ0 (by norm_num)) (div_pos hε (by linarith))
  have hmβ : m ≤ β/64 := min_le_left _ _
  have hmε : high.lip*m ≤ ε/256 := by
    have h1 : m ≤ ε/(256*(high.lip+1)) := min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith
  refine ⟨(ε/12, m, m), show (0:ℝ) < ε/12 from div_pos hε (by norm_num), ?_, hm0, hm0, ?_⟩
  · show ε/12 ≤ ε/(16*(3/4:ℝ)); norm_num
  intro mesh hmesh0 hmeshL tl htl0 htlL g hfloor
  change mesh ≤ m at hmeshL
  change tl ≤ m at htlL
  -- the side data, unfolded
  obtain ⟨_, hSc⟩ := g.hS
  obtain ⟨hf0, hfcg⟩ := g.hf
  have hroot := g.hroot
  obtain ⟨hsel1, hsel2⟩ := g.hsel
  obtain ⟨hs0, hs1⟩ := g.hs
  obtain ⟨ht1, ht2⟩ := g.ht
  have hc := stage_c_eq F high hk0 (r := r) (z := z) (R := R) hβ0
  rw [hc] at hSc
  change g.PC + (g.cg - g.f) + 0*g.S ≤ r - β + tl at hroot
  change min (fu R r) (g.S - g.f) ≤ g.u at hsel1
  change g.u ≤ min (fu R r) (g.S - g.f) + mesh at hsel2
  change ε/12 ≤ g.S - g.f at hfloor
  change (1/2:ℝ) ≤ 1 + g.t - 6*g.u ∧ 1 + g.t - 6*g.u ≤ 3 ∧
    (anchorPrice k (R - del1 β) (β/4) ((1-R)/2 + z - del1 β) hk0 (div_pos hβ0 (by norm_num))
      high).f (g.S - g.f) g.PC g.s (1 + g.t - 6*g.u) ≤ g.u + ε/16
  rw [anchorPrice_f]
  -- scalar facts
  have hd : (0:ℝ) < stageDelta := by norm_num [stageDelta]
  have hdd : stageDelta = 1/25000000 := rfl
  have hu0 := hS.u_nonneg
  have hu := hS.hu
  have hHeq := hS.H_eq
  have hH1 := hS.H_le_one
  have hRH := hS.RH
  have hsid := hS.s_identity
  have hR := hS.hR
  have hk := hS.hk
  have hkpos := hS.k_pos
  have hSR := hS.hSR
  have hSlow := hS.S_lower
  have hz := hS.hz
  have g2 := hS.g2
  have hd1 := del1_pos hβ0
  have hd1δ := del1_le_delta β
  have hd1β := del1_le_beta β
  set u₀ := fu R r with hu₀
  set H₀ := fH R r with hH₀
  set x := tl + 6*mesh with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxm : x ≤ 7*m := by rw [hx]; linarith
  have hule : g.u ≤ u₀ + mesh := hsel2.trans (by linarith [min_le_left u₀ (g.S - g.f)])
  have hPC : g.PC ≤ r - β + tl := by linarith
  have hHlo : H₀ - x ≤ 1 + g.t - 6*g.u := by linarith
  have hlipx : high.lip*(tl + x) ≤ ε/32 := by
    have : tl + x ≤ 8*m := by rw [hx]; linarith
    have := mul_le_mul_of_nonneg_left this hlip
    linarith
  refine ⟨by linarith, by linarith, ?_⟩
  -- HIGH: from the stage point `(r, s*, H₀)` by monotonicity and the Lipschitz bounds
  have high_bound : ∀ s' : ℝ, g.s ≤ s' →
      high.f (g.S - g.f) g.PC g.s (1 + g.t - 6*g.u) ≤
        high.f (g.S - g.f) r s' H₀ + ε/32 := by
    intro s' hs'
    have e1 := high.mono (g.S - g.f) (r + tl) g.PC s' g.s (1 + g.t - 6*g.u) (by linarith) hs'
    have e2 := hH.antiM (g.S - g.f) (r + tl) s' (H₀ + -x) (1 + g.t - 6*g.u) (by linarith)
    have e3 := high.lipM (g.S - g.f) (r + tl) s' H₀ (-x)
    rw [abs_neg, abs_of_nonneg hx0] at e3
    have e4 := high.lipP (g.S - g.f) r s' H₀ tl htl0
    have : high.lip*tl + high.lip*x = high.lip*(tl + x) := by ring
    linarith
  by_cases hw : u₀ ≤ g.S - g.f
  · -- a full selection `u ≥ u*`
    have hsel : min u₀ (g.S - g.f) = u₀ := min_eq_left hw
    rw [hsel] at hsel1
    have hss : g.s ≤ fs R z k r := by
      have : fs R z k r = fS R z k r - u₀ := rfl
      linarith
    refine max_le ?_ ?_
    · -- LOW: the previous anchor at radius `H₀ - x`
      set B₁ := R - del1 β with hB₁
      set c₁ := (1-R)/2 + z - del1 β with hc₁
      set ℓ : ℝ := β/4 with hℓ
      have hℓ0 : 0 < ℓ := by rw [hℓ]; linarith
      have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; linarith
      have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; linarith
      have hc₁1 : c₁ ≤ 1 := by rw [hc₁]; linarith
      have hn1 : deletionNeed B₁ ℓ c₁ g.PC g.s (1 + g.t - 6*g.u) ≤
          deletionNeed B₁ ℓ c₁ (r - β + tl) (fS R z k r - stageDelta - β - u₀) (H₀ - x) :=
        (deletionNeed_mono hℓ0 hPC (by linarith)).trans
          (deletionNeed_antiM hℓ0 hB₁0 hc₁0 hHlo)
      have hn2 := deletionNeed_le_max B₁ ℓ c₁ (r - β + tl) (fS R z k r - stageDelta - β - u₀)
        (H₀ - x)
      -- the cap defect: `k X = u* + k (H₀ δ₁ - δ - β + c₁ x)`
      have hX : k*((fS R z k r - stageDelta - β - u₀) - c₁*(H₀ - x)) ≤ u₀ := by
        have e : fS R z k r - u₀ = H₀*((1-R)/2 + z) + u₀/k := hsid
        have e2 : k*((fS R z k r - stageDelta - β - u₀) - c₁*(H₀ - x)) =
            u₀ + k*(H₀*del1 β - stageDelta - β + c₁*x) := by
          have : fS R z k r - stageDelta - β - u₀ = H₀*((1-R)/2 + z) + u₀/k - stageDelta - β := by
            linarith
          have hkne : k ≠ 0 := hkpos.ne'
          have hku : k*(u₀/k) = u₀ := by field_simp
          rw [this, hc₁]; linear_combination hku
        have q1 : H₀*del1 β ≤ del1 β := mul_le_of_le_one_left hd1.le hH1
        have q2 : c₁*x ≤ x := mul_le_of_le_one_left hx0 hc₁1
        have hQ : H₀*del1 β - stageDelta - β + c₁*x ≤ 0 := by linarith
        have := mul_nonpos_of_nonneg_of_nonpos hk0 hQ
        linarith
      -- the budget defect is negative: `P + ℓ s - B₁ M < 0`
      have hY : (r - β + tl + ℓ*(fS R z k r - stageDelta - β - u₀) - B₁*(H₀ - x))/ℓ < 0 := by
        apply div_neg_of_neg_of_pos _ hℓ0
        have e1 : B₁*(H₀ - x) = r - del1 β*H₀ - R*x + del1 β*x := by
          rw [hB₁]; linear_combination hRH
        have q1 : del1 β*H₀ ≤ del1 β := mul_le_of_le_one_right hd1.le hH1
        have q2 : 0 ≤ del1 β*x := mul_nonneg hd1.le hx0
        have q3 : R*x ≤ x := mul_le_of_le_one_left hx0 (by linarith)
        have q4 : ℓ*(fS R z k r - stageDelta - β - u₀) ≤ ℓ*(1/6) :=
          mul_le_mul_of_nonneg_left (by linarith) hℓ0.le
        rw [e1]
        linarith
      have hmax : max 0 (max ((fS R z k r - stageDelta - β - u₀) - c₁*(H₀ - x))
          ((r - β + tl + ℓ*(fS R z k r - stageDelta - β - u₀) - B₁*(H₀ - x))/ℓ)) ≤
          max 0 ((fS R z k r - stageDelta - β - u₀) - c₁*(H₀ - x)) :=
        max_le (le_max_left _ _) (max_le (le_max_right _ _) (hY.le.trans (le_max_left _ _)))
      have hkX : k * max 0 ((fS R z k r - stageDelta - β - u₀) - c₁*(H₀ - x)) ≤ u₀ := by
        rcases le_total ((fS R z k r - stageDelta - β - u₀) - c₁*(H₀ - x)) 0 with h0 | h0
        · rw [max_eq_left h0, mul_zero]; exact hu0
        · rw [max_eq_right h0]; exact hX
      have hk1 := mul_le_mul_of_nonneg_left (hn1.trans (hn2.trans hmax)) hk0
      linarith
    · -- HIGH
      have := high_bound (fs R z k r) hss
      have h2 : high.f (g.S - g.f) r (fs R z k r) H₀ ≤ u₀ := hH.ledger _
      linarith
  · -- not enough live marks: everything selected, `s ≤ 0`
    replace hw : g.S - g.f < u₀ := lt_of_not_ge hw
    have hsel : min u₀ (g.S - g.f) = g.S - g.f := min_eq_right hw.le
    rw [hsel] at hsel1
    have hsn : g.s ≤ 0 := by linarith
    refine max_le ?_ ?_
    · rw [deletionNeed_of_nonpos hsn, mul_zero]
      linarith
    · have := high_bound 0 hsn
      have h2 : high.f (g.S - g.f) r 0 H₀ ≤ 0 := hH.empty _
      linarith

include hS hH hβ0 hβ1 in
/-- **The step gates** of the ordinary anchor step at a stage point. -/
theorem stageGates : Ordinary.StepGates (stageData F R z k r β high hk0 hβ0) where
  face := by
    have hc := stage_c_eq F high hk0 (r := r) (z := z) (R := R) hβ0
    have hd : (0:ℝ) < stageDelta := by norm_num [stageDelta]
    have hdd : stageDelta = 1/25000000 := rfl
    have hSl := hS.S_lower
    have g2 := hS.g2
    refine ⟨?_, F.hB.2, F.hL, le_rfl, ?_, ?_, F.hc.2⟩
    · show r - β ≤ F.B₀; linarith [hS.hr.2, hS.hR.2, F.hB.1]
    · rw [hc]; linarith [hS.hr.2, hS.hR.2]
    · rw [hc]; linarith
  kappa := rfl
  crossing := by
    have hL := F.hL
    refine ⟨?_, ?_, fun _ => ?_⟩
    · show 0 ≤ (F.B₀ - (r - β))/F.L₀
      exact div_nonneg (by linarith [hS.hr.2, hS.hR.2, F.hB.1]) hL.le
    · show (F.L₀ - 0)*((F.B₀ - (r - β))/F.L₀) ≤ F.B₀ - (r - β)
      have hL0 : F.L₀ ≠ 0 := hL.ne'
      rw [sub_zero]; exact le_of_eq (by field_simp)
    · show (F.B₀ - (r - β))/F.L₀ ≤ F.c₀
      rw [div_le_iff₀ hL]
      linarith [F.hcross, hS.hr.1]
  envelope := by
    show (0:ℝ) < 1/2 ∧ (1:ℝ)/2 < 1 ∧ (3:ℝ) ≤ 3
    norm_num
  sel_spec := by
    intro ε _
    have hu0 := hS.u_nonneg
    refine ⟨fun a _ b _ hab => min_le_min le_rfl hab, fun w hw _ => ⟨le_min hu0 hw, min_le_right _ _⟩⟩
  ledger := stage_ledger F hS high hH hk0 hβ0 hβ1
  reference := ⟨1/100, stage_reference F hS high hk0 hβ0 hβ1⟩

end Gates

/-! ### The chain instance -/

/-- Positivity of an affine function on a segment from its endpoints. -/
theorem pos_affine {f : ℝ → ℝ} (hf : ∀ x, f x = f 0 + (f 1 - f 0) * x) {a b x : ℝ}
    (hab : a < b) (h1 : a ≤ x) (h2 : x ≤ b) (ha : 0 < f a) (hb : 0 < f b) : 0 < f x := by
  rw [hf] at ha hb ⊢
  exact affine_pos_of_endpoints hab h1 h2 ha hb

theorem R_real (n : ℕ) : (R n : ℝ) = 311/400 - (n:ℝ)* 11 / 64000 := by
  rw [R_eq]; push_cast; ring

theorem left_real (n : ℕ) : (left n : ℝ) = 311/400 - ((n:ℝ)+1)* 11 / 64000 := by
  rw [left_eq]; push_cast; ring

theorem R_bounds (n : ℕ) (hn : n < 256) : (7/10 : ℝ) ≤ R n ∧ (R n : ℝ) ≤ 311/400 := by
  have hn' : (n : ℝ) ≤ 255 := by exact_mod_cast Nat.lt_succ_iff.mp hn
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [R_real]
  constructor <;> linarith

theorem left_bounds (n : ℕ) (hn : n < 256) :
    (1467/2000 : ℝ) ≤ left n ∧ (left n : ℝ) = R n - 1* 11 / 64000 := by
  have hn' : (n : ℝ) ≤ 255 := by exact_mod_cast Nat.lt_succ_iff.mp hn
  rw [left_real, R_real]
  constructor
  · linarith
  · ring

theorem gain_nonneg (n : ℕ) (hn : n < 256) : (0 : ℝ) ≤ gain n := by
  rcases n with _ | m
  · rw [gain_zero]; norm_num
  · exact gain_succ_nonneg m (by omega)

/-- The scalar stage facts at every point of every stage. -/
theorem stageHyp_chain (n : ℕ) (hn : n < 256) (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) :
    StageHyp (R n) (gain n) (cut n) r := by
  obtain ⟨hR0, hR1⟩ := R_bounds n hn
  obtain ⟨hl0, hl1⟩ := left_bounds n hn
  obtain ⟨hk1, -, hk2⟩ := cut_bounds n hn
  have hRpos : (0:ℝ) < R n := by linarith
  have hlt := left_lt_R n
  refine ⟨⟨hR0, by linarith⟩, ⟨by linarith, h2⟩, ⟨hk1, hk2⟩, gain_nonneg n hn, ?_, ?_, ?_, ?_, ?_⟩
  · have g := gate2_real n hn (R n) (Or.inr rfl)
    have e : fS (R n : ℝ) (gain n) (cut n) ((R n : ℚ) : ℝ) = (1 - R n)/2 + gain n := by
      unfold fS fY fu
      rw [div_self hRpos.ne']
      ring
    rw [e] at g
    linarith
  · unfold fu
    have : (R n - r)/R n ≤ (1* 11 / 64000)/(7/10) := by
      rw [div_le_iff₀ hRpos]
      have : (1* 11 / 64000 : ℝ)/(7/10)*R n ≥ 1* 11 / 64000 := by nlinarith
      linarith
    have e : 1 - r/R n = (R n - r)/R n := by rw [sub_div, div_self hRpos.ne']
    rw [e]
    have : (1* 11 / 64000 : ℝ)/(7/10) ≤ 6/10000 := by norm_num
    linarith
  · exact pos_affine (f := fun x => 137/1000 - fS (R n : ℝ) (gain n) (cut n) x)
      (fun x => by simp only [fS, fY, fu]; ring) hlt h1 h2
      (gate2_real n hn _ (Or.inl rfl)) (gate2_real n hn _ (Or.inr rfl))
  · exact pos_affine (f := fun x => 9/10 - x - fS (R n : ℝ) (gain n) (cut n) x - 4*fu (R n : ℝ) x)
      (fun x => by simp only [fS, fY, fu]; ring) hlt h1 h2
      (gate4_real n hn _ (Or.inl rfl)) (gate4_real n hn _ (Or.inr rfl))
  · exact pos_affine
      (f := fun x => 5/6 + 21/250 - x - fS (R n : ℝ) (gain n) (cut n) x - 3*fu (R n : ℝ) x - 1/100)
      (fun x => by simp only [fS, fY, fu]; ring) hlt h1 h2
      (gate6_real n hn _ (Or.inl rfl)) (gate6_real n hn _ (Or.inr rfl))

/-- The stage ledger for the floored HIGH price (floor `R n + 10^-6`), as a proposition; it is
proved by `High.chain_highPriceW_le`. -/
def ChainHighLedger : Prop :=
  ∀ n : ℕ, n < 256 → ∀ r : ℝ, (left n : ℝ) ≤ r → r ≤ R n →
    High.highPriceFW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) r
      (fs (R n : ℝ) (gain n) (cut n) r) (fH (R n : ℝ) r) ≤ fu (R n : ℝ) r

theorem cut_nonneg (n : ℕ) (hn : n < 256) : (0:ℝ) ≤ cut n := by
  linarith [(cut_bounds n hn).1]

theorem cut_le (n : ℕ) (hn : n < 256) : (cut n : ℝ) ≤ 3/4 := by
  linarith [(cut_bounds n hn).2.2]

/-- The HIGH facts at every stage point, for the floored HIGH price, from its stage ledger. -/
theorem highAt_chain (hL : ChainHighLedger) (n : ℕ) (hn : n < 256) (r : ℝ)
    (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) :
    HighAt (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
      (cut_le n hn)) (R n) (gain n) (cut n) r := by
  have hS := stageHyp_chain n hn r h1 h2
  refine highAt_highPriceW (cut_nonneg n hn) hS.hk.1 (cut_le n hn) hS.hR.1 hS.hR.2 ?_
    (by linarith) (hL n hn r h1 h2)
  have := hS.H_ge
  unfold fH at this
  linarith

/-- **The step gates at every stage point** (chain data, any parent face). -/
theorem chain_stageGates (F : ParentFace) (hL : ChainHighLedger) (n : ℕ) (hn : n < 256) (r : ℝ)
    (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000) :
    Ordinary.StepGates (stageData F (R n) (gain n) (cut n) r β
      (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
        (cut_le n hn)) (cut_nonneg n hn) hβ0) :=
  stageGates F (stageHyp_chain n hn r h1 h2) _ (highAt_chain hL n hn r h1 h2) (cut_nonneg n hn)
    hβ0 hβ1

end
end Qrh.MarkedAnchor.Price
