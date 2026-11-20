/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
O.2 stage gates, adapted from Sil/Bebel's pinned PR141 Price.Gates.
The source contract is unchanged; the lower anchor and cap collars are explicit. -/
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorZeroLoss.OrdinaryStage
set_option autoImplicit false
noncomputable section
namespace QRH.Cycle092.TangentExtension
open Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.MarkedAnchor.Price
structure ParentFace where
  B₀ : ℝ
  L₀ : ℝ
  c₀ : ℝ
  hB : 7/9 < B₀ ∧ B₀ < 1
  hL : 0 < L₀
  hc : 0 < c₀ ∧ c₀ < 1/6
  /-- the crossing `s₀ = (B₀ - r + β)/L₀` stays below the cap for `r ≥ 18/25`, `β ≤ 1/1000` -/
  hcross : B₀ - 18/25 + 1/1000 ≤ c₀*L₀

structure StageHyp (R z k r : ℝ) : Prop where
  hR : 7/10 ≤ R ∧ R ≤ 7/9
  hr : 18/25 ≤ r ∧ r ≤ R
  hk : 45457/125000 ≤ k ∧ k < 1/2
  hz : 0 ≤ z
  hSR : (1-R)/2 + z ≤ 73/500
  hu : fu R r ≤ 1/10000
  g2 : 0 < 73/500 - fS R z k r
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


end QRH.Cycle092.TangentExtension
