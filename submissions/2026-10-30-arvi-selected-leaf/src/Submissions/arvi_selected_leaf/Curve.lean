/-
The selected-leaf native line, as a continuous curve.

From the end of the native line `G(99999/100000, 5143/2000, 1/10)` (`Native.native_end`, the copy of
`ArviOdeShape.native_end` that does not import the density chain), the selected-leaf native step (`e5_step`, deletion
cut `K = 501/1000`, selected fraction `a = 1/1000`) is valid from every face `(B, Λ₀, c(Λ₀))` of the line
`c(Λ) = 1/10 + γ (5143/2000 - Λ)` to every face at most `5·10⁻⁶` further down. So every face of the line,
`Λ ∈ [401/200, 5143/2000]`, is proven by one induction, given the selected root energy (R1).
-/
import Submissions.arvi_selected_leaf.Step
import Submissions.arvi_selected_leaf.Leaf
import Submissions.arvi_selected_leaf.NativeStart

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree Set
open OAI.SevenEighths QRH.Record1252270103Source

/-- The selected-leaf line: budget `99999/100000`, cap `c(Λ) = 1/10 + (3/50)(5143/2000 - Λ)`. -/
def sB : ℝ := 99999/100000
def sCap (Λ : ℝ) : ℝ := 1/10 + 3/50 * (5143/2000 - Λ)
def sFace (Λ : ℝ) : Face := ⟨sB, Λ, sCap Λ⟩
def sA : ℝ := 1/1000
def sK : ℝ := 501/1000

/-- The cap of the line is at least `1/10` below the top `5143/2000`. -/
theorem sCap_ge {Λ : ℝ} (h : Λ ≤ 5143/2000) : 1/10 ≤ sCap Λ := by
  unfold sCap; linarith only [h]

/-- The cap of the line is at most `13399/100000` above the end `401/200`. -/
theorem sCap_le {Λ : ℝ} (h : 401/200 ≤ Λ) : sCap Λ ≤ 13399/100000 := by
  unfold sCap; linarith only [h]

/-- One step down the line raises the cap by `3/50` times the step. -/
theorem sCap_step (Λ₀ Λ : ℝ) : sCap Λ = sCap Λ₀ + 3/50 * (Λ₀ - Λ) := by
  unfold sCap; ring

/-- The `cap` gate of a step of length `d ≤ 1/200000` from a parent of cap `c ∈ [1/10, 3/20]`. -/
theorem cap_gate_aux {c d : ℝ} (hc0 : 1/10 ≤ c) (hc1 : c ≤ 3/20) (hd0 : 0 ≤ d) (hd1 : d ≤ 1/200000) :
    0 < c * (1 - 6 * sA * (c + 3/50 * d)) - (1 - sA) * (c + 3/50 * d) := by
  have h1 := mul_nonneg (sub_nonneg.2 hc0) (sub_nonneg.2 hc1)
  have h2 := mul_le_mul_of_nonneg_right hc1 hd0
  unfold sA
  linarith only [h1, h2, hc1, hd1]

/-- **The selected-leaf generator**: one step along the line. -/
theorem e5_gates {Λ₀ Λ : ℝ} (hΛ₀ : Λ₀ ∈ Icc (401/200 : ℝ) (5143/2000))
    (hΛ : Λ ∈ Icc (401/200 : ℝ) (5143/2000)) (hlt : Λ < Λ₀) (hle : Λ₀ - Λ ≤ 1/200000) :
    E5Gates (sFace Λ₀) (sFace Λ) sA sK := by
  obtain ⟨a0, a1⟩ := hΛ₀
  obtain ⟨b0, b1⟩ := hΛ
  have hc0 : 1/10 ≤ sCap Λ₀ := sCap_ge a1
  have hc1 : sCap Λ₀ ≤ 3/20 := (sCap_le a0).trans (by norm_num)
  have hcy0 : 1/10 ≤ sCap Λ := sCap_ge b1
  have hcy1 : sCap Λ ≤ 3/20 := (sCap_le b0).trans (by norm_num)
  have hL0 : (0:ℝ) < Λ₀ := by linarith only [a0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < sA - sK * (Λ₀ - Λ + (6 * sB - Λ₀) * sA) / Λ₀
    unfold sA sK sB; rw [sub_pos, div_lt_iff₀ hL0]; linarith only [a0, hle]
  · show 0 < sCap Λ₀ * (1 - 6 * sA * sCap Λ) - (1 - sA) * sCap Λ
    rw [sCap_step Λ₀ Λ]
    exact cap_gate_aux hc0 hc1 (sub_nonneg.2 hlt.le) hle
  · show 0 < Λ - 2 - 9/2 * sA
    unfold sA; linarith only [b0]
  · show 0 < Λ - 1 - 4 * sA
    unfold sA; linarith only [b0]
  · show 0 < 3/2 * Λ - 5/2 - 9/2 * sA
    unfold sA; linarith only [b0]
  · show 0 < 1/6 - (1 + 3/2 * sA) * sCap Λ
    unfold sA; linarith only [hcy1]
  · show 0 < 1 - 6 * sA * sCap Λ
    unfold sA; linarith only [hcy1]
  · show 0 < 1 - sK * (6 * sB - Λ₀) / Λ₀
    unfold sK sB; rw [sub_pos, div_lt_iff₀ hL0]; linarith only [a0]
  · show sB < 1
    unfold sB; norm_num
  · show sCap Λ₀ < 1/6
    linarith only [hc1]
  · show 0 < sCap Λ
    linarith only [hcy0]
  · show 0 < sA
    unfold sA; norm_num
  · show sA < 1
    unfold sA; norm_num
  · show Λ < Λ₀
    exact hlt
  · show 0 < sK
    unfold sK; norm_num
  · show sK ≤ 3/4
    unfold sK; norm_num

/-- The selected leaf for every step of the line, from the selected root energy (R1). -/
theorem line_leaf (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {Λ₀ Λ : ℝ} (hΛ₀ : Λ₀ ∈ Icc (401/200 : ℝ) (5143/2000)) (h : E5Gates (sFace Λ₀) (sFace Λ) sA sK) :
    E5Leaf (sFace Λ₀) (sFace Λ) sA sK h := by
  intro hp
  have hc0 : 0 < sCap Λ₀ := by
    have := sCap_ge hΛ₀.2
    linarith only [this]
  have hH : 0 < 1 - 6 * sA * sCap Λ := h.H
  have ha : 0 < sA := h.a_pos
  have hc : 0 < sCap Λ := h.cap_pos
  have hB0 : 0 < sB := by unfold sB; norm_num
  have hB1 : sB ≤ 1 := by unfold sB; norm_num
  exact e5_priced_source sK h.K_pos h.K_le hR1 sB Λ₀ (sCap Λ₀) ((1 - 6*sA*sCap Λ)/2) (3 + 1) hβ
    ⟨h.L₀_pos, hB0, hB1, hc0⟩ (div_pos hH two_pos)
    (by have := mul_pos ha hc; linarith only [this]) hp

/-- **Every face of the selected-leaf line is proven**, from the end of the native line, by one
induction, given the selected root energy (R1). -/
theorem e5_sources (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ Λ ∈ Icc (401/200 : ℝ) (5143/2000), GlobalSource sB Λ (sCap Λ) := by
  have htop : GlobalSource sB (5143/2000) (sCap (5143/2000)) := by
    have h := Native.native_end hβ
    have e : sCap (5143/2000) = 1/10 := by unfold sCap; norm_num
    rw [e]; simpa only [sB] using h
  exact Native.curve_induction (fun Λ => GlobalSource sB Λ (sCap Λ))
    (by norm_num : (0:ℝ) < 1/200000) htop
    (fun Λ₀ hΛ₀ Λ hΛ hlt hle hsrc => by
      have hg := e5_gates hΛ₀ hΛ hlt hle
      exact e5_step (p := sFace Λ₀) (n := sFace Λ) hg (line_leaf hR1 hβ hΛ₀ hg) hβ hsrc)

/-- The end of the selected-leaf line: `G(99999/100000, 401/200, c(401/200))`, `c = 1/10 + 3399/100000`
(`= 13399/100000`). -/
theorem e5_end (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (401/200) (1/10 + 3/50 * (5143/2000 - 401/200)) := by
  have h := e5_sources hR1 hβ (401/200) ⟨le_rfl, by norm_num⟩
  simpa only [sB, sCap] using h

end
end QRH.ArviSelectedLeaf
