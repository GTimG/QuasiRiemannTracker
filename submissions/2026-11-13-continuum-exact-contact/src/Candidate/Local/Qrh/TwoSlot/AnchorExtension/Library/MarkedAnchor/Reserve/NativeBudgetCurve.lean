/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Joseph Bebel.
Finite source-line transport with explicit seed and selected-energy inputs.
Adapted from Joseph Bebel's PR98 RefinedSource at
72682aa1c6584fbc4be0dc81a91333116dc54a7a, in turn adapted from
ArviFoxy's Curve.lean and NativeStart.lean at
62b12e08066b0269a01f34696ace896e3cb5eb32. Original attribution retained.
The generic curve induction supplies a finite construction without enumerating steps.
Adapted by Joseph Bebel (2026-10-31) for B = 1-10^-256 and L = 2+10^-255.
Reserve-parametric version (B = 1-ε) by Joe Richey, submission exact-contact-point
(QuasiRiemannTracker #129, commit 535397cd), Apache-2.0; inherited notices retained. -/
/- Modified by Sil (2026-11-11): copied from exact-contact-point (#129) PositiveGap/NativeBudgetCurve.lean,
namespace changed to Qrh.MarkedAnchor.Reserve.NativeBudget; otherwise unchanged. -/
import Submissions.arvi_selected_leaf.Curve
import Submissions.arvi_selected_leaf.R1.Cap
set_option autoImplicit false
namespace Qrh.MarkedAnchor.Reserve.NativeBudget
noncomputable section
open Set QRH.ArviSelectedLeaf QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
open OAI.SevenEighths QRH.Record1252270103Source
def rB (ε : ℝ) : ℝ := 1 - ε
def rLow : ℝ := 5143/2000
def rTop : ℝ := 93/25
def rGamma : ℝ := 80/2297
def rCap (L : ℝ) : ℝ := 3/50 + rGamma * (rTop - L)
def rFace (ε L : ℝ) : Face := ⟨rB ε, L, rCap L⟩
def rA : ℝ := 1/10
def rK : ℝ := 3/4
def rStep : ℝ := 1/100000
theorem rCap_ge {L : ℝ} (h : L ≤ rTop) : 3/50 ≤ rCap L := by
  unfold rCap rGamma
  linarith only [h]
theorem rCap_le {L : ℝ} (h : rLow ≤ L) : rCap L ≤ 1/10 := by
  unfold rLow at h
  unfold rCap rGamma rTop
  linarith only [h]
theorem rCap_step (L₀ L : ℝ) : rCap L = rCap L₀ + rGamma * (L₀ - L) := by
  unfold rCap
  ring
theorem cap_gate_aux {c d : ℝ} (hc0 : 3/50 ≤ c) (hc1 : c ≤ 1/10)
    (hd0 : 0 ≤ d) (hd1 : d ≤ rStep) :
    0 < c * (1 - 6*rA*(c+rGamma*d)) - (1-rA)*(c+rGamma*d) := by
  have hc : 0 ≤ c := by linarith only [hc0]
  have h6 : 0 ≤ 1 - 6*c := by linarith only [hc1]
  have h1 : 0 ≤ rA * (c - 3/50) * (1 - 6*(1/10:ℝ)) := by
    apply mul_nonneg
    · exact mul_nonneg (by unfold rA; norm_num) (sub_nonneg.mpr hc0)
    · norm_num
  have h2 : 0 ≤ 6*rA*c*(1/10-c) := by
    exact mul_nonneg (mul_nonneg (by unfold rA; norm_num) hc) (sub_nonneg.mpr hc1)
  have h3 : 0 ≤ rGamma*(rStep-d) := by
    exact mul_nonneg (by unfold rGamma; norm_num) (sub_nonneg.mpr hd1)
  have h4 : 0 ≤ rA*rGamma*d*(1-6*c) := by
    exact mul_nonneg (mul_nonneg (by unfold rA rGamma; norm_num) hd0) h6
  have hid : c * (1 - 6*rA*(c+rGamma*d)) - (1-rA)*(c+rGamma*d) =
      (rA*(3/50)*(1-6*(1/10:ℝ))-rGamma*rStep)
        + rA*(c-3/50)*(1-6*(1/10:ℝ)) + 6*rA*c*(1/10-c)
        + rGamma*(rStep-d) + rA*rGamma*d*(1-6*c) := by ring
  have hm : 0 < rA*(3/50)*(1-6*(1/10:ℝ))-rGamma*rStep := by
    unfold rA rGamma rStep
    norm_num
  linarith only [hid, hm, h1, h2, h3, h4]
theorem refined_gates {ε L₀ L : ℝ} (hε0 : 0 < ε) (_hε1 : ε ≤ 1/1000000000)
    (hL₀ : L₀ ∈ Icc rLow rTop)
    (hL : L ∈ Icc rLow rTop) (hlt : L < L₀) (hle : L₀ - L ≤ rStep) :
    E5Gates (rFace ε L₀) (rFace ε L) rA rK := by
  obtain ⟨a0, a1⟩ := hL₀
  obtain ⟨b0, b1⟩ := hL
  have hc0 : 3/50 ≤ rCap L₀ := rCap_ge a1
  have hc1 : rCap L₀ ≤ 1/10 := rCap_le a0
  have hcy0 : 3/50 ≤ rCap L := rCap_ge b1
  have hcy1 : rCap L ≤ 1/10 := rCap_le b0
  have hL0 : 0 < L₀ := by unfold rLow at a0; linarith only [a0]
  unfold rLow at a0 b0
  unfold rStep at hle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < rA-rK*(L₀-L+(6*rB ε-L₀)*rA)/L₀
    unfold rA rK rB
    rw [sub_pos, div_lt_iff₀ hL0]
    linarith only [a0, hle, hε0]
  · show 0 < rCap L₀*(1-6*rA*rCap L)-(1-rA)*rCap L
    rw [rCap_step L₀ L]
    exact cap_gate_aux hc0 hc1 (sub_nonneg.mpr hlt.le) hle
  · show 0 < L-2-9/2*rA
    unfold rA
    linarith only [b0]
  · show 0 < L-1-4*rA
    unfold rA
    linarith only [b0]
  · show 0 < 3/2*L-5/2-9/2*rA
    unfold rA
    linarith only [b0]
  · show 0 < 1/6-(1+3/2*rA)*rCap L
    unfold rA
    linarith only [hcy1]
  · show 0 < 1-6*rA*rCap L
    unfold rA
    linarith only [hcy1]
  · show 0 < 1-rK*(6*rB ε-L₀)/L₀
    unfold rK rB
    rw [sub_pos, div_lt_iff₀ hL0]
    linarith only [a0, hε0]
  · show rB ε < 1
    unfold rB
    linarith only [hε0]
  · show rCap L₀ < 1/6
    linarith only [hc1]
  · show 0 < rCap L
    linarith only [hcy0]
  · show 0 < rA
    unfold rA
    norm_num
  · show rA < 1
    unfold rA
    norm_num
  · exact hlt
  · show 0 < rK
    unfold rK
    norm_num
  · show rK ≤ 3/4
    unfold rK
    norm_num
theorem refined_leaf {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hR1 : SelectedRootEnergy rK)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {L₀ L : ℝ} (hL₀ : L₀ ∈ Icc rLow rTop)
    (h : E5Gates (rFace ε L₀) (rFace ε L) rA rK) :
    E5Leaf (rFace ε L₀) (rFace ε L) rA rK h := by
  intro hp
  have hc0 : 0 < rCap L₀ := by
    have := rCap_ge hL₀.2
    linarith only [this]
  have hH : 0 < 1-6*rA*rCap L := h.H
  have ha : 0 < rA := h.a_pos
  have hc : 0 < rCap L := h.cap_pos
  have hB0 : 0 < rB ε := by unfold rB; linarith only [hε1]
  have hB1 : rB ε ≤ 1 := by unfold rB; linarith only [hε0]
  exact e5_priced_source rK h.K_pos h.K_le hR1 (rB ε) L₀ (rCap L₀)
    ((1-6*rA*rCap L)/2) (3+1) hβ ⟨h.L₀_pos, hB0, hB1, hc0⟩
    (div_pos hH two_pos) (by have := mul_pos ha hc; linarith only [this]) hp
theorem refined_sources {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hR1 : SelectedRootEnergy rK)
    (hseed : GlobalSource (rB ε) rTop (3/50)) :
    ∀ L ∈ Icc rLow rTop, GlobalSource (rB ε) L (rCap L) := by
  have htop : GlobalSource (rB ε) rTop (rCap rTop) := by
    simpa only [rCap, sub_self, mul_zero, add_zero] using hseed
  exact QRH.ArviSelectedLeaf.Native.curve_induction
    (fun L => GlobalSource (rB ε) L (rCap L))
    (by unfold rStep; norm_num : 0 < rStep) htop
    (fun L₀ hL₀ L hL hlt hle hsrc => by
      have hg := refined_gates hε0 hε1 hL₀ hL hlt hle
      exact e5_step (p := rFace ε L₀) (n := rFace ε L) hg
        (refined_leaf hε0 hε1 hR1 hβ hL₀ hg) hβ hsrc)
theorem refined_end {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hR1 : SelectedRootEnergy rK)
    (hseed : GlobalSource (rB ε) rTop (3/50)) :
    GlobalSource (1 - ε) (5143/2000) (1/10) := by
  have h := refined_sources hε0 hε1 hβ hR1 hseed rLow ⟨le_rfl, by unfold rLow rTop; norm_num⟩
  have hc : rCap rLow = 1/10 := by unfold rCap rLow rTop rGamma; norm_num
  rw [hc] at h
  simpa only [rB, rLow] using h
end
end Qrh.MarkedAnchor.Reserve.NativeBudget
