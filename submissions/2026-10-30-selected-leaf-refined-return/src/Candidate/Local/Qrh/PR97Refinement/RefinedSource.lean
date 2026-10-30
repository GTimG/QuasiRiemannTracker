/-
Copyright (c) 2026 Joseph Bebel.

Review candidate extending PR97's selected-leaf source line.
Adapted from ArviFoxy's Curve.lean and NativeStart.lean at commit
62b12e08066b0269a01f34696ace896e3cb5eb32; original attribution is preserved here.

The cut K is the lower endpoint already allowed by PR97's R1 theorem.
-/
import Submissions.arvi_selected_leaf.Curve
import Submissions.arvi_selected_leaf.R1.Cap

set_option autoImplicit false

namespace QRH.QrhPR97Refinement
noncomputable section
open Set QRH.ArviSelectedLeaf QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
open OAI.SevenEighths QRH.Record1252270103Source

def rB : ℝ := 99999/100000
def rLow : ℝ := 200001/100000
def rTop : ℝ := 5143/2000
def rGamma : ℝ := 5000/57149
def rCap (L : ℝ) : ℝ := 1/10 + rGamma * (rTop - L)
def rFace (L : ℝ) : Face := ⟨rB, L, rCap L⟩
def rA : ℝ := 1/1000000
def rK : ℝ := 500001/1000000
def rStep : ℝ := 1/1000000000000

theorem rCap_ge {L : ℝ} (h : L ≤ rTop) : 1/10 ≤ rCap L := by
  unfold rCap rGamma
  linarith only [h]

theorem rCap_le {L : ℝ} (h : rLow ≤ L) : rCap L ≤ 3/20 := by
  unfold rLow at h
  unfold rCap rGamma rTop
  linarith only [h]

theorem rCap_step (L₀ L : ℝ) : rCap L = rCap L₀ + rGamma * (L₀ - L) := by
  unfold rCap
  ring

/-- Uniform cap gate. The four nonnegative terms below give the exact identity
used by the independent rational checker; the constant remainder is positive. -/
theorem cap_gate_aux {c d : ℝ} (hc0 : 1/10 ≤ c) (hc1 : c ≤ 3/20)
    (hd0 : 0 ≤ d) (hd1 : d ≤ rStep) :
    0 < c * (1 - 6*rA*(c+rGamma*d)) - (1-rA)*(c+rGamma*d) := by
  have hc : 0 ≤ c := by linarith only [hc0]
  have h6 : 0 ≤ 1 - 6*c := by linarith only [hc1]
  have h1 : 0 ≤ rA * (c - 1/10) * (1 - 6*(3/20:ℝ)) := by
    apply mul_nonneg
    · exact mul_nonneg (by unfold rA; norm_num) (sub_nonneg.mpr hc0)
    · norm_num
  have h2 : 0 ≤ 6*rA*c*(3/20-c) := by
    exact mul_nonneg (mul_nonneg (by unfold rA; norm_num) hc) (sub_nonneg.mpr hc1)
  have h3 : 0 ≤ rGamma*(rStep-d) := by
    exact mul_nonneg (by unfold rGamma; norm_num) (sub_nonneg.mpr hd1)
  have h4 : 0 ≤ rA*rGamma*d*(1-6*c) := by
    exact mul_nonneg (mul_nonneg (by unfold rA rGamma; norm_num) hd0) h6
  have hid : c * (1 - 6*rA*(c+rGamma*d)) - (1-rA)*(c+rGamma*d) =
      (rA*(1/10)*(1-6*(3/20:ℝ))-rGamma*rStep)
        + rA*(c-1/10)*(1-6*(3/20:ℝ)) + 6*rA*c*(3/20-c)
        + rGamma*(rStep-d) + rA*rGamma*d*(1-6*c) := by ring
  have hm : 0 < rA*(1/10)*(1-6*(3/20:ℝ))-rGamma*rStep := by
    unfold rA rGamma rStep
    norm_num
  linarith only [hid, hm, h1, h2, h3, h4]

/-- All seventeen literal PR97 gates for every short step in the whole interval. -/
theorem refined_gates {L₀ L : ℝ} (hL₀ : L₀ ∈ Icc rLow rTop)
    (hL : L ∈ Icc rLow rTop) (hlt : L < L₀) (hle : L₀ - L ≤ rStep) :
    E5Gates (rFace L₀) (rFace L) rA rK := by
  obtain ⟨a0, a1⟩ := hL₀
  obtain ⟨b0, b1⟩ := hL
  have hc0 : 1/10 ≤ rCap L₀ := rCap_ge a1
  have hc1 : rCap L₀ ≤ 3/20 := rCap_le a0
  have hcy0 : 1/10 ≤ rCap L := rCap_ge b1
  have hcy1 : rCap L ≤ 3/20 := rCap_le b0
  have hL0 : 0 < L₀ := by unfold rLow at a0; linarith only [a0]
  unfold rLow at a0 b0
  unfold rStep at hle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < rA-rK*(L₀-L+(6*rB-L₀)*rA)/L₀
    unfold rA rK rB
    rw [sub_pos, div_lt_iff₀ hL0]
    linarith only [a0, hle]
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
  · show 0 < 1-rK*(6*rB-L₀)/L₀
    unfold rK rB
    rw [sub_pos, div_lt_iff₀ hL0]
    linarith only [a0]
  · show rB < 1
    unfold rB
    norm_num
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

theorem refined_leaf (hR1 : SelectedRootEnergy rK)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {L₀ L : ℝ} (hL₀ : L₀ ∈ Icc rLow rTop)
    (h : E5Gates (rFace L₀) (rFace L) rA rK) :
    E5Leaf (rFace L₀) (rFace L) rA rK h := by
  intro hp
  have hc0 : 0 < rCap L₀ := by
    have := rCap_ge hL₀.2
    linarith only [this]
  have hH : 0 < 1-6*rA*rCap L := h.H
  have ha : 0 < rA := h.a_pos
  have hc : 0 < rCap L := h.cap_pos
  have hB0 : 0 < rB := by unfold rB; norm_num
  have hB1 : rB ≤ 1 := by unfold rB; norm_num
  exact e5_priced_source rK h.K_pos h.K_le hR1 rB L₀ (rCap L₀)
    ((1-6*rA*rCap L)/2) (3+1) hβ ⟨h.L₀_pos, hB0, hB1, hc0⟩
    (div_pos hH two_pos) (by have := mul_pos ha hc; linarith only [this]) hp

/-- Conditional only on the same beta lower bound as the original native start. -/
theorem refined_sources (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ L ∈ Icc rLow rTop, GlobalSource rB L (rCap L) := by
  have hR1 : SelectedRootEnergy rK :=
    selectedRootEnergy rK (by unfold rK; norm_num) (by unfold rK; norm_num)
  have htop : GlobalSource rB rTop (rCap rTop) := by
    have h := QRH.ArviSelectedLeaf.Native.native_end hβ
    simpa only [rB, rTop, rCap, sub_self, mul_zero, add_zero] using h
  exact QRH.ArviSelectedLeaf.Native.curve_induction
    (fun L => GlobalSource rB L (rCap L))
    (by unfold rStep; norm_num : 0 < rStep) htop
    (fun L₀ hL₀ L hL hlt hle hsrc => by
      have hg := refined_gates hL₀ hL hlt hle
      exact e5_step (p := rFace L₀) (n := rFace L) hg
        (refined_leaf hR1 hβ hL₀ hg) hβ hsrc)

theorem refined_end (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (200001/100000) (3/20) := by
  have h := refined_sources hβ rLow ⟨le_rfl, by unfold rLow rTop; norm_num⟩
  have hc : rCap rLow = 3/20 := by unfold rCap rLow rTop rGamma; norm_num
  rw [hc] at h
  simpa only [rB, rLow] using h

end
end QRH.QrhPR97Refinement

#print axioms QRH.QrhPR97Refinement.refined_end
