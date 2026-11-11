import Submissions.arvi_selected_leaf.Curve
import Submissions.arvi_selected_leaf.R1.Cap
set_option autoImplicit false
namespace QRH.PositiveGapTightSelected
noncomputable section
open Set QRH.ArviSelectedLeaf QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
open OAI.SevenEighths QRH.Record1252270103Source
def rB (ε : ℝ) : ℝ := 1 - ε
def rLow (ε : ℝ) : ℝ := 2 + 10 * ε
def rTop : ℝ := 5143/2000
def rGamma : ℝ := 3/50
def rCap (L : ℝ) : ℝ := 1/10 + rGamma * (rTop - L)
def rFace (ε L : ℝ) : Face := ⟨rB ε, L, rCap L⟩
def rA (ε : ℝ) : ℝ := ε / 10
def rK (ε : ℝ) : ℝ := 1/2 + ε
def rStep (ε : ℝ) : ℝ := ε ^ 2
theorem rCap_ge {L : ℝ} (h : L ≤ rTop) : 1/10 ≤ rCap L := by
  unfold rCap rGamma
  linarith only [h]
theorem rCap_le {ε L : ℝ} (hε0 : 0 < ε) (h : rLow ε ≤ L) : rCap L ≤ 3/20 := by
  unfold rLow at h
  unfold rCap rGamma rTop
  linarith only [h, hε0]
theorem rCap_step (L₀ L : ℝ) : rCap L = rCap L₀ + rGamma * (L₀ - L) := by
  unfold rCap
  ring
theorem cap_gate_aux {ε c d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hc0 : 1/10 ≤ c) (hc1 : c ≤ 3/20)
    (hd0 : 0 ≤ d) (hd1 : d ≤ rStep ε) :
    0 < c * (1 - 6*rA ε*(c+rGamma*d)) - (1-rA ε)*(c+rGamma*d) := by
  have hc : 0 ≤ c := by linarith only [hc0]
  have h6 : 0 ≤ 1 - 6*c := by linarith only [hc1]
  have hrA : 0 ≤ rA ε := by unfold rA; positivity
  have h1 : 0 ≤ rA ε * (c - 1/10) * (1 - 6*(3/20:ℝ)) := by
    apply mul_nonneg
    · exact mul_nonneg hrA (sub_nonneg.mpr hc0)
    · norm_num
  have h2 : 0 ≤ 6*rA ε*c*(3/20-c) := by
    exact mul_nonneg (mul_nonneg (by positivity) hc) (sub_nonneg.mpr hc1)
  have h3 : 0 ≤ rGamma*(rStep ε-d) := by
    exact mul_nonneg (by unfold rGamma; norm_num) (sub_nonneg.mpr hd1)
  have h4 : 0 ≤ rA ε*rGamma*d*(1-6*c) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hrA (by unfold rGamma; norm_num)) hd0) h6
  have hid : c * (1 - 6*rA ε*(c+rGamma*d)) - (1-rA ε)*(c+rGamma*d) =
      (rA ε*(1/10)*(1-6*(3/20:ℝ))-rGamma*rStep ε)
        + rA ε*(c-1/10)*(1-6*(3/20:ℝ)) + 6*rA ε*c*(3/20-c)
        + rGamma*(rStep ε-d) + rA ε*rGamma*d*(1-6*c) := by ring
  have hm : 0 < rA ε*(1/10)*(1-6*(3/20:ℝ))-rGamma*rStep ε := by
    have heq : rA ε*(1/10)*(1-6*(3/20:ℝ))-rGamma*rStep ε = ε * (1/1000 - 3/50 * ε) := by
      unfold rA rGamma rStep; ring
    rw [heq]
    exact mul_pos hε0 (by linarith only [hε1])
  linarith only [hid, hm, h1, h2, h3, h4]
theorem refined_gates {ε L₀ L : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hL₀ : L₀ ∈ Icc (rLow ε) rTop)
    (hL : L ∈ Icc (rLow ε) rTop) (hlt : L < L₀) (hle : L₀ - L ≤ rStep ε) :
    E5Gates (rFace ε L₀) (rFace ε L) (rA ε) (rK ε) := by
  obtain ⟨a0, a1⟩ := hL₀
  obtain ⟨b0, b1⟩ := hL
  have hc0 : 1/10 ≤ rCap L₀ := rCap_ge a1
  have hc1 : rCap L₀ ≤ 3/20 := rCap_le hε0 a0
  have hcy0 : 1/10 ≤ rCap L := rCap_ge b1
  have hcy1 : rCap L ≤ 3/20 := rCap_le hε0 b0
  have hL0 : 0 < L₀ := by unfold rLow at a0; linarith only [a0, hε0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < rA ε-rK ε*(L₀-L+(6*rB ε-L₀)*rA ε)/L₀
    rw [sub_pos, div_lt_iff₀ hL0, ← sub_pos]
    have hid : rA ε * L₀ - rK ε * (L₀ - L + (6 * rB ε - L₀) * rA ε) =
        (ε / 10) * (3 / 2 + ε) * (L₀ - rLow ε) + (1 / 2 + ε) * (rStep ε - (L₀ - L)) +
        9 / 10 * ε ^ 2 + 3 / 5 * ε ^ 3 := by
      unfold rA rK rB rLow rStep; ring
    rw [hid]
    have t1 : 0 ≤ (ε / 10) * (3 / 2 + ε) * (L₀ - rLow ε) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr a0)
    have t2 : 0 ≤ (1 / 2 + ε) * (rStep ε - (L₀ - L)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hle)
    have t3 : 0 < 9 / 10 * ε ^ 2 + 3 / 5 * ε ^ 3 := by positivity
    linarith only [t1, t2, t3]
  · show 0 < rCap L₀*(1-6*rA ε*rCap L)-(1-rA ε)*rCap L
    rw [rCap_step L₀ L]
    exact cap_gate_aux hε0 hε1 hc0 hc1 (sub_nonneg.mpr hlt.le) hle
  · show 0 < L-2-9/2*rA ε
    unfold rLow at b0; unfold rA
    linarith only [b0, hε0]
  · show 0 < L-1-4*rA ε
    unfold rLow at b0; unfold rA
    linarith only [b0, hε0]
  · show 0 < 3/2*L-5/2-9/2*rA ε
    unfold rLow at b0; unfold rA
    linarith only [b0, hε0]
  · show 0 < 1/6-(1+3/2*rA ε)*rCap L
    have h1 : 0 ≤ rCap L := by linarith only [hcy0]
    have h2 : rA ε ≤ 1/100 := by unfold rA; linarith only [hε1]
    nlinarith only [hcy1, h1, h2]
  · show 0 < 1-6*rA ε*rCap L
    have h1 : 0 ≤ rCap L := by linarith only [hcy0]
    have h2 : rA ε ≤ 1/100 := by unfold rA; linarith only [hε1]
    nlinarith only [hcy1, h1, h2]
  · show 0 < 1-rK ε*(6*rB ε-L₀)/L₀
    rw [sub_pos, div_lt_iff₀ hL0, one_mul, ← sub_pos]
    have hid : L₀ - rK ε * (6 * rB ε - L₀) =
        (3 / 2 + ε) * (L₀ - rLow ε) + 14 * ε + 16 * ε ^ 2 := by
      unfold rK rB rLow; ring
    rw [hid]
    have t1 : 0 ≤ (3 / 2 + ε) * (L₀ - rLow ε) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr a0)
    have t2 : 0 < 14 * ε + 16 * ε ^ 2 := by positivity
    linarith only [t1, t2]
  · show rB ε < 1
    unfold rB; linarith only [hε0]
  · show rCap L₀ < 1/6
    linarith only [hc1]
  · show 0 < rCap L
    linarith only [hcy0]
  · show 0 < rA ε
    unfold rA; positivity
  · show rA ε < 1
    unfold rA; linarith only [hε1]
  · exact hlt
  · show 0 < rK ε
    unfold rK; positivity
  · show rK ε ≤ 3/4
    unfold rK; linarith only [hε1]
theorem refined_leaf {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hR1 : SelectedRootEnergy (rK ε))
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {L₀ L : ℝ} (hL₀ : L₀ ∈ Icc (rLow ε) rTop)
    (h : E5Gates (rFace ε L₀) (rFace ε L) (rA ε) (rK ε)) :
    E5Leaf (rFace ε L₀) (rFace ε L) (rA ε) (rK ε) h := by
  intro hp
  have hc0 : 0 < rCap L₀ := by
    have := rCap_ge hL₀.2
    linarith only [this]
  have hH : 0 < 1-6*rA ε*rCap L := h.H
  have ha : 0 < rA ε := h.a_pos
  have hc : 0 < rCap L := h.cap_pos
  have hB0 : 0 < rB ε := by unfold rB; linarith only [hε1]
  have hB1 : rB ε ≤ 1 := by unfold rB; linarith only [hε0]
  exact e5_priced_source (rK ε) h.K_pos h.K_le hR1 (rB ε) L₀ (rCap L₀)
    ((1-6*rA ε*rCap L)/2) (3+1) hβ ⟨h.L₀_pos, hB0, hB1, hc0⟩
    (div_pos hH two_pos) (by have := mul_pos ha hc; linarith only [this]) hp
theorem refined_sources {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hR1 : SelectedRootEnergy (rK ε))
    (hseed : GlobalSource (rB ε) rTop (1/10)) :
    ∀ L ∈ Icc (rLow ε) rTop, GlobalSource (rB ε) L (rCap L) := by
  have htop : GlobalSource (rB ε) rTop (rCap rTop) := by
    simpa only [rCap, sub_self, mul_zero, add_zero] using hseed
  exact QRH.ArviSelectedLeaf.Native.curve_induction
    (fun L => GlobalSource (rB ε) L (rCap L))
    (by unfold rStep; positivity : 0 < rStep ε) htop
    (fun L₀ hL₀ L hL hlt hle hsrc => by
      have hg := refined_gates hε0 hε1 hL₀ hL hlt hle
      exact e5_step (p := rFace ε L₀) (n := rFace ε L) hg
        (refined_leaf hε0 hε1 hR1 hβ hL₀ hg) hβ hsrc)
theorem refined_end {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hR1 : SelectedRootEnergy (rK ε))
    (hseed : GlobalSource (rB ε) rTop (1/10)) :
    GlobalSource (1 - ε) (2 + 10 * ε) (rCap (2 + 10 * ε)) := by
  have h := refined_sources hε0 hε1 hβ hR1 hseed (rLow ε)
    ⟨le_rfl, by unfold rLow rTop; linarith only [hε1]⟩
  simpa only [rB, rLow] using h
end
end QRH.PositiveGapTightSelected
