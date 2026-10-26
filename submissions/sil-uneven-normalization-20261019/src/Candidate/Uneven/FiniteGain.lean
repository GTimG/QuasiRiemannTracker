/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.JointMarkedGain

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Sil.Uneven.FiniteGain

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The minimum of any nonempty finite family of affine gain forms. -/
def gain (a b : ι → ℝ) (S D : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => a i*S+b i*D)

theorem gain_le (a b : ι → ℝ) (S D : ℝ) (i : ι) :
    gain a b S D ≤ a i*S+b i*D :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem gain_lower {a b : ι → ℝ} {S D t : ℝ}
    (h : ∀i,t ≤ a i*S+b i*D) : t ≤ gain a b S D :=
  Finset.le_inf' _ _ (fun i _ => h i)

theorem gain_attained (a b : ι → ℝ) (S D : ℝ) :
    ∃i,gain a b S D=a i*S+b i*D := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => a i*S+b i*D)
  exact ⟨i,hi⟩

theorem gain_nonneg {a b : ι → ℝ} {S D : ℝ}
    (ha : ∀i,0 ≤ a i) (hb : ∀i,0 ≤ b i) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    0 ≤ gain a b S D :=
  gain_lower (fun i => add_nonneg (mul_nonneg (ha i) hS) (mul_nonneg (hb i) hD))

theorem gain_mono {a b : ι → ℝ} {S S' D D' : ℝ}
    (ha : ∀i,0 ≤ a i) (hb : ∀i,0 ≤ b i) (hS : S ≤ S') (hD : D ≤ D') :
    gain a b S D ≤ gain a b S' D' := by
  apply gain_lower
  intro i
  exact (gain_le a b S D i).trans (add_le_add
    (mul_le_mul_of_nonneg_left hS (ha i)) (mul_le_mul_of_nonneg_left hD (hb i)))

theorem gain_homogeneous {a b : ι → ℝ} {S D q : ℝ} (hq : 0 ≤ q) :
    gain a b (q*S) (q*D)=q*gain a b S D := by
  apply le_antisymm
  · obtain ⟨i,hi⟩ := gain_attained a b S D
    rw [hi]
    convert gain_le a b (q*S) (q*D) i using 1 <;> ring
  · apply gain_lower
    intro i
    have h := mul_le_mul_of_nonneg_left (gain_le a b S D i) hq
    convert h using 1 <;> ring

theorem gain_rescale {a b : ι → ℝ} {S D : ℝ} (hD : 0 < D) :
    D*gain a b (S/D) 1=gain a b S D := by
  rw [←gain_homogeneous hD.le, mul_div_cancel₀ S hD.ne',mul_one]

/-- Only the minimum needs a cap; individual scale coefficients may exceed it. -/
theorem root_gain_lower {a b : ι → ℝ} {S D q pad cap : ℝ}
    (ha : ∀i,0 ≤ a i) (hb : ∀i,0 ≤ b i)
    (hS : 0 ≤ S) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hpad : 0 ≤ pad)
    (hcap : gain a b S D ≤ cap*D) :
    gain a b S D-cap*D*(1-q) ≤ gain a b S (D*q+pad) := by
  have hscaled : q*gain a b S D ≤ gain a b S (D*q+pad) := by
    apply gain_lower
    intro i
    have h := mul_le_mul_of_nonneg_left (gain_le a b S D i) hq0
    have hs := mul_nonneg (mul_nonneg (ha i) hS) (sub_nonneg.mpr hq1)
    have hp := mul_nonneg (hb i) hpad
    nlinarith only [h,hs,hp]
  have hc := mul_le_mul_of_nonneg_right hcap (sub_nonneg.mpr hq1)
  nlinarith only [hscaled,hc]


theorem width_transport {a b : ι → ℝ} {gamma R L Q S F : ℝ}
    (ha : ∀i,0 ≤ a i) (hb : ∀i,0 ≤ b i) (hg : 0 ≤ gamma)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hS : 0 ≤ S) (hF : 2*S ≤ F) (hlive : S ≤ R+L) (hfreq : F ≤ 2*R+Q) :
    min (gamma*S) (gain a b S F) ≤ gamma*R+gain a b L Q := by
  have hh : min (gamma*S) (gain a b S F)-gamma*R ≤ gain a b L Q := by
    apply gain_lower
    intro i
    have hm := min_le_min_left (gamma*S) (gain_le a b S F i)
    have hp := PR63Adaptation.one_form_width_transport
      (ha i) (hb i) hg hR hL hQ hS hF hlive hfreq
    linarith only [hm,hp]
  linarith only [hh]

theorem channel_payment {a b : ι → ℝ} {gamma R L Q S F base fee : ℝ}
    (ha : ∀i,0 ≤ a i) (hb : ∀i,0 ≤ b i) (hg : 0 ≤ gamma)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hS : 0 ≤ S) (hF : 2*S ≤ F) (hlive : S ≤ R+L) (hfreq : F ≤ 2*R+Q)
    (hremoved : fee ≤ base+gamma*S)
    (hfaces : ∀i,fee ≤ base+a i*S+b i*F) :
    fee ≤ base+gamma*R+gain a b L Q := by
  have hgain : fee-base ≤ gain a b S F := gain_lower (by intro i; linarith [hfaces i])
  have hh := width_transport ha hb hg hR hL hQ hS hF hlive hfreq
  have hl : fee-base ≤ min (gamma*S) (gain a b S F) := le_min (by linarith) hgain
  linarith only [hl,hh]

end Sil.Uneven.FiniteGain
