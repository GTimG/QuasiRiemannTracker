/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Restore both independent physical pitches before integrating the native
second Fourier variable. Reanchoring a mark does not duplicate that variable. -/
import Candidate.C092.transport.FixedRegularPrice
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree.Packet.Grouped
namespace QRH.Cycle092.PackedPrice
variable {L mesh U:ℝ} {θ:GData L}

def shiftedPitch (t v:ℝ) := 2*Real.pi*(t+v/(2*Real.pi))

theorem shiftedPitch_eq (t v:ℝ) : shiftedPitch t v=2*Real.pi*t+v := by
  unfold shiftedPitch
  field_simp [ne_of_gt Real.pi_pos]
  <;> ring

theorem shifted_slot (r:GSrc θ mesh U) (t v:ℝ) (i:Fin θ.N) :
    r.t+v+r.freq i-shiftedPitch t v=r.t+r.freq i-2*Real.pi*t := by rw [shiftedPitch_eq];ring

def frameHeightConstant : ℝ := 8+4*Real.pi

theorem frame_height (r:GSrc θ mesh U) (v:ℝ) :
    1+|r.t+v|+2*|shiftedPitch r.t₁ v|+2*|shiftedPitch r.t₂ v|+r.Vf ≤
      frameHeightConstant*r.height*(1+‖v‖) := by
  simp only [shiftedPitch_eq]
  have h1:=abs_add_le r.t v
  have h2:=abs_add_le (2*Real.pi*r.t₁) v
  have h3:=abs_add_le (2*Real.pi*r.t₂) v
  have hp:0 ≤ 2*Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  rw [abs_mul,abs_of_nonneg hp] at h2 h3
  have hh:=r.one_le_height
  have hH:0 ≤ frameHeightConstant*r.height:=mul_nonneg (by unfold frameHeightConstant;positivity) (zero_le_one.trans hh)
  have hv:0 ≤ |v|:=abs_nonneg _
  have hC:5 ≤ frameHeightConstant*r.height :=
    (by unfold frameHeightConstant;linarith [Real.pi_pos] : 5 ≤ frameHeightConstant).trans
      (le_mul_of_one_le_right (by unfold frameHeightConstant;positivity) hh)
  have hmain:1+|r.t|+r.Vf+4*Real.pi*(|r.t₁|+|r.t₂|) ≤ frameHeightConstant*r.height := by
    unfold GSrc.height frameHeightConstant
    nlinarith only [abs_nonneg r.t,abs_nonneg r.t₁,abs_nonneg r.t₂,r.hVf,Real.pi_pos,
      mul_nonneg Real.pi_pos.le (abs_nonneg r.t),mul_nonneg Real.pi_pos.le r.hVf]
  rw [Real.norm_eq_abs];linarith only [h1,h2,h3,hmain,mul_le_mul_of_nonneg_right hC hv,le_rfl (a:=|v|)]

theorem frame_height_power (r:GSrc θ mesh U) (v:ℝ) (D:ℕ) :
    (1+|r.t+v|+2*|shiftedPitch r.t₁ v|+2*|shiftedPitch r.t₂ v|+r.Vf)^D ≤
      (frameHeightConstant^D*r.height^D)*(1+‖v‖)^(2*D) := by
  have hn : 0≤1+|r.t+v|+2*|shiftedPitch r.t₁ v|+2*|shiftedPitch r.t₂ v|+r.Vf := by
    have:=r.hVf;positivity
  have h:=pow_le_pow_left₀ hn (frame_height r v) D
  rw [mul_pow,mul_pow] at h
  have hc:0≤frameHeightConstant:=by unfold frameHeightConstant;positivity
  have hr:=zero_le_one.trans r.one_le_height
  exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by have:=norm_nonneg v;linarith) (by omega)) (by positivity))

/-- A genuinely exhausted source has no marked quota to pay.
The first parameter is its actual selected width. -/
def exhausted : QRH.SilDensitySplit.CubeFree.Price where
  f:=fun u' _ _ M=>(5/6)*max 0 (1-6*u'-M)
  nonneg:=by intros;positivity
  mono:=by intros;rfl
  lip:=5/6
  lip_nonneg:=by norm_num
  lipP:=by intros;linarith
  lipS:=by intros;linarith
  lipM:=by
    intro u' p s M e
    have h : max 0 (1-6*u'-(M+e)) ≤ max 0 (1-6*u'-M)+|e| := by
      apply max_le <;> linarith [le_max_left 0 (1-6*u'-M),le_max_right 0 (1-6*u'-M),abs_nonneg e,neg_abs_le e]
    linarith
theorem exhausted_leaf (u' p s M:ℝ) : exhausted.f u' p s M-(5/6)*max 0 (1-6*u'-M)=0 := by
  unfold exhausted;dsimp;ring

#print axioms frame_height_power
#print axioms exhausted_leaf
end QRH.Cycle092.PackedPrice
