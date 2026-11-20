/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine grouped source amplitude uses the original two independent
profiles. Its fixed height polynomial has no hidden dependence on labels. -/
import Candidate.C092.transport.RegularFrameHeightBudget
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedAt
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second
namespace QRH.Cycle092.PackedPrice
variable {L mesh U:ℝ} {θ:GData L}

theorem original_height (r:GSrc θ mesh U) (t₁ t₂ height:ℝ) (hheight:0 ≤ height)
    (hV:r.Vf ≤ height) (ht:r.t=t₁) (ht₁:r.t₁=t₁/(2*Real.pi))
    (ht₂:r.t₂=t₂/(2*Real.pi)) :
    r.height  ≤  2*(1+|t₁|+|t₂|+height) := by
  have hπ : 1  ≤  2*Real.pi := by linarith only [Real.pi_gt_three]
  have help (t:ℝ): |t/(2*Real.pi)|  ≤  |t| := by
    rw [abs_div,abs_of_nonneg (zero_le_one.trans hπ)];exact div_le_self (abs_nonneg t) hπ
  unfold GSrc.height
  rw [ht,ht₁,ht₂]
  linarith only [help t₁, help t₂, hheight,hV,abs_nonneg t₂]

theorem original_amplitude {p:Profiles (1/4) (9/4)} (η:Character)
    (r:GSrc θ mesh U) (J D:ℕ) (hD:J ≤ D) (S Smax:Finset (ℕ×ℕ)) (hS:S⊆Smax)
    (t₁ t₂ height:ℝ) (hheight:0 ≤ height) (hV:r.Vf ≤ height) (ht:r.t=t₁)
    (ht₁:r.t₁=t₁/(2*Real.pi)) (ht₂:r.t₂=t₂/(2*Real.pi))
    (hw₁:r.W₁=p.profile 0) (hw₂:r.W₂=p.profile 1) :
    gAmp L θ mesh η U r J S  ≤  (2:ℝ)^D*((p.control Smax)^2*(1+|t₁|+|t₂|+height)^D) := by
  have hc (i:Fin 2): sourceControl S (p.profile i)  ≤  sourceControl Smax (p.profile i) :=
    Seminorm.le_def.mp (Finset.sup_mono hS) _
  have hctl:=mul_le_mul (hc 0) (hc 1) (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hr:=original_height r t₁ t₂ height hheight hV ht ht₁ ht₂
  have hH:1 ≤ 1+|t₁|+|t₂|+height:=by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hdeg:r.height^J ≤ (2:ℝ)^D*(1+|t₁|+|t₂|+height)^D:=by
    have h:=pow_le_pow_left₀ (zero_le_one.trans r.one_le_height) hr D
    rw [mul_pow] at h;exact (pow_le_pow_right₀ r.one_le_height hD).trans h
  unfold gAmp
  rw [hw₁,hw₂]
  have h0:=mul_nonneg (sourceControl_nonneg S (p.profile 0)) (sourceControl_nonneg S (p.profile 1))
  exact (mul_le_mul (pow_le_pow_left₀ h0 hctl 2) hdeg (pow_nonneg (zero_le_one.trans r.one_le_height) _) (sq_nonneg _)).trans_eq
    (by unfold Profiles.control;ring)

theorem selected_amplitude {p:Profiles (1/4) (9/4)} (η:Character)
    (r:GSrc θ mesh U) (J D:ℕ) (hD:J ≤ D) (S Smax:Finset (ℕ×ℕ)) (hS:S⊆Smax)
    (t₁ t₂ height:ℝ) (hheight:0 ≤ height) (hV:r.Vf ≤ height) (ht:r.t=t₁)
    (ht₁:r.t₁=t₁/(2*Real.pi)) (ht₂:r.t₂=t₂/(2*Real.pi))
    (hw₁:r.W₁=p.profile 0) (hw₂:r.W₂=p.profile 1) (t:ℝ) :
    gAmp L θ mesh η U r J S*(1+‖t‖)^(2*J)  ≤ 
    (2:ℝ)^D*((p.control Smax)^2*(1+|t₁|+|t₂|+height)^D)*(1+‖t‖)^(2*D) := by
  apply mul_le_mul (original_amplitude η r J D hD S Smax hS t₁ t₂ height hheight hV ht ht₁ ht₂ hw₁ hw₂)
    (pow_le_pow_right₀ (by have:=norm_nonneg t;linarith) (by omega)) (by positivity)
  positivity

#print axioms original_amplitude
#print axioms selected_amplitude
end QRH.Cycle092.PackedPrice
