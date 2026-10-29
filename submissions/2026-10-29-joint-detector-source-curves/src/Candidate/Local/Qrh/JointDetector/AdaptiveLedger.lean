/- Copyright (c) 2026 Joseph Bebel. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The LOW and reference adapters retain Sil's generic step proof. -/
import Candidate.Local.Qrh.JointDetector.AdaptivePrice
import Submissions.sil_density_split_20261026.Density.StepGates

namespace Qrh.JointDetector.AdaptiveLedger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Hybrid
open QRH.SilDensitySplit.Density
open AdaptivePrice (Policy)

def densK (φ L₀ A : ℝ) : ℝ := φ*L₀*A
def dens (φ B₀ L₀ L A D v : ℝ) : ℝ := densK φ L₀ A / densE B₀ L₀ L A D v

theorem dens_mul (φ B₀ L₀ L A D v : ℝ) (hE : densE B₀ L₀ L A D v ≠ 0) :
    dens φ B₀ L₀ L A D v*densE B₀ L₀ L A D v=densK φ L₀ A := div_mul_cancel₀ _ hE

def densQ (policy : Policy) (φ B₀ L₀ L A D s₀ w : ℝ) : ℝ :=
  max policy.floor (min (3/4) (dens φ B₀ L₀ L A D (max 0 (w-s₀))))
theorem densQ_mem (policy : Policy) (φ B₀ L₀ L A D s₀ w : ℝ) :
    densQ policy φ B₀ L₀ L A D s₀ w ∈ Set.Icc policy.floor (3/4) :=
  ⟨le_max_left _ _, max_le policy.floor_mem.2 (min_le_left _ _)⟩
theorem densQ_eq {policy : Policy} {φ B₀ L₀ L A D s₀ w : ℝ}
    (hl : policy.floor ≤ dens φ B₀ L₀ L A D (max 0 (w-s₀)))
    (hu : dens φ B₀ L₀ L A D (max 0 (w-s₀)) ≤ 3/4) :
    densQ policy φ B₀ L₀ L A D s₀ w=dens φ B₀ L₀ L A D (max 0 (w-s₀)) := by
  unfold densQ
  rw [min_eq_right hu,max_eq_right hl]

def lowDefect (φ B₀ L₀ L A D v : ℝ) : ℝ := L₀*sel A D v-
  dens φ B₀ L₀ L A D v*((L₀-L)*v+(6*B₀-L₀)*sel A D v)
theorem lowDefect_eq (φ B₀ L₀ L A D v : ℝ)
    (hx : 1+D*v ≠ 0) (hE : densE B₀ L₀ L A D v ≠ 0) :
    lowDefect φ B₀ L₀ L A D v=(1-φ)*L₀*sel A D v := by
  have hs := sel_mul A D v hx
  have hq : dens φ B₀ L₀ L A D v*((L₀-L)*(1+D*v)+(6*B₀-L₀)*A)=φ*L₀*A :=
    dens_mul φ B₀ L₀ L A D v hE
  apply mul_right_cancel₀ hx
  unfold lowDefect
  linear_combination (φ*L₀-dens φ B₀ L₀ L A D v*(6*B₀-L₀))*hs-v*hq

def gQFloor (policy : Policy) (φ B₀ L₀ L A D v : ℝ) : ℝ :=
  dens φ B₀ L₀ L A D v-policy.floor
def gQUpper (φ B₀ L₀ L A D v : ℝ) : ℝ := 3/4-dens φ B₀ L₀ L A D v
def gLowPerWidth (φ L₀ A D v : ℝ) : ℝ := (1-φ)*L₀*A/(1+D*v)
def derivLo (floor : ℝ) : ℝ := 150/(15-6*floor)^2

def highJ (rebate B L W σ ν : ℝ) : ℝ := AdaptivePrice.k ν-ν*B+
  (ν*L-AdaptivePrice.k ν+rebate)*W-(5*AdaptivePrice.k ν-1+rebate)*σ

def gHighAtQ (policy : Policy) (φ B₀ L₀ B L A D v : ℝ) : ℝ :=
  let q := dens φ B₀ L₀ L A D v
  highJ (policy.gain q) B L (width B₀ L₀ B L v) (sel A D v) q

def gHighFactor (B₀ L₀ B L A D v : ℝ) : ℝ := 1-width B₀ L₀ B L v-5*sel A D v

def gHighDeriv (policy : Policy) (B₀ L₀ B L A D v : ℝ) : ℝ :=
  derivLo policy.floor*gHighFactor B₀ L₀ B L A D v-(B-L*width B₀ L₀ B L v)

structure Gates (policy : Policy) (φ B₀ L₀ c₀ B L c A D : ℝ) : Prop where
  phi_mem : φ ∈ Set.Ioc (0:ℝ) 1
  width_pos : 0 < c-cross B₀ L₀ B L
  sel_den_pos : ∀ v, 0 ≤ v → v ≤ c-cross B₀ L₀ B L → 0 < 1+D*v
  dens_den_pos : ∀ v, 0 ≤ v → v ≤ c-cross B₀ L₀ B L → 0 < densE B₀ L₀ L A D v
  q_floor : UnifPos (gQFloor policy φ B₀ L₀ L A D) 0 (c-cross B₀ L₀ B L)
  q_upper : UnifPos (gQUpper φ B₀ L₀ L A D) 0 (c-cross B₀ L₀ B L)
  H_lower : UnifPos (gHLower A D) 0 (c-cross B₀ L₀ B L)
  retained_cap : UnifPos (gRetainedCap B₀ L₀ c₀ B L A D) 0 (c-cross B₀ L₀ B L)
  retained_width : UnifPos (gRetainedWidth B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  high_at_q : UnifPos (gHighAtQ policy φ B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  high_density_derivative : UnifPos (gHighDeriv policy B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  high_derivative_factor : UnifPos (gHighFactor B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  principal_reference : UnifPos (gPrincipal B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  second_reference : UnifPos (gSecondRef B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  second_diagonal : UnifPos (gSecondDiag B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  reference_upper_positive : UnifPos (gRefUpper B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  selection_monotonicity : UnifPos (gSelDeriv A D) 0 (c-cross B₀ L₀ B L)

def stepData (policy : Policy) (φ B₀ L₀ c₀ B L c A D : ℝ) (hL : 0 < L₀) : StepData where
  B₀ := B₀
  L₀ := L₀
  c₀ := c₀
  B := B
  L := L
  c := c
  κ := 3/4
  s₀ := cross B₀ L₀ B L
  Hmin := 9/10
  Hmax := 3
  sel := fun _ w => dsSel A D (cross B₀ L₀ B L) w
  price := AdaptivePrice.jointPrice policy B₀ L₀ c₀ hL
    (densQ policy φ B₀ L₀ L A D (cross B₀ L₀ B L))
    (densQ_mem policy φ B₀ L₀ L A D (cross B₀ L₀ B L))

theorem highJ_affine (rebate B L W σ ν : ℝ) :
    highJ rebate B L W σ ν = AdaptivePrice.k ν * (1 - W - 5*σ) -
      ν * (B - L*W) + (rebate : ℝ)*W + (1-rebate : ℝ)*σ := by
  unfold highJ
  ring

theorem highJ_difference (rebate B L W σ ν₁ ν₂ : ℝ)
    (h₁ : 15 - 6*ν₁ ≠ 0) (h₂ : 15 - 6*ν₂ ≠ 0) :
    highJ rebate B L W σ ν₂ - highJ rebate B L W σ ν₁ =
      (ν₂-ν₁) * (150 / ((15-6*ν₁)*(15-6*ν₂)) * (1-W-5*σ) - (B-L*W)) := by
  have hk : AdaptivePrice.k ν₂ - AdaptivePrice.k ν₁ =
      (ν₂-ν₁) * (150 / ((15-6*ν₁)*(15-6*ν₂))) := by
    simpa only [one_sub_rhoOf, AdaptivePrice.k] using
      one_sub_rhoOf_sub ν₁ ν₂ h₁ h₂
  rw [highJ_affine, highJ_affine]
  linear_combination (1-W-5*σ)*hk

/-- The refined density range gives the sharper inherited slope constant. -/
theorem density_slope_ge {floor ν₁ ν₂ : ℝ}
    (hf : floor ∈ Set.Icc (29/50:ℝ) (3/4))
    (h₁ : ν₁ ∈ Set.Icc floor (3/4)) (h₂ : ν₂ ∈ Set.Icc floor (3/4)) :
    derivLo floor ≤ 150/((15-6*ν₁)*(15-6*ν₂)) := by
  have hd₁ := AdaptivePrice.k_den_pos ⟨hf.1.trans h₁.1,h₁.2⟩
  have hd₂ := AdaptivePrice.k_den_pos ⟨hf.1.trans h₂.1,h₂.2⟩
  have hdf := AdaptivePrice.k_den_pos hf
  have ha : 15-6*ν₁ ≤ 15-6*floor := by linarith [h₁.1]
  have hb : 15-6*ν₂ ≤ 15-6*floor := by linarith [h₂.1]
  have hp : (15-6*ν₁)*(15-6*ν₂) ≤ (15-6*floor)^2 := by
    nlinarith [mul_le_mul ha hb hd₂.le hdf.le]
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hd₁ hd₂) hp

theorem highJ_mono_quant {floor rebate B L W σ ν₁ ν₂ : ℝ}
    (hf : floor ∈ Set.Icc (29/50:ℝ) (3/4))
    (h₁ : ν₁ ∈ Set.Icc floor (3/4)) (h₂ : ν₂ ∈ Set.Icc floor (3/4))
    (hν : ν₁ ≤ ν₂) (hfactor : 0 ≤ 1-W-5*σ) :
    highJ rebate B L W σ ν₁+(ν₂-ν₁)*(derivLo floor*(1-W-5*σ)-(B-L*W)) ≤
      highJ rebate B L W σ ν₂ := by
  have hi := highJ_difference rebate B L W σ ν₁ ν₂
    (AdaptivePrice.k_den_pos ⟨hf.1.trans h₁.1,h₁.2⟩).ne'
    (AdaptivePrice.k_den_pos ⟨hf.1.trans h₂.1,h₂.2⟩).ne'
  have hk := mul_le_mul_of_nonneg_right (density_slope_ge hf h₁ h₂) hfactor
  have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right hk (B-L*W)) (sub_nonneg.mpr hν)
  linarith

/-- Genuine derivative formula, independent of the constant price subtraction. -/
theorem highJ_hasDerivAt (rebate B L W σ ν : ℝ) (hν : 15-6*ν ≠ 0) :
    HasDerivAt (fun x => highJ rebate B L W σ x)
      (150/(15-6*ν)^2*(1-W-5*σ)-(B-L*W)) ν := by
  have h1 : HasDerivAt (fun x : ℝ => 10*x) 10 ν :=
    ((hasDerivAt_id' ν).const_mul (10:ℝ)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => 15-6*x) (-6) ν :=
    (((hasDerivAt_id' ν).const_mul (6:ℝ)).const_sub (15:ℝ)).congr_deriv (by ring)
  have hk : HasDerivAt AdaptivePrice.k (150/(15-6*ν)^2) ν := by
    exact (h1.div h2 hν).congr_deriv (by congr 1; ring)
  have hf := ((hk.mul_const (1-W-5*σ)).sub
    ((hasDerivAt_id' ν).mul_const (B-L*W))).add_const
      ((rebate : ℝ)*W+(1-rebate : ℝ)*σ)
  convert hf using 1
  · ext x
    rw [highJ_affine]
    simp only [Pi.sub_apply]
    ring
  · ring

/-- The closed derivative gate bounds the actual derivative everywhere. -/
theorem highJ_deriv_ge {floor B L W σ ν : ℝ}
    (hf : floor ∈ Set.Icc (29/50:ℝ) (3/4))
    (hν : ν ∈ Set.Icc floor (3/4)) (hfactor : 0 ≤ 1-W-5*σ) :
    derivLo floor*(1-W-5*σ)-(B-L*W) ≤ 150/(15-6*ν)^2*(1-W-5*σ)-(B-L*W) := by
  have h := mul_le_mul_of_nonneg_right (density_slope_ge hf hν hν) hfactor
  simpa only [pow_two] using sub_le_sub_right h (B-L*W)

/-- Exact HIGH payment before bounding the upward greedy error. -/
theorem high_price_ledger {rebate ν P s B L W u σ t tl : ℝ}
    (hc : rebate ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (hP : P ≤ B-L*W+tl) (hs : s ≤ W-u)
    (hcap : s ≤ (1+t-6*u)/10) (ht : -tl ≤ t) :
    AdaptivePrice.gWith rebate ν P s (1+t-6*u)-u ≤ -highJ rebate B L W σ ν +
      (5*AdaptivePrice.k ν-1+rebate)*(u-σ)+(ν+AdaptivePrice.k ν)*tl := by
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hk : 0 ≤ AdaptivePrice.k ν := by linarith [(AdaptivePrice.k_range hν).1]
  have hp := mul_le_mul_of_nonneg_left hP hn
  have hslot := mul_le_mul_of_nonneg_left hs (AdaptivePrice.retainedSlope_pos hc hν).le
  have htpaid := mul_nonneg hk (show 0 ≤ t+tl by linarith)
  rw [AdaptivePrice.gWith, max_eq_right (by linarith : s-(1+t-6*u)/10 ≤ 0)]
  unfold AdaptivePrice.retainedSlope at hslot
  unfold AdaptivePrice.retainedSlope highJ
  nlinarith

theorem overshoot_coefficients {rebate ν : ℝ}
    (hc : rebate ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4)) :
    (0 ≤ 5*AdaptivePrice.k ν-1+rebate ∧ 5*AdaptivePrice.k ν-1+rebate ≤ 6) ∧
      (0 ≤ ν+AdaptivePrice.k ν ∧ ν+AdaptivePrice.k ν ≤ 2) := by
  have hk := AdaptivePrice.k_range hν
  constructor <;> constructor <;> linarith [hν.1, hν.2, hc.1, hc.2]

theorem high_price_paid {rebate ν P s B L W u σ t tl mesh rJ : ℝ}
    (hc : rebate ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (hP : P ≤ B-L*W+tl) (hs : s ≤ W-u)
    (hcap : s ≤ (1+t-6*u)/10) (ht : -tl ≤ t)
    (hu0 : σ ≤ u) (hu1 : u ≤ σ+mesh) (htl : 0 ≤ tl)
    (hJ : rJ ≤ highJ rebate B L W σ ν) (hreserve : 6*mesh+2*tl ≤ rJ) :
    AdaptivePrice.gWith rebate ν P s (1+t-6*u) ≤ u := by
  have h := high_price_ledger (σ := σ) hc hν hP hs hcap ht
  have hc := overshoot_coefficients hc hν
  have ho := mul_le_mul_of_nonneg_right hc.1.2 (sub_nonneg.mpr hu0)
  have hm : 6*(u-σ) ≤ 6*mesh := by linarith
  have hp := mul_le_mul_of_nonneg_right hc.2.2 htl
  linarith



/-- LOW uses a nonnegative residual, allowing φ=1 and retaining the actual
upward greedy overshoot. There is no strict residual claim at v=0. -/
theorem low_aux {q L₀ L B₀ v σ u ε tl F : ℝ} (hq0 : 0 ≤ q) (hq34 : q ≤ 3/4)
    (hB₁ : B₀ < 1) (_hL₀ : 0 ≤ L₀) (_hσ0 : 0 ≤ σ) (hu0 : σ ≤ u)
    (hdef : F ≤ (L₀-L)*v+(6*B₀-L₀)*u+(B₀*tl+tl))
    (hC : 0 ≤ L₀*σ-q*((L₀-L)*v+(6*B₀-L₀)*σ))
    (hq6 : q*(6*B₀-L₀) ≤ L₀) (htl : 0 ≤ tl) (ht4 : tl ≤ L₀*ε/24) :
    q*F ≤ L₀*(u+ε/16) := by
  have e1 := mul_le_mul_of_nonneg_left hdef hq0
  have e2 : q*(6*B₀-L₀)*(u-σ) ≤ L₀*(u-σ) :=
    mul_le_mul_of_nonneg_right hq6 (sub_nonneg.mpr hu0)
  have e5 : q*B₀ ≤ 3/4 :=
    (mul_le_mul_of_nonneg_left hB₁.le hq0).trans (by linarith)
  have e3 := mul_le_mul_of_nonneg_right e5 htl
  have e4 := mul_le_mul_of_nonneg_right hq34 htl
  linarith

section
variable {policy : Policy} {φ : ℝ}
variable {B₀ L₀ c₀ B L c A D : ℝ}
namespace Gates

theorem dens_mem (h : Gates policy φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    1/2 < dens φ B₀ L₀ L A D v ∧ dens φ B₀ L₀ L A D v < 3/4 := by
  have ha := h.q_floor.pos v h0 h1
  have hb := h.q_upper.pos v h0 h1
  unfold gQFloor at ha
  have hfloor := policy.floor_mem.1
  unfold gQUpper at hb
  constructor <;> linarith

theorem dens_floor (h : Gates policy φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    policy.floor < dens φ B₀ L₀ L A D v := by
  have ha := h.q_floor.pos v h0 h1
  unfold gQFloor at ha
  have hfloor := policy.floor_mem.1
  linarith

theorem low_identity (h : Gates policy φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    lowDefect φ B₀ L₀ L A D v = (1-φ : ℝ) * L₀ * sel A D v :=
  lowDefect_eq φ B₀ L₀ L A D v (h.sel_den_pos v h0 h1).ne'
    (h.dens_den_pos v h0 h1).ne'
theorem dsA_pos (h : Gates policy φ B₀ L₀ c₀ B L c A D) : 0 < A := by
  have := h.selection_monotonicity.pos 0 le_rfl h.width_pos.le
  simpa [gSelDeriv] using this

theorem dsCross_lt_c₀ (h : Gates policy φ B₀ L₀ c₀ B L c A D) :
    cross B₀ L₀ B L < c₀ := by
  have := h.retained_cap.pos 0 le_rfl h.width_pos.le
  simp only [gRetainedCap, packed, width, sel_zero] at this
  linarith

theorem dsSel_nonneg (h : Gates policy φ B₀ L₀ c₀ B L c A D) {v : ℝ} (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B₀ L₀ B L) : 0 ≤ sel A D v :=
  div_nonneg (mul_nonneg h.dsA_pos.le h0) (h.sel_den_pos v h0 h1).le

theorem dsSel_mono (h : Gates policy φ B₀ L₀ c₀ B L c A D) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ c - cross B₀ L₀ B L) : sel A D a ≤ sel A D b := by
  have da := h.sel_den_pos a ha (hab.trans hb)
  have db := h.sel_den_pos b (ha.trans hab) hb
  unfold sel
  rw [div_le_div_iff₀ da db]
  nlinarith [mul_le_mul_of_nonneg_left hab h.dsA_pos.le]

/-- `q(v)·(6B₀-L₀) ≤ L₀`: the LOW overshoot coefficient is at most one. -/
theorem dsDens_overshoot (h : Gates policy φ B₀ L₀ c₀ B L c A D)
    (hF : DSFace B₀ L₀ c₀ B L c) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    dens φ B₀ L₀ L A D v * (6 * B₀ - L₀) ≤ L₀ := by
  have hE := h.dens_den_pos v h0 h1
  have hm := dens_mul φ B₀ L₀ L A D v hE.ne'
  unfold densE densK at hm
  have hA := h.dsA_pos
  have hx := h.sel_den_pos v h0 h1
  have hq := (h.dens_mem v h0 h1).1
  have hLL : 0 < L₀ - L := sub_pos.2 hF.L_lt
  have hL₀ : 0 < L₀ := by linarith [hF.one_lt_L]
  have hp : 0 < dens φ B₀ L₀ L A D v * ((L₀ - L) * (1 + D * v)) :=
    mul_pos (by linarith) (mul_pos hLL hx)
  have hφ : φ ≤ 1 := h.phi_mem.2
  have key : (dens φ B₀ L₀ L A D v * (6 * B₀ - L₀) - L₀) * A ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hφ) (mul_pos hL₀ hA).le]
  by_contra hc
  have hc : L₀ < dens φ B₀ L₀ L A D v * (6 * B₀ - L₀) := lt_of_not_ge hc
  have := mul_pos (sub_pos.2 hc) hA
  linarith


theorem high_mono (h : Gates policy φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c-cross B₀ L₀ B L)
    (ν : ℝ) (hν : dens φ B₀ L₀ L A D v ≤ ν) (hν' : ν ≤ 3/4) :
    gHighAtQ policy φ B₀ L₀ B L A D v ≤
      highJ (policy.gain (dens φ B₀ L₀ L A D v)) B L (width B₀ L₀ B L v) (sel A D v) ν := by
  have hq : dens φ B₀ L₀ L A D v ∈ Set.Icc policy.floor (3/4) :=
    ⟨(h.dens_floor v h0 h1).le, (h.dens_mem v h0 h1).2.le⟩
  have hn : ν ∈ Set.Icc policy.floor (3/4) := ⟨hq.1.trans hν, hν'⟩
  have hf := h.high_derivative_factor.pos v h0 h1
  have hd := h.high_density_derivative.pos v h0 h1
  have hm := highJ_mono_quant (rebate:=policy.gain (dens φ B₀ L₀ L A D v)) (B := B) (L := L) policy.floor_mem hq hn hν (by exact hf.le)
  have hprod := mul_nonneg (sub_nonneg.mpr hν) hd.le
  change gHighAtQ policy φ B₀ L₀ B L A D v ≤ _
  unfold gHighAtQ
  dsimp [gHighDeriv, gHighFactor] at hprod
  linarith

theorem high_reserve (h : Gates policy φ B₀ L₀ c₀ B L c A D) :
    ∃ r, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ c-cross B₀ L₀ B L →
      ∀ ν, dens φ B₀ L₀ L A D v ≤ ν → ν ≤ 3/4 →
        r ≤ highJ (policy.gain (dens φ B₀ L₀ L A D v)) B L (width B₀ L₀ B L v) (sel A D v) ν := by
  obtain ⟨r, hr, hJ⟩ := h.high_at_q
  exact ⟨r, hr, fun v h0 h1 ν hν hν' =>
    (hJ v h0 h1).trans (h.high_mono v h0 h1 ν hν hν')⟩

end Gates

theorem ledger (h : Gates policy φ B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c)
    (hL : 0 < L₀) (hc₀ : c₀ ≤ 1/10) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × ℝ × ℝ, LedgerAt (stepData policy φ B₀ L₀ c₀ B L c A D hL) ε p.1 p.2.1 p.2.2 := by
  obtain ⟨rH, hrH, hHr⟩ := h.H_lower
  obtain ⟨rC, hrC, hCr⟩ := h.retained_cap
  obtain ⟨rJ, hrJ, hJr⟩ := h.high_reserve
  obtain ⟨m, hm⟩ : ∃ m, m = min rJ rH := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ lt_min hrJ hrH
  have hmJ : m ≤ rJ := hm ▸ min_le_left _ _
  have hmH : m ≤ rH := hm ▸ min_le_right _ _
  refine ⟨(ε/16, m/12, min (m/4) (min rC (min 1 (min (L₀*ε/24) (ε/32))))), by positivity, ?_,
    by positivity, lt_min (by positivity) (lt_min hrC (lt_min one_pos
      (lt_min (by positivity) (by positivity)))), ?_⟩
  · show ε/16 ≤ ε/(16*(3/4))
    apply div_le_div_of_nonneg_left hε.le (by norm_num) (by norm_num)
  intro mesh hmesh hmeshL tl htl htlL g hfloor
  simp only at hmeshL htlL hfloor
  have ht1 : tl ≤ m/4 := htlL.trans (min_le_left _ _)
  have ht2 : tl ≤ rC := htlL.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : tl ≤ 1 :=
    htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht4 : tl ≤ L₀*ε/24 := htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have ht5 : tl ≤ ε/32 := htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  -- the side geometry
  have hS := g.hS
  have hf := g.hf
  have hPC := g.hPC
  have hroot := g.hroot
  have hsel := g.hsel
  have hs := g.hs
  have ht := g.ht
  simp only [stepData] at hS hroot hsel
  have hw : g.w = g.S - g.f := rfl
  have hH : g.H = 1 + g.t - 6*g.u := rfl
  -- scalar facts
  have hLL : 0 < L₀ - L := sub_pos.2 hF.L_lt
  have hL1 := hF.one_lt_L
  have hs0 := hF.cross_nonneg
  have hcross := hF.cross_mul
  have hcs := h.width_pos
  have hc0 := h.dsCross_lt_c₀
  have hc06 := hF.c₀_lt
  -- the excess
  obtain ⟨v, hv⟩ : ∃ v, v = max 0 (g.w - cross B₀ L₀ B L) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := hv ▸ le_max_left _ _
  have hv1 : v ≤ c - cross B₀ L₀ B L := hv ▸ max_le hcs.le (by rw [hw]; linarith)
  have hvS : v ≤ g.S - cross B₀ L₀ B L := hv ▸ max_le (by linarith) (by rw [hw]; linarith)
  have hwv : g.S - g.f - cross B₀ L₀ B L ≤ v := hv ▸ le_max_right _ _
  have hu0 : sel A D v ≤ g.u := by rw [hv]; exact hsel.1
  have hu1 : g.u ≤ sel A D v + mesh := by rw [hv]; exact hsel.2
  have hσ0 := h.dsSel_nonneg hv0 hv1
  have hq := h.dens_mem v hv0 hv1
  have hqf := h.dens_floor v hv0 hv1
  have hq6 := h.dsDens_overshoot hF hv0 hv1
  have hB₀ : 0 ≤ B₀ := by
    have hSf : ε/16 ≤ g.S := by rw [hw] at hfloor; linarith
    have : 1*(ε/16) ≤ L * g.S := mul_le_mul hL1.le hSf (by positivity) (by linarith)
    linarith [hF.B_le]
  have hP : g.PC ≤ B-L*(cross B₀ L₀ B L+v)+tl := by
    have hLS := mul_le_mul_of_nonneg_left
      (show cross B₀ L₀ B L+v ≤ g.S by linarith) (show 0 ≤ L by linarith)
    linarith
  have hslot : g.s ≤ (cross B₀ L₀ B L+v)-g.u := by linarith
  have hHL : (9/10 : ℝ) ≤ g.H := by
    have hh := hHr v hv0 hv1
    simp only [gHLower, packed] at hh
    rw [hH]
    linarith
  have hHU : g.H ≤ 3 := by rw [hH]; linarith
  have hcapParent : g.s-c₀*g.H ≤ 0 := by
    have hr := hCr v hv0 hv1
    simp only [gRetainedCap, packed, width] at hr
    rw [hH]
    exact ds_cap_aux hc06 (by linarith) hs.2 hwv hu0 ht.1 htl ht2 hr
  have hcap : g.s ≤ g.H/10 := by
    have hh := mul_le_mul_of_nonneg_right hc₀ (show 0 ≤ g.H by linarith)
    linarith
  refine ⟨hHL, hHU, ?_⟩
  -- the price at the side
  have hQ : densQ policy φ B₀ L₀ L A D (cross B₀ L₀ B L) g.w = dens φ B₀ L₀ L A D v := by
    have := densQ_eq (policy:=policy) (φ:=φ) (B₀ := B₀) (L₀ := L₀) (L := L) (A := A) (D := D)
      (s₀ := cross B₀ L₀ B L) (w := g.w) (by rw [← hv]; exact hqf.le) (by rw [← hv]; exact hq.2.le)
    rw [← hv] at this; exact this
  show max (lowPart B₀ L₀ c₀ (densQ policy φ B₀ L₀ L A D (cross B₀ L₀ B L) g.w) g.PC g.s g.H)
      (AdaptivePrice.supWith (policy.gain (densQ policy φ B₀ L₀ L A D (cross B₀ L₀ B L) g.w))
      (densQ policy φ B₀ L₀ L A D (cross B₀ L₀ B L) g.w) g.PC g.s g.H) ≤ g.u + ε/16
  rw [hQ]
  refine max_le ?_ ?_
  · -- LOW: identity (C) and the defect bound
    have hcap : g.s - c₀ * g.H ≤ 0 := by
      have hr := hCr v hv0 hv1
      simp only [gRetainedCap, packed, width] at hr
      rw [hH]
      exact ds_cap_aux hc06 (by linarith) hs.2 hwv hu0 ht.1 htl ht2 hr
    have hdef : g.PC + L₀ * g.s - B₀ * g.H ≤
        (L₀ - L) * v + (6*B₀ - L₀) * g.u + (B₀ * tl + tl) := by
      rw [hH]
      exact ds_defect_aux hL.le hL1.le hLL.le hB₀ hcross hf.1 hf.2 hroot hs.2 hwv ht.1
    have hC := h.low_identity v hv0 hv1
    have hC0 : 0 ≤ L₀*sel A D v-dens φ B₀ L₀ L A D v*
        ((L₀-L)*v+(6*B₀-L₀)*sel A D v) := by
      change 0 ≤ lowDefect φ B₀ L₀ L A D v
      rw [hC]
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr h.phi_mem.2) hL.le) hσ0
    have hq0 : 0 ≤ dens φ B₀ L₀ L A D v := by linarith
    have hqd := low_aux hq0 hq.2.le hF.B₀_lt hL.le hσ0 hu0 hdef hC0 hq6 htl ht4
    have hneed := deletionNeed_le_defect (B₀ := B₀) (L₀ := L₀) (P := g.PC) hcap
    unfold lowPart
    calc dens φ B₀ L₀ L A D v * deletionNeed B₀ L₀ c₀ g.PC g.s g.H
        ≤ dens φ B₀ L₀ L A D v * max 0 ((g.PC + L₀ * g.s - B₀ * g.H) / L₀) :=
          mul_le_mul_of_nonneg_left hneed hq0
      _ = max 0 (dens φ B₀ L₀ L A D v * (g.PC + L₀ * g.s - B₀ * g.H) / L₀) := by
          rw [mul_max_of_nonneg _ _ hq0, mul_zero, mul_div_assoc]
      _ ≤ g.u + ε/16 := by
          refine max_le (by linarith) ?_
          rw [div_le_iff₀ hL]; linarith
  · -- HIGH: the modified price and every retained-slot branch are paid.
    refine AdaptivePrice.supWith_le hq.2.le fun ν hν1 hν2 => ?_
    have hJ := hJr v hv0 hv1 ν hν1 hν2
    simp only [width] at hJ
    have hn : ν ∈ Set.Icc (29/50:ℝ) (3/4) :=
      ⟨policy.floor_mem.1.trans ((h.dens_floor v hv0 hv1).le.trans hν1), hν2⟩
    have hc := policy.gain_mem (dens φ B₀ L₀ L A D v)
      ⟨(h.dens_floor v hv0 hv1).le,hq.2.le⟩
    have hh : AdaptivePrice.gWith (policy.gain (dens φ B₀ L₀ L A D v)) ν g.PC g.s g.H ≤ g.u := by
      rw [hH] at hcap ⊢
      exact high_price_paid hc hn hP hslot hcap ht.1 hu0 hu1 htl hJ (by linarith)
    linarith

theorem reference (h : Gates policy φ B₀ L₀ c₀ B L c A D) (hL : 0 < L₀) :
    ∃ ρ, ReferenceAt (stepData policy φ B₀ L₀ c₀ B L c A D hL) ρ := by
  obtain ⟨r1, h1, hr1⟩ := h.principal_reference
  obtain ⟨r2, h2, hr2⟩ := h.second_reference
  obtain ⟨r3, h3, hr3⟩ := h.second_diagonal
  obtain ⟨r4, h4, hr4⟩ := h.reference_upper_positive
  refine ⟨min (min r1 r2) (min r3 r4), lt_min (lt_min h1 h2) (lt_min h3 h4), ?_⟩
  intro ε _ S hS0 hSc
  simp only [stepData, dsSel] at hS0 hSc ⊢
  have hv0 : 0 ≤ S - cross B₀ L₀ B L := by linarith
  have hv1 : S - cross B₀ L₀ B L ≤ c - cross B₀ L₀ B L := by linarith
  rw [max_eq_right hv0]
  have hwS : width B₀ L₀ B L (S - cross B₀ L₀ B L) = S := by unfold width; ring
  have g1 := hr1 _ hv0 hv1
  have g2 := hr2 _ hv0 hv1
  have g3 := hr3 _ hv0 hv1
  have g4 := hr4 _ hv0 hv1
  simp only [gPrincipal, gSecondRef, gSecondDiag, gRefUpper, hwS] at g1 g2 g3 g4
  have m1 : min (min r1 r2) (min r3 r4) ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
  have m2 : min (min r1 r2) (min r3 r4) ≤ r2 := (min_le_left _ _).trans (min_le_right _ _)
  have m3 : min (min r1 r2) (min r3 r4) ≤ r3 := (min_le_right _ _).trans (min_le_left _ _)
  have m4 : min (min r1 r2) (min r3 r4) ≤ r4 := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The certified hybrid gates (with the face facts) imply the generic step gates. -/
theorem stepGates (h : Gates policy φ B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c)
    (hL : 0 < L₀) (hc₀ : c₀ ≤ 1/10) : StepGates (stepData policy φ B₀ L₀ c₀ B L c A D hL) where
  face := by
    have := hF.cross_nonneg; have := h.width_pos
    exact ⟨hF.B_le, hF.B₀_lt, hF.L_lt, hF.one_lt_L, by show 0 < c; linarith, hF.c_lt,
      hF.c₀_lt⟩
  kappa := rfl
  crossing := ⟨hF.cross_nonneg, le_of_eq hF.cross_mul, fun _ => h.dsCross_lt_c₀.le⟩
  envelope := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [stepData] <;> norm_num
  sel_spec := by
    intro ε _
    have hs0 := hF.cross_nonneg
    have hcs := h.width_pos
    simp only [stepData, dsSel]
    refine ⟨fun x hx y hy hxy => ?_, fun w hw0 hwc => ?_⟩
    · exact h.dsSel_mono (le_max_left _ _) (max_le_max le_rfl (by linarith))
        (max_le hcs.le (by linarith [hy.2]))
    · have hv0 : (0:ℝ) ≤ max 0 (w - cross B₀ L₀ B L) := le_max_left _ _
      have hv1 : max 0 (w - cross B₀ L₀ B L) ≤ c - cross B₀ L₀ B L :=
        max_le hcs.le (by linarith)
      refine ⟨h.dsSel_nonneg hv0 hv1, ?_⟩
      rcases le_total w (cross B₀ L₀ B L) with hle | hle
      · rw [max_eq_left (by linarith), sel_zero]; exact hw0
      · rw [max_eq_right (by linarith)] at hv1 ⊢
        have := h.retained_width.pos _ (by linarith) hv1
        simp only [gRetainedWidth, width] at this
        linarith
  ledger := fun ε hε => ledger h hF hL hc₀ hε
  reference := reference h hL


end
def highNumerator (rebate B L W Av T E N F : ℝ) : ℝ :=
  10*N*T*E - N*B*T*F +
    (N*L*F-10*N*E+(rebate : ℝ)*E*F)*T*W -
      Av*E*(50*N-(1-rebate : ℝ)*F)

theorem highJ_cleared {rebate B L W σ q Av T E N F : ℝ}
    (hσ : σ*T = Av) (hq : q*E = N) (hk : AdaptivePrice.k q*F = 10*N) :
    highJ rebate B L W σ q*(T*E*F) = highNumerator rebate B L W Av T E N F := by
  calc
    _ = (AdaptivePrice.k q*F)*(1-W-5*σ)*T*E +
        (q*E)*(-B+L*W)*T*F+(rebate : ℝ)*W*T*E*F+
          (1-rebate : ℝ)*σ*T*E*F := by rw [highJ_affine]; ring
    _ = 10*N*(1-W-5*σ)*T*E +
        N*(-B+L*W)*T*F+(rebate : ℝ)*W*T*E*F+
          (1-rebate : ℝ)*σ*T*E*F := by rw [hk, hq]
    _ = _ := by
      unfold highNumerator
      linear_combination E*(-50*N+(1-rebate : ℝ)*F)*hσ

/-- The modified HIGH gate's exact cleared form. The three nonzero
requirements are supplied by the positive denominator certificates. -/
theorem gHighAtQ_mul (policy : Policy) (φ B₀ L₀ B L A D v : ℝ)
    (hx : 1+D*v ≠ 0) (hE : densE B₀ L₀ L A D v ≠ 0)
    (hF : 15*densE B₀ L₀ L A D v-6*densK φ L₀ A ≠ 0) :
    let T := 1+D*v
    let E := densE B₀ L₀ L A D v
    let N := densK φ L₀ A
    let F := 15*E-6*N
    gHighAtQ policy φ B₀ L₀ B L A D v*(T*E*F) =
      highNumerator (policy.gain (dens φ B₀ L₀ L A D v)) B L (width B₀ L₀ B L v) (A*v) T E N F := by
  dsimp only
  have hs := sel_mul A D v hx
  have hq := dens_mul φ B₀ L₀ L A D v hE
  let q := dens φ B₀ L₀ L A D v
  let E := densE B₀ L₀ L A D v
  let N := densK φ L₀ A
  let F := 15*E-6*N
  have hFE : F = E*(15-6*q) := by dsimp [F, E, N, q]; nlinarith
  have hqd : 15-6*q ≠ 0 := by
    intro hz
    have hzero : F = 0 := by rw [hFE, hz, mul_zero]
    exact hF hzero
  have hkq : AdaptivePrice.k q*(15-6*q) = 10*q := by
    unfold AdaptivePrice.k
    exact div_mul_cancel₀ _ hqd
  have hk : AdaptivePrice.k q*F = 10*N := by
    calc
      _ = (AdaptivePrice.k q*(15-6*q))*E := by rw [hFE]; ring
      _ = _ := by rw [hkq]; dsimp [q, E, N]; nlinarith
  exact highJ_cleared (rebate:=policy.gain q) hs hq hk

/-- The positive derivative factor has the saved quadratic numerator. -/
theorem gHighFactor_mul (B₀ L₀ B L A D v : ℝ) (hx : 1+D*v ≠ 0) :
    gHighFactor B₀ L₀ B L A D v*(1+D*v) =
      (1-width B₀ L₀ B L v)*(1+D*v)-5*A*v := by
  have hs := sel_mul A D v hx
  unfold gHighFactor
  linear_combination (-5:ℝ)*hs

/-- The derivative gate uses exactly the same density slope as its ledger. -/
theorem gHighDeriv_mul (policy : Policy) (B₀ L₀ B L A D v : ℝ) (hx : 1+D*v ≠ 0) :
    gHighDeriv policy B₀ L₀ B L A D v*(1+D*v) =
      (derivLo policy.floor)*((1-width B₀ L₀ B L v)*(1+D*v)-5*A*v) -
        (B-L*width B₀ L₀ B L v)*(1+D*v) := by
  have hf := gHighFactor_mul B₀ L₀ B L A D v hx
  unfold gHighDeriv
  linear_combination (derivLo policy.floor)*hf



/-- The adaptive gain is on its ramp exactly under this scalar guard. -/
def gRamp (φ B₀ L₀ L A D v : ℝ) : ℝ :=
  9/100-(AdaptivePrice.k (dens φ B₀ L₀ L A D v)-AdaptivePrice.amplitudeFloor)

def rampNumerator (B L W Av T E N F : ℝ) : ℝ :=
  10*N*T*E-N*B*T*F+
    (N*L*F-AdaptivePrice.amplitudeFloor*E*F)*T*W-
    Av*E*(60*N-(1+AdaptivePrice.amplitudeFloor)*F)

theorem highNumerator_ramp {rebate B L W Av T E N F : ℝ}
    (hr : rebate*F=10*N-AdaptivePrice.amplitudeFloor*F) :
    highNumerator rebate B L W Av T E N F = rampNumerator B L W Av T E N F := by
  unfold highNumerator rampNumerator
  linear_combination E*(T*W-Av)*hr

theorem gQFloor_mul (policy : Policy) (φ B₀ L₀ L A D v : ℝ)
    (hE : densE B₀ L₀ L A D v ≠ 0) :
    gQFloor policy φ B₀ L₀ L A D v*densE B₀ L₀ L A D v=
      densK φ L₀ A-policy.floor*densE B₀ L₀ L A D v := by
  have hm := dens_mul φ B₀ L₀ L A D v hE
  unfold gQFloor
  linear_combination hm

theorem gQUpper_mul (φ B₀ L₀ L A D v : ℝ) (hE : densE B₀ L₀ L A D v ≠ 0) :
    gQUpper φ B₀ L₀ L A D v*densE B₀ L₀ L A D v=
      (3/4)*densE B₀ L₀ L A D v-densK φ L₀ A := by
  have hm := dens_mul φ B₀ L₀ L A D v hE
  unfold gQUpper
  linear_combination -hm

theorem gLowPerWidth_mul (φ L₀ A D v : ℝ) (hx : 1+D*v ≠ 0) :
    gLowPerWidth φ L₀ A D v*(1+D*v)=(1-φ)*L₀*A := div_mul_cancel₀ _ hx

theorem gRamp_mul (φ B₀ L₀ L A D v : ℝ) (hE : densE B₀ L₀ L A D v ≠ 0)
    (hF : 15*densE B₀ L₀ L A D v-6*densK φ L₀ A ≠ 0) :
    gRamp φ B₀ L₀ L A D v*(15*densE B₀ L₀ L A D v-6*densK φ L₀ A)=
      (9/100+AdaptivePrice.amplitudeFloor)*(15*densE B₀ L₀ L A D v-6*densK φ L₀ A)-
        10*densK φ L₀ A := by
  have hq := dens_mul φ B₀ L₀ L A D v hE
  have hFE : 15*densE B₀ L₀ L A D v-6*densK φ L₀ A=
      densE B₀ L₀ L A D v*(15-6*dens φ B₀ L₀ L A D v) := by nlinarith
  have hd : 15-6*dens φ B₀ L₀ L A D v ≠ 0 := by
    intro hh
    exact hF (by rw [hFE,hh,mul_zero])
  have hk : AdaptivePrice.k (dens φ B₀ L₀ L A D v)*
      (15*densE B₀ L₀ L A D v-6*densK φ L₀ A)=10*densK φ L₀ A := by
    rw [hFE]
    have hh : AdaptivePrice.k (dens φ B₀ L₀ L A D v)*
        (15-6*dens φ B₀ L₀ L A D v)=10*dens φ B₀ L₀ L A D v := div_mul_cancel₀ _ hd
    calc
      _ = (AdaptivePrice.k (dens φ B₀ L₀ L A D v)*(15-6*dens φ B₀ L₀ L A D v))*
          densE B₀ L₀ L A D v := by ring
      _ = _ := by rw [hh]; nlinarith [hq]
  unfold gRamp
  linear_combination -hk

theorem derivLo_58 : derivLo (29/50)=15625/13824 := by norm_num [derivLo]
theorem derivLo_60 : derivLo (3/5)=1250/1083 := by norm_num [derivLo]
theorem derivLo_65 : derivLo (13/20)=5000/4107 := by norm_num [derivLo]


/-- The HIGH denominator is positive on the certified density range. -/
theorem high_den_pos (φ B₀ L₀ L A D v : ℝ) (hE : 0 < densE B₀ L₀ L A D v)
    (hq : dens φ B₀ L₀ L A D v ≤ 3/4) :
    0 < 15*densE B₀ L₀ L A D v-6*densK φ L₀ A := by
  have hm := dens_mul φ B₀ L₀ L A D v hE.ne'
  have hp := mul_le_mul_of_nonneg_right hq hE.le
  nlinarith

theorem highJ_at_ramp (B L W σ q : ℝ) :
    highJ (AdaptivePrice.k q-AdaptivePrice.amplitudeFloor) B L W σ q =
      AdaptivePrice.k q*(1-6*σ)-q*(B-L*W)-AdaptivePrice.amplitudeFloor*(W-σ)+σ := by
  unfold highJ
  ring

/-- The exact ramp polynomial used in the adaptive count-chain certificates.
The ramp condition selects a branch algebraically; q is not differentiated. -/
theorem gHighAtQ_adaptive_ramp_mul (floor : ℝ)
    (hf : floor ∈ Set.Icc (29/50:ℝ) (3/4)) (φ B₀ L₀ B L A D v : ℝ)
    (hx : 1+D*v ≠ 0) (hE : densE B₀ L₀ L A D v ≠ 0)
    (hF : 15*densE B₀ L₀ L A D v-6*densK φ L₀ A ≠ 0)
    (hr : 0 ≤ gRamp φ B₀ L₀ L A D v) :
    let T := 1+D*v
    let E := densE B₀ L₀ L A D v
    let N := densK φ L₀ A
    let F := 15*E-6*N
    gHighAtQ (AdaptivePrice.adaptivePolicy floor hf) φ B₀ L₀ B L A D v*(T*E*F)=
      rampNumerator B L (width B₀ L₀ B L v) (A*v) T E N F := by
  dsimp only
  have hg := gHighAtQ_mul (AdaptivePrice.adaptivePolicy floor hf) φ B₀ L₀ B L A D v hx hE hF
  dsimp only at hg
  have hc : (AdaptivePrice.adaptivePolicy floor hf).gain (dens φ B₀ L₀ L A D v)=
      AdaptivePrice.k (dens φ B₀ L₀ L A D v)-AdaptivePrice.amplitudeFloor := by
    change min _ _ = _
    apply min_eq_right
    unfold gRamp at hr
    linarith
  rw [hc] at hg
  have hk := gRamp_mul φ B₀ L₀ L A D v hE hF
  unfold gRamp at hk
  have he : (AdaptivePrice.k (dens φ B₀ L₀ L A D v)-AdaptivePrice.amplitudeFloor)*
      (15*densE B₀ L₀ L A D v-6*densK φ L₀ A)=
        10*densK φ L₀ A-AdaptivePrice.amplitudeFloor*(15*densE B₀ L₀ L A D v-6*densK φ L₀ A) := by
    linear_combination -hk
  exact hg.trans (highNumerator_ramp he)

end
end Qrh.JointDetector.AdaptiveLedger

#print axioms Qrh.JointDetector.AdaptiveLedger.stepGates
#print axioms Qrh.JointDetector.AdaptiveLedger.lowDefect_eq
#print axioms Qrh.JointDetector.AdaptiveLedger.highJ_hasDerivAt
#print axioms Qrh.JointDetector.AdaptiveLedger.gHighAtQ_adaptive_ramp_mul
