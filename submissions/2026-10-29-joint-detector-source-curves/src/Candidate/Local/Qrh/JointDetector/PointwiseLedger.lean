/- Copyright (c) 2026 Joseph Bebel. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The common LOW, geometry and reference proofs retain the generic source step.
The pointwise HIGH ledger uses the new flat/curved density gates. -/
import Candidate.Local.Qrh.JointDetector.AdaptiveLedger
import Candidate.Local.Qrh.JointDetector.PointwisePrice

/-! The pointwise retained-slope HIGH ledger. The running density changes
the slope itself. Its proof therefore uses separate flat and curved
density gates, rather than treating a rebate as a fixed constant.

The scalar lemmas below are parameterized by the actual retained-slope
function. They do not assert a packed supplier or a source theorem.
-/
namespace Qrh.JointDetector.PointwiseLedger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Hybrid
open QRH.SilDensitySplit.Density

def highJ (slope : ℝ → ℝ) (B L W σ ν : ℝ) : ℝ :=
  AdaptivePrice.k ν*(1-6*σ)-ν*(B-L*W)-slope ν*(W-σ)+σ

def highPrice (slope : ℝ → ℝ) (ν P s M : ℝ) : ℝ :=
  ν*P-AdaptivePrice.k ν*M+slope ν*s+
    (ν-slope ν)*max 0 (s-M/10)

theorem highJ_difference (slope : ℝ → ℝ) (B L W σ ν₁ ν₂ : ℝ)
    (h₁ : 15-6*ν₁ ≠ 0) (h₂ : 15-6*ν₂ ≠ 0) :
    highJ slope B L W σ ν₂-highJ slope B L W σ ν₁ =
      (ν₂-ν₁)*(150/((15-6*ν₁)*(15-6*ν₂))*(1-6*σ)-(B-L*W))-
        (slope ν₂-slope ν₁)*(W-σ) := by
  have hk : AdaptivePrice.k ν₂-AdaptivePrice.k ν₁ =
      (ν₂-ν₁)*(150/((15-6*ν₁)*(15-6*ν₂))) := by
    simpa [AdaptiveLedger.highJ] using
      AdaptiveLedger.highJ_difference 0 0 0 0 0 ν₁ ν₂ h₁ h₂
  unfold highJ
  linear_combination (1-6*σ)*hk

theorem density_slope_ge {floor ν₁ ν₂ : ℝ}
    (h₁ : ν₁ ∈ Set.Icc floor (3/4:ℝ)) (h₂ : ν₂ ∈ Set.Icc floor (3/4:ℝ)) :
    150/(15-6*floor)^2 ≤ 150/((15-6*ν₁)*(15-6*ν₂)) := by
  have hd₁ : 0 < 15-6*ν₁ := by linarith [h₁.2]
  have hd₂ : 0 < 15-6*ν₂ := by linarith [h₂.2]
  have hdf : 0 < 15-6*floor := by linarith [h₁.1,h₁.2]
  have ha : 15-6*ν₁ ≤ 15-6*floor := by linarith [h₁.1]
  have hb : 15-6*ν₂ ≤ 15-6*floor := by linarith [h₂.1]
  have hp : (15-6*ν₁)*(15-6*ν₂) ≤ (15-6*floor)^2 := by
    nlinarith [mul_le_mul ha hb hd₂.le hdf.le]
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hd₁ hd₂) hp

theorem flat_gate_mono {slope : ℝ → ℝ} {B L W σ ν₁ ν₂ : ℝ}
    (hν₁ : (1/2:ℝ) ≤ ν₁) (hν₂ : ν₂ ≤ 3/4) (hν : ν₁ ≤ ν₂)
    (hfactor : 0 ≤ 1-6*σ) (hflat : slope ν₂=slope ν₁)
    (hgate : 0 ≤ (25/24:ℝ)*(1-6*σ)-(B-L*W)) :
    highJ slope B L W σ ν₁ ≤ highJ slope B L W σ ν₂ := by
  have hd₁ : 0 < 15-6*ν₁ := by linarith
  have hd₂ : 0 < 15-6*ν₂ := by linarith
  have hk := density_slope_ge ⟨hν₁,hν.trans hν₂⟩ ⟨hν₁.trans hν,hν₂⟩
  have hk' : (25/24:ℝ) ≤ 150/((15-6*ν₁)*(15-6*ν₂)) := by
    convert hk using 1; norm_num
  have hcoef := mul_le_mul_of_nonneg_right hk' hfactor
  have hcoef' : 0 ≤ 150/((15-6*ν₁)*(15-6*ν₂))*(1-6*σ)-(B-L*W) := by
    linarith
  have hd := highJ_difference slope B L W σ ν₁ ν₂ hd₁.ne' hd₂.ne'
  rw [hflat, sub_self, zero_mul, sub_zero] at hd
  have hm := mul_nonneg (sub_nonneg.mpr hν) hcoef'
  linarith

theorem curved_gate_mono {slope : ℝ → ℝ} {B L W σ ν₁ ν₂ : ℝ}
    (hν₁ : (7/10:ℝ) ≤ ν₁) (hν₂ : ν₂ ≤ 3/4) (hν : ν₁ ≤ ν₂)
    (hfactor : 0 ≤ 1-6*σ) (hwidth : 0 ≤ W-σ)
    (hslope : slope ν₂-slope ν₁ ≤ 3*(ν₂-ν₁))
    (hgate : 0 ≤ (625/486:ℝ)*(1-6*σ)-(B-L*W)-3*(W-σ)) :
    highJ slope B L W σ ν₁ ≤ highJ slope B L W σ ν₂ := by
  have hd₁ : 0 < 15-6*ν₁ := by linarith
  have hd₂ : 0 < 15-6*ν₂ := by linarith
  have hk := density_slope_ge ⟨hν₁,hν.trans hν₂⟩ ⟨hν₁.trans hν,hν₂⟩
  have hk' : (625/486:ℝ) ≤ 150/((15-6*ν₁)*(15-6*ν₂)) := by
    convert hk using 1; norm_num
  have hcoef := mul_le_mul_of_nonneg_right hk' hfactor
  have hcoef' : 0 ≤ 150/((15-6*ν₁)*(15-6*ν₂))*(1-6*σ)-(B-L*W)-3*(W-σ) := by
    linarith
  have hs := mul_le_mul_of_nonneg_right hslope hwidth
  have hm := mul_nonneg (sub_nonneg.mpr hν) hcoef'
  have hd := highJ_difference slope B L W σ ν₁ ν₂ hd₁.ne' hd₂.ne'
  nlinarith

/-- The two polynomial gates control the full supremum interval even when
it crosses the retained-slope corner. No differentiation in q is used. -/
theorem highJ_mono_from_cut {slope : ℝ → ℝ} {B L W σ q ν : ℝ}
    (hq0 : (57/100:ℝ) ≤ q) (hq1 : q ≤ 7/10) (hν0 : q ≤ ν) (hν1 : ν ≤ 3/4)
    (hfactor : 0 ≤ 1-6*σ) (hwidth : 0 ≤ W-σ)
    (hflat : ∀ x ∈ Set.Icc q (7/10:ℝ), slope x=slope q)
    (hslope : ∀ x y, (7/10:ℝ) ≤ x → y ≤ 3/4 → x ≤ y →
      slope y-slope x ≤ 3*(y-x))
    (hgate0 : 0 ≤ (25/24:ℝ)*(1-6*σ)-(B-L*W))
    (hgate1 : 0 ≤ (625/486:ℝ)*(1-6*σ)-(B-L*W)-3*(W-σ)) :
    highJ slope B L W σ q ≤ highJ slope B L W σ ν := by
  by_cases hν : ν ≤ 7/10
  · exact flat_gate_mono (by linarith) hν1 hν0 hfactor
      (hflat ν ⟨hν0,hν⟩) hgate0
  · have hmiddle : highJ slope B L W σ q ≤ highJ slope B L W σ (7/10) :=
      flat_gate_mono (by linarith) (by norm_num) hq1 hfactor
        (hflat _ ⟨hq1,le_rfl⟩) hgate0
    exact hmiddle.trans (curved_gate_mono le_rfl hν1 (by linarith)
      hfactor hwidth (hslope _ _ le_rfl hν1 (by linarith)) hgate1)

theorem highPrice_physical {slope : ℝ → ℝ} {ν P s M : ℝ} (hs : s ≤ M/10) :
    highPrice slope ν P s M=ν*P-AdaptivePrice.k ν*M+slope ν*s := by
  unfold highPrice
  rw [max_eq_left (by linarith), mul_zero, add_zero]

/-- Exact overshoot accounting with a varying retained slope. The new
price is evaluated at the live running density throughout this identity. -/
theorem high_price_ledger {slope : ℝ → ℝ} {ν P s B L W u σ t tl : ℝ}
    (hν : 0 ≤ ν) (hk : 0 ≤ AdaptivePrice.k ν) (hκ : 0 ≤ slope ν)
    (hP : P ≤ B-L*W+tl) (hs : s ≤ W-u)
    (hcap : s ≤ (1+t-6*u)/10) (ht : -tl ≤ t) :
    highPrice slope ν P s (1+t-6*u)-u ≤
      -highJ slope B L W σ ν+(6*AdaptivePrice.k ν-slope ν-1)*(u-σ)+
        (ν+AdaptivePrice.k ν)*tl := by
  rw [highPrice_physical hcap]
  have hplain := mul_le_mul_of_nonneg_left hP hν
  have hslot := mul_le_mul_of_nonneg_left hs hκ
  have hfreq := mul_le_mul_of_nonneg_left ht hk
  unfold highJ
  nlinarith

theorem high_price_paid {slope : ℝ → ℝ} {ν P s B L W u σ t tl mesh rJ : ℝ}
    (hν : 0 ≤ ν) (hk : 0 ≤ AdaptivePrice.k ν) (hκ : 0 ≤ slope ν)
    (hc : 6*AdaptivePrice.k ν-slope ν-1 ≤ 6)
    (hf : ν+AdaptivePrice.k ν ≤ 2)
    (hP : P ≤ B-L*W+tl) (hs : s ≤ W-u)
    (hcap : s ≤ (1+t-6*u)/10) (ht : -tl ≤ t)
    (hu0 : σ ≤ u) (hu1 : u ≤ σ+mesh) (htl : 0 ≤ tl)
    (hJ : rJ ≤ highJ slope B L W σ ν) (hreserve : 6*mesh+2*tl ≤ rJ) :
    highPrice slope ν P s (1+t-6*u) ≤ u := by
  have h := high_price_ledger (σ:=σ) hν hk hκ hP hs hcap ht
  have ho := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hu0)
  have hm : 6*(u-σ) ≤ 6*mesh := by linarith
  have hfreq := mul_le_mul_of_nonneg_right hf htl
  linarith

theorem pointwise_highJ_mono_from_cut {B L W σ q ν : ℝ}
    (hq0 : PointwisePrice.q0 ≤ q) (hq1 : q ≤ 7/10) (hν0 : q ≤ ν) (hν1 : ν ≤ 3/4)
    (hfactor : 0 ≤ 1-6*σ) (hwidth : 0 ≤ W-σ)
    (hgate0 : 0 ≤ (25/24:ℝ)*(1-6*σ)-(B-L*W))
    (hgate1 : 0 ≤ (625/486:ℝ)*(1-6*σ)-(B-L*W)-3*(W-σ)) :
    highJ PointwisePrice.slope B L W σ q ≤ highJ PointwisePrice.slope B L W σ ν := by
  apply highJ_mono_from_cut hq0 hq1 hν0 hν1 hfactor hwidth
  · intro x hx
    rw [PointwisePrice.slope_flat ⟨hq0.trans hx.1,hx.2⟩,
      PointwisePrice.slope_flat ⟨hq0,hq1⟩]
  · intro x y hx hy hxy
    exact PointwisePrice.slope_sub_le ⟨by dsimp [PointwisePrice.q0]; linarith,hxy.trans hy⟩
      ⟨by dsimp [PointwisePrice.q0]; linarith,hy⟩ hxy
  · exact hgate0
  · exact hgate1

theorem highPrice_eq_g (ν P s M : ℝ) :
    highPrice PointwisePrice.slope ν P s M=PointwisePrice.g ν P s M := by
  simp only [highPrice,PointwisePrice.g,max_comm]
  rfl

theorem pointwise_high_price_paid {ν P s B L W u σ t tl mesh rJ : ℝ}
    (hν : ν ∈ Set.Icc PointwisePrice.q0 (3/4:ℝ))
    (hP : P ≤ B-L*W+tl) (hs : s ≤ W-u)
    (hcap : s ≤ (1+t-6*u)/10) (ht : -tl ≤ t)
    (hu0 : σ ≤ u) (hu1 : u ≤ σ+mesh) (htl : 0 ≤ tl)
    (hJ : rJ ≤ highJ PointwisePrice.slope B L W σ ν)
    (hreserve : 6*mesh+2*tl ≤ rJ) : PointwisePrice.g ν P s (1+t-6*u) ≤ u := by
  have hν0 : 0 ≤ ν := by dsimp [PointwisePrice.q0] at hν; linarith [hν.1]
  have hk := PointwisePrice.k_range hν
  have hκ := (PointwisePrice.slope_pos hν).le
  have hk0 : 0 ≤ AdaptivePrice.k ν := by change 0 ≤ PointwisePrice.k ν; linarith [hk.1]
  have hk1 : AdaptivePrice.k ν ≤ 5/7 := hk.2
  rw [← highPrice_eq_g]
  exact high_price_paid hν0 hk0 hκ (by linarith) (by linarith [hν.2])
    hP hs hcap ht hu0 hu1 htl hJ hreserve

abbrev densK := AdaptiveLedger.densK
abbrev dens := AdaptiveLedger.dens
abbrev dens_mul := AdaptiveLedger.dens_mul
abbrev lowDefect := AdaptiveLedger.lowDefect
abbrev lowDefect_eq := AdaptiveLedger.lowDefect_eq

def densQ (φ B₀ L₀ L A D s₀ w : ℝ) : ℝ :=
  max PointwisePrice.q0 (min (3/4) (dens φ B₀ L₀ L A D (max 0 (w-s₀))))

theorem densQ_mem (φ B₀ L₀ L A D s₀ w : ℝ) :
    densQ φ B₀ L₀ L A D s₀ w ∈ Set.Icc PointwisePrice.q0 (3/4:ℝ) :=
  ⟨le_max_left _ _,max_le (by norm_num [PointwisePrice.q0]) (min_le_left _ _)⟩

theorem densQ_eq {φ B₀ L₀ L A D s₀ w : ℝ}
    (hl : PointwisePrice.q0 ≤ dens φ B₀ L₀ L A D (max 0 (w-s₀)))
    (hu : dens φ B₀ L₀ L A D (max 0 (w-s₀)) ≤ 3/4) :
    densQ φ B₀ L₀ L A D s₀ w=dens φ B₀ L₀ L A D (max 0 (w-s₀)) := by
  unfold densQ
  rw [min_eq_right hu,max_eq_right hl]

def gQFloor (φ B₀ L₀ L A D v : ℝ) : ℝ := dens φ B₀ L₀ L A D v-PointwisePrice.q0
def gQUpper (φ B₀ L₀ L A D v : ℝ) : ℝ := 7/10-dens φ B₀ L₀ L A D v
def gHighAtQ (φ B₀ L₀ B L A D v : ℝ) : ℝ :=
  highJ PointwisePrice.slope B L (width B₀ L₀ B L v) (sel A D v) (dens φ B₀ L₀ L A D v)
def gHighFlat (B₀ L₀ B L A D v : ℝ) : ℝ :=
  (25/24:ℝ)*(1-6*sel A D v)-(B-L*width B₀ L₀ B L v)
def gHighCurved (B₀ L₀ B L A D v : ℝ) : ℝ :=
  (625/486:ℝ)*(1-6*sel A D v)-(B-L*width B₀ L₀ B L v)-
    3*(width B₀ L₀ B L v-sel A D v)

structure Gates (φ B₀ L₀ c₀ B L c A D : ℝ) : Prop where
  phi_mem : φ ∈ Set.Ioc (0:ℝ) 1
  width_pos : 0 < c-cross B₀ L₀ B L
  sel_den_pos : ∀ v, 0 ≤ v → v ≤ c-cross B₀ L₀ B L → 0 < 1+D*v
  dens_den_pos : ∀ v, 0 ≤ v → v ≤ c-cross B₀ L₀ B L → 0 < densE B₀ L₀ L A D v
  q_floor : UnifPos (gQFloor φ B₀ L₀ L A D) 0 (c-cross B₀ L₀ B L)
  q_upper : UnifPos (gQUpper φ B₀ L₀ L A D) 0 (c-cross B₀ L₀ B L)
  H_lower : UnifPos (gHLower A D) 0 (c-cross B₀ L₀ B L)
  retained_cap : UnifPos (gRetainedCap B₀ L₀ c₀ B L A D) 0 (c-cross B₀ L₀ B L)
  retained_width : UnifPos (gRetainedWidth B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  high_at_q : UnifPos (gHighAtQ φ B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  high_flat : UnifPos (gHighFlat B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  high_curved : UnifPos (gHighCurved B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  principal_reference : UnifPos (gPrincipal B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  second_reference : UnifPos (gSecondRef B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  second_diagonal : UnifPos (gSecondDiag B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  reference_upper_positive : UnifPos (gRefUpper B₀ L₀ B L A D) 0 (c-cross B₀ L₀ B L)
  selection_monotonicity : UnifPos (gSelDeriv A D) 0 (c-cross B₀ L₀ B L)

def stepData (φ B₀ L₀ c₀ B L c A D : ℝ) (hL : 0 < L₀) : StepData where
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
  price := PointwisePrice.jointPrice B₀ L₀ c₀ hL
    (densQ φ B₀ L₀ L A D (cross B₀ L₀ B L))
    (densQ_mem φ B₀ L₀ L A D (cross B₀ L₀ B L))

section
variable {φ B₀ L₀ c₀ B L c A D : ℝ}
namespace Gates

theorem dens_mem (h : Gates φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c-cross B₀ L₀ B L) :
    1/2 < dens φ B₀ L₀ L A D v ∧ dens φ B₀ L₀ L A D v < 3/4 := by
  have ha := h.q_floor.pos v h0 h1
  have hb := h.q_upper.pos v h0 h1
  unfold gQFloor PointwisePrice.q0 at ha
  unfold gQUpper at hb
  constructor <;> linarith

theorem dens_floor (h : Gates φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c-cross B₀ L₀ B L) :
    PointwisePrice.q0 < dens φ B₀ L₀ L A D v := by
  have ha := h.q_floor.pos v h0 h1
  exact sub_pos.mp ha

theorem dens_flat_upper (h : Gates φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c-cross B₀ L₀ B L) : dens φ B₀ L₀ L A D v < 7/10 := by
  have hb := h.q_upper.pos v h0 h1
  exact sub_pos.mp hb
theorem low_identity (h : Gates φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    lowDefect φ B₀ L₀ L A D v = (1-φ : ℝ) * L₀ * sel A D v :=
  lowDefect_eq φ B₀ L₀ L A D v (h.sel_den_pos v h0 h1).ne'
    (h.dens_den_pos v h0 h1).ne'
theorem dsA_pos (h : Gates φ B₀ L₀ c₀ B L c A D) : 0 < A := by
  have := h.selection_monotonicity.pos 0 le_rfl h.width_pos.le
  simpa [gSelDeriv] using this

theorem dsCross_lt_c₀ (h : Gates φ B₀ L₀ c₀ B L c A D) :
    cross B₀ L₀ B L < c₀ := by
  have := h.retained_cap.pos 0 le_rfl h.width_pos.le
  simp only [gRetainedCap, packed, width, sel_zero] at this
  linarith

theorem dsSel_nonneg (h : Gates φ B₀ L₀ c₀ B L c A D) {v : ℝ} (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B₀ L₀ B L) : 0 ≤ sel A D v :=
  div_nonneg (mul_nonneg h.dsA_pos.le h0) (h.sel_den_pos v h0 h1).le

theorem dsSel_mono (h : Gates φ B₀ L₀ c₀ B L c A D) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ c - cross B₀ L₀ B L) : sel A D a ≤ sel A D b := by
  have da := h.sel_den_pos a ha (hab.trans hb)
  have db := h.sel_den_pos b (ha.trans hab) hb
  unfold sel
  rw [div_le_div_iff₀ da db]
  nlinarith [mul_le_mul_of_nonneg_left hab h.dsA_pos.le]

/-- `q(v)·(6B₀-L₀) ≤ L₀`: the LOW overshoot coefficient is at most one. -/
theorem dsDens_overshoot (h : Gates φ B₀ L₀ c₀ B L c A D)
    (hF : DSFace B₀ L₀ c₀ B L c) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    dens φ B₀ L₀ L A D v * (6 * B₀ - L₀) ≤ L₀ := by
  have hE := h.dens_den_pos v h0 h1
  have hm := dens_mul φ B₀ L₀ L A D v hE.ne'
  unfold densE AdaptiveLedger.densK at hm
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


theorem high_mono (h : Gates φ B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c-cross B₀ L₀ B L)
    (ν : ℝ) (hν : dens φ B₀ L₀ L A D v ≤ ν) (hν' : ν ≤ 3/4) :
    gHighAtQ φ B₀ L₀ B L A D v ≤
      highJ PointwisePrice.slope B L (width B₀ L₀ B L v) (sel A D v) ν := by
  have hfactor := h.H_lower.pos v h0 h1
  simp only [gHLower,packed] at hfactor
  have hwidth := h.retained_width.pos v h0 h1
  simp only [gRetainedWidth] at hwidth
  have hflat := h.high_flat.pos v h0 h1
  have hcurved := h.high_curved.pos v h0 h1
  exact pointwise_highJ_mono_from_cut (h.dens_floor v h0 h1).le
    (h.dens_flat_upper v h0 h1).le hν hν' (by linarith) hwidth.le hflat.le hcurved.le

theorem high_reserve (h : Gates φ B₀ L₀ c₀ B L c A D) :
    ∃ r, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ c-cross B₀ L₀ B L →
      ∀ ν, dens φ B₀ L₀ L A D v ≤ ν → ν ≤ 3/4 →
        r ≤ highJ PointwisePrice.slope B L (width B₀ L₀ B L v) (sel A D v) ν := by
  obtain ⟨r,hr,hJ⟩ := h.high_at_q
  exact ⟨r,hr,fun v h0 h1 ν hν hν' =>
    (hJ v h0 h1).trans (h.high_mono v h0 h1 ν hν hν')⟩

end Gates

theorem ledger (h : Gates φ B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c)
    (hL : 0 < L₀) (hc₀ : c₀ ≤ 1/10) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × ℝ × ℝ, LedgerAt (stepData φ B₀ L₀ c₀ B L c A D hL) ε p.1 p.2.1 p.2.2 := by
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
  have hQ : densQ φ B₀ L₀ L A D (cross B₀ L₀ B L) g.w = dens φ B₀ L₀ L A D v := by
    have := densQ_eq (φ:=φ) (B₀ := B₀) (L₀ := L₀) (L := L) (A := A) (D := D)
      (s₀ := cross B₀ L₀ B L) (w := g.w) (by rw [← hv]; exact hqf.le) (by rw [← hv]; exact hq.2.le)
    rw [← hv] at this; exact this
  show max (lowPart B₀ L₀ c₀ (densQ φ B₀ L₀ L A D (cross B₀ L₀ B L) g.w) g.PC g.s g.H)
      (PointwisePrice.highSup (densQ φ B₀ L₀ L A D (cross B₀ L₀ B L) g.w) g.PC g.s g.H) ≤ g.u+ε/16
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
    have hqd := AdaptiveLedger.low_aux hq0 hq.2.le hF.B₀_lt hL.le hσ0 hu0 hdef hC0 hq6 htl ht4
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
    refine PointwisePrice.highSup_le hq.2.le fun ν hν1 hν2 => ?_
    have hJ := hJr v hv0 hv1 ν hν1 hν2
    simp only [width] at hJ
    have hn : ν ∈ Set.Icc PointwisePrice.q0 (3/4:ℝ) :=
      ⟨(h.dens_floor v hv0 hv1).le.trans hν1,hν2⟩
    have hh : PointwisePrice.g ν g.PC g.s g.H ≤ g.u := by
      rw [hH] at hcap ⊢
      exact pointwise_high_price_paid hn hP hslot hcap ht.1 hu0 hu1 htl hJ (by linarith)
    linarith

theorem reference (h : Gates φ B₀ L₀ c₀ B L c A D) (hL : 0 < L₀) :
    ∃ ρ, ReferenceAt (stepData φ B₀ L₀ c₀ B L c A D hL) ρ := by
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
theorem stepGates (h : Gates φ B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c)
    (hL : 0 < L₀) (hc₀ : c₀ ≤ 1/10) : StepGates (stepData φ B₀ L₀ c₀ B L c A D hL) where
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

/-- Cleared source gates; the flat HIGH identity uses the admitted density
interval before replacing the actual retained slope by a*. -/
theorem dens_floor_mul (floor φ B₀ L₀ L A D v : ℝ)
    (hE : densE B₀ L₀ L A D v ≠ 0) :
    (dens φ B₀ L₀ L A D v-floor)*densE B₀ L₀ L A D v=
      densK φ L₀ A-floor*densE B₀ L₀ L A D v := by
  linear_combination dens_mul φ B₀ L₀ L A D v hE

theorem gQFloor_mul (φ B₀ L₀ L A D v : ℝ) (hE : densE B₀ L₀ L A D v ≠ 0) :
    gQFloor φ B₀ L₀ L A D v*densE B₀ L₀ L A D v=
      densK φ L₀ A-PointwisePrice.q0*densE B₀ L₀ L A D v :=
  dens_floor_mul _ _ _ _ _ _ _ _ hE

theorem gQUpper_mul (φ B₀ L₀ L A D v : ℝ) (hE : densE B₀ L₀ L A D v ≠ 0) :
    gQUpper φ B₀ L₀ L A D v*densE B₀ L₀ L A D v=
      (7/10)*densE B₀ L₀ L A D v-densK φ L₀ A := by
  unfold gQUpper
  linear_combination -dens_mul φ B₀ L₀ L A D v hE

def highNumerator (B L W Av T E N F : ℝ) : ℝ :=
  10*N*E*(T-6*Av)-N*T*F*(B-L*W)-
    PointwisePrice.amplitudeFloor*(W*T-Av)*E*F+Av*E*F

theorem highJ_flat_cleared {B L W σ q Av T E N F : ℝ}
    (hflat : PointwisePrice.slope q=PointwisePrice.amplitudeFloor)
    (hE : E ≠ 0) (hF : F ≠ 0) (hσ : σ*T=Av) (hq : q*E=N)
    (hFE : F=15*E-6*N) :
    highJ PointwisePrice.slope B L W σ q*(T*E*F)=highNumerator B L W Av T E N F := by
  have hFD : F=(15-6*q)*E := by linear_combination hFE+6*hq
  have hden : 15-6*q ≠ 0 := by
    intro hd
    rw [hd,zero_mul] at hFD
    exact hF hFD
  have hkF : AdaptivePrice.k q*F=10*N := by
    rw [hFD,← mul_assoc]
    have hk : AdaptivePrice.k q*(15-6*q)=10*q := div_mul_cancel₀ _ hden
    rw [hk]
    linear_combination 10*hq
  unfold highJ highNumerator
  rw [hflat]
  linear_combination E*(T-6*Av)*hkF-T*F*(B-L*W)*hq+
    ((PointwisePrice.amplitudeFloor+1)*E*F-6*AdaptivePrice.k q*E*F)*hσ

theorem gHighAtQ_mul (φ B₀ L₀ B L A D v : ℝ)
    (hT : 1+D*v ≠ 0) (hE : densE B₀ L₀ L A D v ≠ 0)
    (hF : 15*densE B₀ L₀ L A D v-6*densK φ L₀ A ≠ 0)
    (hq : dens φ B₀ L₀ L A D v ∈ Set.Icc PointwisePrice.q0 (7/10:ℝ)) :
    gHighAtQ φ B₀ L₀ B L A D v*((1+D*v)*densE B₀ L₀ L A D v*
      (15*densE B₀ L₀ L A D v-6*densK φ L₀ A))=
      highNumerator B L (width B₀ L₀ B L v) (A*v) (1+D*v)
        (densE B₀ L₀ L A D v) (densK φ L₀ A)
        (15*densE B₀ L₀ L A D v-6*densK φ L₀ A) :=
  highJ_flat_cleared (PointwisePrice.slope_flat hq) hE hF
    (sel_mul A D v hT) (dens_mul φ B₀ L₀ L A D v hE) rfl

theorem gHighFlat_mul (B₀ L₀ B L A D v : ℝ) (hT : 1+D*v ≠ 0) :
    gHighFlat B₀ L₀ B L A D v*(1+D*v)=
      (25/24:ℝ)*((1+D*v)-6*A*v)-(B-L*width B₀ L₀ B L v)*(1+D*v) := by
  unfold gHighFlat
  linear_combination -(25/4:ℝ)*sel_mul A D v hT

theorem gHighCurved_mul (B₀ L₀ B L A D v : ℝ) (hT : 1+D*v ≠ 0) :
    gHighCurved B₀ L₀ B L A D v*(1+D*v)=
      (625/486:ℝ)*((1+D*v)-6*A*v)-(B-L*width B₀ L₀ B L v)*(1+D*v)-
        3*(width B₀ L₀ B L v*(1+D*v)-A*v) := by
  unfold gHighCurved
  linear_combination (-(625/81:ℝ)+3)*sel_mul A D v hT

end
end Qrh.JointDetector.PointwiseLedger

#print axioms Qrh.JointDetector.PointwiseLedger.highJ_mono_from_cut
#print axioms Qrh.JointDetector.PointwiseLedger.high_price_paid
#print axioms Qrh.JointDetector.PointwiseLedger.pointwise_highJ_mono_from_cut
#print axioms Qrh.JointDetector.PointwiseLedger.pointwise_high_price_paid
#print axioms Qrh.JointDetector.PointwiseLedger.stepGates
#print axioms Qrh.JointDetector.PointwiseLedger.gHighAtQ_mul
