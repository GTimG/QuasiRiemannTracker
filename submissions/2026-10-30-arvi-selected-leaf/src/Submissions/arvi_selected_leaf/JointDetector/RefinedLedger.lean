/- Copyright (c) 2026 Joseph Bebel. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from the admitted Density/StepGates.lean: the LOW, selection and
reference proofs retain their original structure; the refined HIGH ledger
and modified gate interface are proved here. -/
import Submissions.arvi_selected_leaf.JointDetector.RefinedPrice
import Submissions.sil_density_split_20261026.Density.StepGates

/-!
# Refined HIGH source-step ledger

The 17/200 price is inserted into the actual generic StepData/StepGates
interface. All scalar gates are explicit inputs on the full closed excess
interval. No analytic PricedPackedSource theorem is asserted here.
-/
namespace Qrh.JointDetector.RefinedLedger
noncomputable section
set_option autoImplicit false
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Hybrid
open QRH.SilDensitySplit.Density

/-- Modified HIGH ledger functional. -/
def highJ (B L W σ ν : ℝ) : ℝ :=
  RefinedPrice.k ν - ν * B + (ν * L - RefinedPrice.k ν + 17/200) * W -
    (5 * RefinedPrice.k ν - 1 + 17/200) * σ

def gHighAtQ (B₀ L₀ B L A D v : ℝ) : ℝ :=
  highJ B L (width B₀ L₀ B L v) (sel A D v) (dens B₀ L₀ L A D v)

def gHighFactor (B₀ L₀ B L A D v : ℝ) : ℝ :=
  1 - width B₀ L₀ B L v - 5 * sel A D v

def gHighDeriv (B₀ L₀ B L A D v : ℝ) : ℝ :=
  (5000/4107 : ℝ) * gHighFactor B₀ L₀ B L A D v -
    (B - L * width B₀ L₀ B L v)

/-- Exactly the closed scalar gates required for the refined transition.
The original two HIGH gates are replaced; their truth is not assumed. -/
structure Gates (B₀ L₀ c₀ B L c A D : ℝ) : Prop where
  width_pos : 0 < c - cross B₀ L₀ B L
  sel_den_pos : ∀ v, 0 ≤ v → v ≤ c - cross B₀ L₀ B L → 0 < 1 + D * v
  dens_den_pos : ∀ v, 0 ≤ v → v ≤ c - cross B₀ L₀ B L → 0 < densE B₀ L₀ L A D v
  q_floor : UnifPos (gQFloor B₀ L₀ L A D) 0 (c - cross B₀ L₀ B L)
  q_upper : UnifPos (gQUpper B₀ L₀ L A D) 0 (c - cross B₀ L₀ B L)
  H_lower : UnifPos (gHLower A D) 0 (c - cross B₀ L₀ B L)
  retained_cap : UnifPos (gRetainedCap B₀ L₀ c₀ B L A D) 0 (c - cross B₀ L₀ B L)
  retained_width : UnifPos (gRetainedWidth B₀ L₀ B L A D) 0 (c - cross B₀ L₀ B L)
  low_per_excess_width : UnifPos (gLowPerWidth L₀ A D) 0 (c - cross B₀ L₀ B L)
  high_at_q : UnifPos (gHighAtQ B₀ L₀ B L A D) 0 (c - cross B₀ L₀ B L)
  high_density_derivative : UnifPos (gHighDeriv B₀ L₀ B L A D) 0 (c - cross B₀ L₀ B L)
  high_derivative_factor : UnifPos (gHighFactor B₀ L₀ B L A D) 0 (c - cross B₀ L₀ B L)
  principal_reference : UnifPos (gPrincipal B₀ L₀ B L A D) 0 (c - cross B₀ L₀ B L)
  second_reference : UnifPos (gSecondRef B₀ L₀ B L A D) 0 (c - cross B₀ L₀ B L)
  second_diagonal : UnifPos (gSecondDiag B₀ L₀ B L A D) 0 (c - cross B₀ L₀ B L)
  reference_upper_positive : UnifPos (gRefUpper B₀ L₀ B L A D) 0 (c - cross B₀ L₀ B L)
  selection_monotonicity : UnifPos (gSelDeriv A D) 0 (c - cross B₀ L₀ B L)

/-- Actual generic step data; only the price differs from the original
variable-density data. The selection and every source width remain intact. -/
def stepData (B₀ L₀ c₀ B L c A D : ℝ) (hL : 0 < L₀) : StepData where
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
  price := RefinedPrice.jointDensityPrice B₀ L₀ c₀ L A D (cross B₀ L₀ B L) hL

/-- The subtraction constant contributes no density derivative. -/
theorem highJ_affine (B L W σ ν : ℝ) :
    highJ B L W σ ν = RefinedPrice.k ν * (1 - W - 5*σ) -
      ν * (B - L*W) + (17/200 : ℝ)*W + (1-17/200 : ℝ)*σ := by
  unfold highJ
  ring

theorem highJ_difference (B L W σ ν₁ ν₂ : ℝ)
    (h₁ : 15 - 6*ν₁ ≠ 0) (h₂ : 15 - 6*ν₂ ≠ 0) :
    highJ B L W σ ν₂ - highJ B L W σ ν₁ =
      (ν₂-ν₁) * (150 / ((15-6*ν₁)*(15-6*ν₂)) * (1-W-5*σ) - (B-L*W)) := by
  have hk : RefinedPrice.k ν₂ - RefinedPrice.k ν₁ =
      (ν₂-ν₁) * (150 / ((15-6*ν₁)*(15-6*ν₂))) := by
    simpa only [one_sub_rhoOf, RefinedPrice.k] using
      one_sub_rhoOf_sub ν₁ ν₂ h₁ h₂
  rw [highJ_affine, highJ_affine]
  linear_combination (1-W-5*σ)*hk

/-- The refined density range gives the sharper inherited slope constant. -/
theorem density_slope_ge {ν₁ ν₂ : ℝ}
    (h₁ : ν₁ ∈ Set.Icc (13/20 : ℝ) (3/4))
    (h₂ : ν₂ ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    (5000/4107 : ℝ) ≤ 150 / ((15-6*ν₁)*(15-6*ν₂)) := by
  have hd₁ := RefinedPrice.k_den_pos h₁
  have hd₂ := RefinedPrice.k_den_pos h₂
  apply (le_div_iff₀ (mul_pos hd₁ hd₂)).2
  have hprod : (15-6*ν₁)*(15-6*ν₂) ≤ (111/10 : ℝ)^2 := by
    have ha : 15-6*ν₁ ≤ (111/10 : ℝ) := by linarith [h₁.1]
    have hb : 15-6*ν₂ ≤ (111/10 : ℝ) := by linarith [h₂.1]
    nlinarith [mul_le_mul ha hb hd₂.le (by norm_num : (0:ℝ) ≤ 111/10)]
  nlinarith

theorem highJ_mono_quant {B L W σ ν₁ ν₂ : ℝ}
    (h₁ : ν₁ ∈ Set.Icc (13/20 : ℝ) (3/4))
    (h₂ : ν₂ ∈ Set.Icc (13/20 : ℝ) (3/4)) (hν : ν₁ ≤ ν₂)
    (hfactor : 0 ≤ 1-W-5*σ) :
    highJ B L W σ ν₁ + (ν₂-ν₁) *
      ((5000/4107 : ℝ)*(1-W-5*σ)-(B-L*W)) ≤ highJ B L W σ ν₂ := by
  have hi := highJ_difference B L W σ ν₁ ν₂
    (RefinedPrice.k_den_pos h₁).ne' (RefinedPrice.k_den_pos h₂).ne'
  have hk := mul_le_mul_of_nonneg_right (density_slope_ge h₁ h₂) hfactor
  have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right hk (B-L*W))
    (sub_nonneg.mpr hν)
  linarith

/-- Genuine derivative formula, independent of the constant price subtraction. -/
theorem highJ_hasDerivAt (B L W σ ν : ℝ) (hν : 15-6*ν ≠ 0) :
    HasDerivAt (fun x => highJ B L W σ x)
      (150/(15-6*ν)^2*(1-W-5*σ)-(B-L*W)) ν := by
  have h1 : HasDerivAt (fun x : ℝ => 10*x) 10 ν :=
    ((hasDerivAt_id' ν).const_mul (10:ℝ)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => 15-6*x) (-6) ν :=
    (((hasDerivAt_id' ν).const_mul (6:ℝ)).const_sub (15:ℝ)).congr_deriv (by ring)
  have hk : HasDerivAt RefinedPrice.k (150/(15-6*ν)^2) ν := by
    exact (h1.div h2 hν).congr_deriv (by congr 1; ring)
  have hf := ((hk.mul_const (1-W-5*σ)).sub
    ((hasDerivAt_id' ν).mul_const (B-L*W))).add_const
      ((17/200 : ℝ)*W+(1-17/200 : ℝ)*σ)
  convert hf using 1
  · ext x
    rw [highJ_affine]
    simp only [Pi.sub_apply]
    ring
  · ring

/-- The closed derivative gate bounds the actual derivative everywhere. -/
theorem highJ_deriv_ge {B L W σ ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) (hfactor : 0 ≤ 1-W-5*σ) :
    (5000/4107 : ℝ)*(1-W-5*σ)-(B-L*W) ≤
      150/(15-6*ν)^2*(1-W-5*σ)-(B-L*W) := by
  have h := mul_le_mul_of_nonneg_right (density_slope_ge hν hν) hfactor
  simpa only [pow_two] using sub_le_sub_right h (B-L*W)

/-- Exact HIGH payment before bounding the upward greedy error. -/
theorem high_price_ledger {ν P s B L W u σ t tl : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hP : P ≤ B-L*W+tl) (hs : s ≤ W-u)
    (hcap : s ≤ (1+t-6*u)/10) (ht : -tl ≤ t) :
    RefinedPrice.g ν P s (1+t-6*u)-u ≤ -highJ B L W σ ν +
      (5*RefinedPrice.k ν-1+17/200)*(u-σ)+(ν+RefinedPrice.k ν)*tl := by
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hk : 0 ≤ RefinedPrice.k ν := by linarith [(RefinedPrice.k_range hν).1]
  have hp := mul_le_mul_of_nonneg_left hP hn
  have hslot := mul_le_mul_of_nonneg_left hs (RefinedPrice.retainedSlope_pos hν).le
  have htpaid := mul_nonneg hk (show 0 ≤ t+tl by linarith)
  rw [RefinedPrice.g, max_eq_right (by linarith : s-(1+t-6*u)/10 ≤ 0)]
  unfold RefinedPrice.retainedSlope at hslot
  unfold RefinedPrice.retainedSlope highJ
  nlinarith

theorem overshoot_coefficients {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    (0 ≤ 5*RefinedPrice.k ν-1+17/200 ∧ 5*RefinedPrice.k ν-1+17/200 ≤ 6) ∧
      (0 ≤ ν+RefinedPrice.k ν ∧ ν+RefinedPrice.k ν ≤ 2) := by
  have hk := RefinedPrice.k_range hν
  constructor <;> constructor <;> linarith [hν.1, hν.2]

theorem high_price_paid {ν P s B L W u σ t tl mesh rJ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hP : P ≤ B-L*W+tl) (hs : s ≤ W-u)
    (hcap : s ≤ (1+t-6*u)/10) (ht : -tl ≤ t)
    (hu0 : σ ≤ u) (hu1 : u ≤ σ+mesh) (htl : 0 ≤ tl)
    (hJ : rJ ≤ highJ B L W σ ν) (hreserve : 6*mesh+2*tl ≤ rJ) :
    RefinedPrice.g ν P s (1+t-6*u) ≤ u := by
  have h := high_price_ledger (σ := σ) hν hP hs hcap ht
  have hc := overshoot_coefficients hν
  have ho := mul_le_mul_of_nonneg_right hc.1.2 (sub_nonneg.mpr hu0)
  have hm : 6*(u-σ) ≤ 6*mesh := by linarith
  have hp := mul_le_mul_of_nonneg_right hc.2.2 htl
  linarith


/-- Polynomial numerator of the refined HIGH gate. Its denominator is `T E F`. -/
def highNumerator (B L W Av T E N F : ℝ) : ℝ :=
  10*N*T*E - N*B*T*F +
    (N*L*F-10*N*E+(17/200 : ℝ)*E*F)*T*W -
      Av*E*(50*N-(1-17/200 : ℝ)*F)

theorem highJ_cleared {B L W σ q Av T E N F : ℝ}
    (hσ : σ*T = Av) (hq : q*E = N) (hk : RefinedPrice.k q*F = 10*N) :
    highJ B L W σ q*(T*E*F) = highNumerator B L W Av T E N F := by
  calc
    _ = (RefinedPrice.k q*F)*(1-W-5*σ)*T*E +
        (q*E)*(-B+L*W)*T*F+(17/200 : ℝ)*W*T*E*F+
          (1-17/200 : ℝ)*σ*T*E*F := by rw [highJ_affine]; ring
    _ = 10*N*(1-W-5*σ)*T*E +
        N*(-B+L*W)*T*F+(17/200 : ℝ)*W*T*E*F+
          (1-17/200 : ℝ)*σ*T*E*F := by rw [hk, hq]
    _ = _ := by
      unfold highNumerator
      linear_combination E*(-50*N+(1-17/200 : ℝ)*F)*hσ

/-- The modified HIGH gate's exact cleared form. The three nonzero
requirements are supplied by the positive denominator certificates. -/
theorem gHighAtQ_mul (B₀ L₀ B L A D v : ℝ)
    (hx : 1+D*v ≠ 0) (hE : densE B₀ L₀ L A D v ≠ 0)
    (hF : 15*densE B₀ L₀ L A D v-6*densK L₀ A ≠ 0) :
    let T := 1+D*v
    let E := densE B₀ L₀ L A D v
    let N := densK L₀ A
    let F := 15*E-6*N
    gHighAtQ B₀ L₀ B L A D v*(T*E*F) =
      highNumerator B L (width B₀ L₀ B L v) (A*v) T E N F := by
  dsimp only
  have hs := sel_mul A D v hx
  have hq := dens_mul B₀ L₀ L A D v hE
  let q := dens B₀ L₀ L A D v
  let E := densE B₀ L₀ L A D v
  let N := densK L₀ A
  let F := 15*E-6*N
  have hFE : F = E*(15-6*q) := by dsimp [F, E, N, q]; nlinarith
  have hqd : 15-6*q ≠ 0 := by
    intro hz
    have hzero : F = 0 := by rw [hFE, hz, mul_zero]
    exact hF hzero
  have hkq : RefinedPrice.k q*(15-6*q) = 10*q := by
    unfold RefinedPrice.k
    exact div_mul_cancel₀ _ hqd
  have hk : RefinedPrice.k q*F = 10*N := by
    calc
      _ = (RefinedPrice.k q*(15-6*q))*E := by rw [hFE]; ring
      _ = _ := by rw [hkq]; dsimp [q, E, N]; nlinarith
  exact highJ_cleared hs hq hk

/-- The positive derivative factor has the saved quadratic numerator. -/
theorem gHighFactor_mul (B₀ L₀ B L A D v : ℝ) (hx : 1+D*v ≠ 0) :
    gHighFactor B₀ L₀ B L A D v*(1+D*v) =
      (1-width B₀ L₀ B L v)*(1+D*v)-5*A*v := by
  have hs := sel_mul A D v hx
  unfold gHighFactor
  linear_combination (-5:ℝ)*hs

/-- The derivative gate uses exactly the same density slope as its ledger. -/
theorem gHighDeriv_mul (B₀ L₀ B L A D v : ℝ) (hx : 1+D*v ≠ 0) :
    gHighDeriv B₀ L₀ B L A D v*(1+D*v) =
      (5000/4107 : ℝ)*((1-width B₀ L₀ B L v)*(1+D*v)-5*A*v) -
        (B-L*width B₀ L₀ B L v)*(1+D*v) := by
  have hf := gHighFactor_mul B₀ L₀ B L A D v hx
  unfold gHighDeriv
  linear_combination (5000/4107 : ℝ)*hf

/-- Exact extra source-step reserve relative to the previous 1/12 price. -/
theorem highJ_gain (B L W σ ν : ℝ) :
    highJ B L W σ ν -
      (RefinedPrice.k ν-ν*B+(ν*L-RefinedPrice.k ν+1/12)*W-
        (5*RefinedPrice.k ν-1+1/12)*σ) = (W-σ)/600 := by
  unfold highJ
  ring


section
variable {B₀ L₀ c₀ B L c A D : ℝ}
namespace Gates

theorem dens_mem (h : Gates B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    1/2 < dens B₀ L₀ L A D v ∧ dens B₀ L₀ L A D v < 3/4 := by
  have ha := h.q_floor.pos v h0 h1
  have hb := h.q_upper.pos v h0 h1
  unfold gQFloor at ha
  unfold gQUpper at hb
  constructor <;> linarith

theorem dens_floor (h : Gates B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    13/20 < dens B₀ L₀ L A D v := by
  have ha := h.q_floor.pos v h0 h1
  unfold gQFloor at ha
  linarith

theorem low_identity (h : Gates B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    lowDefect B₀ L₀ L A D v = (1/1000 : ℝ) * L₀ * sel A D v :=
  lowDefect_eq B₀ L₀ L A D v (h.sel_den_pos v h0 h1).ne'
    (h.dens_den_pos v h0 h1).ne'
theorem dsA_pos (h : Gates B₀ L₀ c₀ B L c A D) : 0 < A := by
  have := h.selection_monotonicity.pos 0 le_rfl h.width_pos.le
  simpa [gSelDeriv] using this

theorem dsCross_lt_c₀ (h : Gates B₀ L₀ c₀ B L c A D) :
    cross B₀ L₀ B L < c₀ := by
  have := h.retained_cap.pos 0 le_rfl h.width_pos.le
  simp only [gRetainedCap, packed, width, sel_zero] at this
  linarith

theorem dsSel_nonneg (h : Gates B₀ L₀ c₀ B L c A D) {v : ℝ} (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B₀ L₀ B L) : 0 ≤ sel A D v :=
  div_nonneg (mul_nonneg h.dsA_pos.le h0) (h.sel_den_pos v h0 h1).le

theorem dsSel_mono (h : Gates B₀ L₀ c₀ B L c A D) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ c - cross B₀ L₀ B L) : sel A D a ≤ sel A D b := by
  have da := h.sel_den_pos a ha (hab.trans hb)
  have db := h.sel_den_pos b (ha.trans hab) hb
  unfold sel
  rw [div_le_div_iff₀ da db]
  nlinarith [mul_le_mul_of_nonneg_left hab h.dsA_pos.le]

/-- `q(v)·(6B₀-L₀) ≤ L₀`: the LOW overshoot coefficient is at most one. -/
theorem dsDens_overshoot (h : Gates B₀ L₀ c₀ B L c A D)
    (hF : DSFace B₀ L₀ c₀ B L c) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    dens B₀ L₀ L A D v * (6 * B₀ - L₀) ≤ L₀ := by
  have hE := h.dens_den_pos v h0 h1
  have hm := dens_mul B₀ L₀ L A D v hE.ne'
  unfold densE densK at hm
  have hA := h.dsA_pos
  have hx := h.sel_den_pos v h0 h1
  have hq := (h.dens_mem v h0 h1).1
  have hLL : 0 < L₀ - L := sub_pos.2 hF.L_lt
  have hL₀ : 0 < L₀ := by linarith [hF.one_lt_L]
  have hp : 0 < dens B₀ L₀ L A D v * ((L₀ - L) * (1 + D * v)) :=
    mul_pos (by linarith) (mul_pos hLL hx)
  have key : (dens B₀ L₀ L A D v * (6 * B₀ - L₀) - L₀) * A ≤ 0 := by
    nlinarith [mul_pos hL₀ hA]
  by_contra hc
  have hc : L₀ < dens B₀ L₀ L A D v * (6 * B₀ - L₀) := lt_of_not_ge hc
  have := mul_pos (sub_pos.2 hc) hA
  linarith


theorem high_mono (h : Gates B₀ L₀ c₀ B L c A D) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ c-cross B₀ L₀ B L)
    (ν : ℝ) (hν : dens B₀ L₀ L A D v ≤ ν) (hν' : ν ≤ 3/4) :
    gHighAtQ B₀ L₀ B L A D v ≤
      highJ B L (width B₀ L₀ B L v) (sel A D v) ν := by
  have hq : dens B₀ L₀ L A D v ∈ Set.Icc (13/20 : ℝ) (3/4) :=
    ⟨(h.dens_floor v h0 h1).le, (h.dens_mem v h0 h1).2.le⟩
  have hn : ν ∈ Set.Icc (13/20 : ℝ) (3/4) := ⟨hq.1.trans hν, hν'⟩
  have hf := h.high_derivative_factor.pos v h0 h1
  have hd := h.high_density_derivative.pos v h0 h1
  have hm := highJ_mono_quant (B := B) (L := L) hq hn hν (by exact hf.le)
  have hprod := mul_nonneg (sub_nonneg.mpr hν) hd.le
  change gHighAtQ B₀ L₀ B L A D v ≤ _
  unfold gHighAtQ
  dsimp [gHighDeriv, gHighFactor] at hprod
  linarith

theorem high_reserve (h : Gates B₀ L₀ c₀ B L c A D) :
    ∃ r, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ c-cross B₀ L₀ B L →
      ∀ ν, dens B₀ L₀ L A D v ≤ ν → ν ≤ 3/4 →
        r ≤ highJ B L (width B₀ L₀ B L v) (sel A D v) ν := by
  obtain ⟨r, hr, hJ⟩ := h.high_at_q
  exact ⟨r, hr, fun v h0 h1 ν hν hν' =>
    (hJ v h0 h1).trans (h.high_mono v h0 h1 ν hν hν')⟩

end Gates

theorem ledger (h : Gates B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c)
    (hL : 0 < L₀) (hc₀ : c₀ ≤ 1/10) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × ℝ × ℝ, LedgerAt (stepData B₀ L₀ c₀ B L c A D hL) ε p.1 p.2.1 p.2.2 := by
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
  have hQ : densQ B₀ L₀ L A D (cross B₀ L₀ B L) g.w = dens B₀ L₀ L A D v := by
    have := densQ_eq (B₀ := B₀) (L₀ := L₀) (L := L) (A := A) (D := D)
      (s₀ := cross B₀ L₀ B L) (w := g.w) (by rw [← hv]; exact hqf.le) (by rw [← hv]; exact hq.2.le)
    rw [← hv] at this; exact this
  show max (lowPart B₀ L₀ c₀ (densQ B₀ L₀ L A D (cross B₀ L₀ B L) g.w) g.PC g.s g.H)
      (RefinedPrice.highSup (densQ B₀ L₀ L A D (cross B₀ L₀ B L) g.w) g.PC g.s g.H) ≤ g.u + ε/16
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
    unfold lowDefect at hC
    have hq0 : 0 ≤ dens B₀ L₀ L A D v := by linarith
    have hqd := ds_low_aux hq0 hq.2.le hF.B₀_lt hL.le hσ0 hu0 hdef hC hq6 htl ht4
    have hneed := deletionNeed_le_defect (B₀ := B₀) (L₀ := L₀) (P := g.PC) hcap
    unfold lowPart
    calc dens B₀ L₀ L A D v * deletionNeed B₀ L₀ c₀ g.PC g.s g.H
        ≤ dens B₀ L₀ L A D v * max 0 ((g.PC + L₀ * g.s - B₀ * g.H) / L₀) :=
          mul_le_mul_of_nonneg_left hneed hq0
      _ = max 0 (dens B₀ L₀ L A D v * (g.PC + L₀ * g.s - B₀ * g.H) / L₀) := by
          rw [mul_max_of_nonneg _ _ hq0, mul_zero, mul_div_assoc]
      _ ≤ g.u + ε/16 := by
          refine max_le (by linarith) ?_
          rw [div_le_iff₀ hL]; linarith
  · -- HIGH: the modified price and every retained-slot branch are paid.
    refine RefinedPrice.highSup_le hq.2.le fun ν hν1 hν2 => ?_
    have hJ := hJr v hv0 hv1 ν hν1 hν2
    simp only [width] at hJ
    have hn : ν ∈ Set.Icc (13/20 : ℝ) (3/4) :=
      ⟨(h.dens_floor v hv0 hv1).le.trans hν1, hν2⟩
    have hh : RefinedPrice.g ν g.PC g.s g.H ≤ g.u := by
      rw [hH] at hcap ⊢
      exact high_price_paid hn hP hslot hcap ht.1 hu0 hu1 htl hJ (by linarith)
    linarith

theorem reference (h : Gates B₀ L₀ c₀ B L c A D) (hL : 0 < L₀) :
    ∃ ρ, ReferenceAt (stepData B₀ L₀ c₀ B L c A D hL) ρ := by
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
theorem stepGates (h : Gates B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c)
    (hL : 0 < L₀) (hc₀ : c₀ ≤ 1/10) : StepGates (stepData B₀ L₀ c₀ B L c A D hL) where
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

end
end Qrh.JointDetector.RefinedLedger

#print axioms Qrh.JointDetector.RefinedLedger.stepGates
#print axioms Qrh.JointDetector.RefinedLedger.high_price_ledger
#print axioms Qrh.JointDetector.RefinedLedger.gHighAtQ_mul
#print axioms Qrh.JointDetector.RefinedLedger.highJ_hasDerivAt
