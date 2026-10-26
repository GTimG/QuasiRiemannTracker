/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted parametrically from Gao's Target836/Detector836/Arith.lean,
source snapshot gao-balanced-marked-20261017; exact hashes in companion receipt.
The common r,m are the lengths of one supported witness, not independent optima. -/
import Mathlib.Tactic
set_option autoImplicit false
namespace QRH.Record12518109Count
noncomputable section
structure Parameters where
  Bc : ℝ
  lam : ℝ
  mLo : ℝ
  mHi : ℝ
  lam_gt_one : 1 < lam
namespace Parameters
variable (P : Parameters)
def DN (P : Parameters) (p : ℝ) : ℝ := 3-p-4*p/P.lam
def aN (P : Parameters) (p : ℝ) : ℝ := 2-4*p/P.lam
def cN (P : Parameters) (p : ℝ) : ℝ := 1-2*p*P.Bc/P.lam
/-- Crossing of the inverse branch with the affine plain branch. -/
def rN (P : Parameters) (p t : ℝ) : ℝ := (P.aN p*t+2*p*P.Bc/P.lam-p)/P.DN p
def shortNew (P : Parameters) (δ p t : ℝ) : ℝ := 1-δ*(p+(1-p)*P.rN p t)
def inverseExp (P : Parameters) (δ p r : ℝ) : ℝ := 1-δ*(p+(1-p)*r)
def affineExp (P : Parameters) (δ p m : ℝ) : ℝ := 1-2*δ*m-2*(δ*p)*(P.Bc-2*m)/P.lam
def oldPlainExp (P : Parameters) (δ p κ m : ℝ) : ℝ := 1-2*δ*m-2*(δ*p)*(1-2*m)/(6*κ)
def longExp (P : Parameters) (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)
def JN (P : Parameters) (δ p : ℝ) : ℝ := (5/6-δ)*P.DN p+δ*(1-p)*P.aN p
def numT (P : Parameters) (δ p : ℝ) : ℝ := (5/6-δ)*P.DN p+δ*(1-p)*(P.aN p+P.cN p)
/-- New cutoff and the new detector count exponent. -/
def tN (P : Parameters) (δ p : ℝ) : ℝ := P.numT δ p/P.JN δ p
def RNew (P : Parameters) (δ p : ℝ) : ℝ := 1-δ+(5/6-δ)*δ*(1-p)*P.cN p/P.JN δ p
theorem lam_pos : 0 < P.lam := by linarith [P.lam_gt_one]
theorem DN_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < P.DN p := by
  unfold DN; rw [sub_pos];
  have h := P.lam_gt_one
  have hq : 4*p/P.lam < 2 := by rw [div_lt_iff₀ (lam_pos P)]; nlinarith
  linarith
theorem aN_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < P.aN p := by
  unfold aN; rw [sub_pos, div_lt_iff₀ (lam_pos P)]; nlinarith [P.lam_gt_one]
theorem affine_at_crossing (δ p t : ℝ) (hd : P.DN p ≠ 0) :
    P.affineExp δ p (t-P.rN p t) = P.shortNew δ p t := by
  have hr : P.rN p t * P.DN p = P.aN p*t+2*p*P.Bc/P.lam-p := div_mul_cancel₀ _ hd
  unfold affineExp shortNew
  unfold DN aN at hr
  linear_combination δ * hr

theorem short_ge_base {δ p t : ℝ} (hδ : 0 ≤ δ) (hp1 : p ≤ 1) (hr : P.rN p t ≤ 1) :
    1-δ ≤ P.shortNew δ p t := by
  unfold shortNew
  have : p+(1-p)*P.rN p t ≤ 1 := by nlinarith
  nlinarith

theorem inverse_le_short {δ p t r : ℝ} (hδ : 0 ≤ δ) (hp1 : p ≤ 1) (hr : P.rN p t ≤ r) :
    P.inverseExp δ p r ≤ P.shortNew δ p t := by
  unfold inverseExp shortNew
  have h1 := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1-p by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hδ]

/-- The affine plain exponent is nonincreasing in the plain length. -/
theorem affine_antitone {δ p m m' : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (hm : m' ≤ m) :
    P.affineExp δ p m ≤ P.affineExp δ p m' := by
  unfold affineExp
  have hl := lam_pos P
  have hk : 4*p/P.lam ≤ 2 := by rw [div_le_iff₀ hl]; nlinarith [P.lam_gt_one]
  have e : ∀ u : ℝ, 1-2*δ*u-2*(δ*p)*(P.Bc-2*u)/P.lam = 1-2*δ*p*P.Bc/P.lam-δ*(2-4*p/P.lam)*u := by
    intro u; field_simp; ring
  rw [e m, e m']
  have : 0 ≤ δ*(2-4*p/P.lam) := mul_nonneg hδ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hm this]

theorem affine_shift {δ p m : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (γ : ℝ)
    (hγ : 0 ≤ γ) : P.affineExp δ p (m-γ) ≤ P.affineExp δ p m+2*γ := by
  unfold affineExp
  have hl := lam_pos P
  have hk : 0 ≤ 4*p/P.lam := by positivity
  have e : ∀ u : ℝ, 1-2*δ*u-2*(δ*p)*(P.Bc-2*u)/P.lam = 1-2*δ*p*P.Bc/P.lam-δ*(2-4*p/P.lam)*u := by
    intro u; field_simp; ring
  rw [e (m-γ), e m]
  have h2 : δ*(2-4*p/P.lam) ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h2 hγ]

theorem old_antitone {δ p κ m m' : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hp1 : p ≤ 1/2)
    (hk : 7/10 ≤ κ) (hm : m' ≤ m) : P.oldPlainExp δ p κ m ≤ P.oldPlainExp δ p κ m' := by
  unfold oldPlainExp
  have hk0 : 0 < 6*κ := by linarith
  have e : ∀ u : ℝ, 1-2*δ*u-2*(δ*p)*(1-2*u)/(6*κ) = 1-2*δ*p/(6*κ)-δ*(2-4*p/(6*κ))*u := by
    intro u; field_simp; ring
  rw [e m, e m']
  have hq : 4*p/(6*κ) ≤ 2 := by rw [div_le_iff₀ hk0]; nlinarith
  have : 0 ≤ δ*(2-4*p/(6*κ)) := mul_nonneg hδ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hm this]

/-- Combination of the five detector branches with the affine plain branch.
`B` is the count, `C*U^_` the common prefactor. -/
theorem affine_count_bound (B C U δ x κ t r m ε ν γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6)
    (hx : 0 ≤ x) (hx' : x ≤ 1/2) (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4)
    (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hleft : t-r-γ ≤ m) (hright : r ≤ t+γ)
    (hrN : 23/37 ≤ P.rN x t) (hrN1 : P.rN x t ≤ 1) (hmN : P.mLo+γ ≤ t-P.rN x t)
    (htail : P.oldPlainExp δ x κ P.mHi ≤ P.shortNew δ x t)
    (hI0 : B ≤ C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B ≤ C*U^(1-2*δ*m+ε))
    (hI : 23/37 ≤ r → r < 1 → ν < (1-r)/2 → B ≤ C*U^(P.inverseExp δ x r+ε))
    (hA : P.mLo ≤ m → m ≤ P.mHi → B ≤ C*U^(P.affineExp δ x m+2*(δ*x)*ν+ε))
    (hP : P.mHi ≤ m → m < 1/2 → ν < (1-2*m)/(6*κ) → B ≤ C*U^(P.oldPlainExp δ x κ m+ε)) :
    B ≤ C*U^(max (P.shortNew δ x t) (P.longExp δ t)+ε+6*ν+5*γ) := by
  have hshort : P.shortNew δ x t ≤ max (P.shortNew δ x t) (P.longExp δ t) := le_max_left _ _
  have hlong : P.longExp δ t ≤ max (P.shortNew δ x t) (P.longExp δ t) := le_max_right _ _
  have hbase : 1-δ ≤ P.shortNew δ x t := short_ge_base P hδ (by linarith) hrN1
  have promote (q : ℝ) (hq : B ≤ C*U^q)
      (hqt : q ≤ max (P.shortNew δ x t) (P.longExp δ t)+ε+6*ν+5*γ) :
      B ≤ C*U^(max (P.shortNew δ x t) (P.longExp δ t)+ε+6*ν+5*γ) :=
    hq.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hqt) hC)
  have hdx : δ*x ≤ (5/6)*(1/2) := mul_le_mul hδ' hx' hx (by norm_num)
  have hδν : 2*(δ*x)*ν ≤ 1*ν := mul_le_mul_of_nonneg_right (by linarith) hν
  have h2δν : 2*δ*ν ≤ 2*ν := by
    have := mul_le_mul_of_nonneg_right hδ' hν; linarith
  by_cases hr1 : 1 ≤ r
  · have hmax : max 1 ((1+5*r)/6) = (1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hh := mul_le_mul_of_nonneg_left hright (show 0 ≤ 5/6-δ by linarith)
    have hcγ : (5/6-δ)*γ ≤ 1*γ := mul_le_mul_of_nonneg_right (by linarith) hγ
    have hl2 : P.longExp δ t = 1-δ+(5/6-δ)*(t-1) := rfl
    have e1 : (1+5*r)/6-δ*r = 1/6+(5/6-δ)*r := by ring
    have e2 : (5/6-δ)*(t+γ) = (5/6-δ)*(t-1)+(5/6-δ)+(5/6-δ)*γ := by ring
    linarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6) = 1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : P.rN x t ≤ r
  · by_cases hcap : (1-r)/2 ≤ ν
    · apply promote _ hI0
      have hh := mul_le_mul_of_nonneg_left hcap hδ
      have e : δ*((1-r)/2) = δ/2-δ*r/2 := by ring
      linarith
    · apply promote _ (hI (hrN.trans hrc) hr1' (lt_of_not_ge hcap))
      have := inverse_le_short P (δ:=δ) hδ (by linarith) hrc
      linarith
  have hrc' : r < P.rN x t := lt_of_not_ge hrc
  have hmlo : t-P.rN x t-γ ≤ m := by linarith
  by_cases hm : 1/2 ≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    linarith
  have hm' : m < 1/2 := lt_of_not_ge hm
  by_cases hmh : m ≤ P.mHi
  · apply promote _ (hA (by linarith) hmh)
    have h1 := affine_antitone P (p:=x) hδ hx hx' hmlo
    have h2 := affine_shift P (p:=x) (m:=t-P.rN x t) hδ (by linarith) hx hx' γ hγ
    have h3 := affine_at_crossing P δ x t (DN_pos P hx hx').ne'
    linarith
  have hmh' : P.mHi ≤ m := (lt_of_not_ge hmh).le
  by_cases hcap : (1-2*m)/(6*κ) ≤ ν
  · apply promote _ hP0
    have hh := (div_le_iff₀ (show 0 < 6*κ by linarith)).mp hcap
    have hk6 : ν*(6*κ) ≤ ν*(9/2) := mul_le_mul_of_nonneg_left (by linarith) hν
    have hm6 : 1-2*m ≤ 6*ν := by linarith
    have hh' := mul_le_mul_of_nonneg_left hm6 hδ
    have h6 : δ*(6*ν) ≤ 6*ν := by
      have := mul_le_mul_of_nonneg_right hδ' (show 0 ≤ 6*ν by linarith); linarith
    have e : δ*(1-2*m) = δ-2*δ*m := by ring
    linarith
  · apply promote _ (hP hmh' hm' (lt_of_not_ge hcap))
    have := old_antitone P (κ:=κ) hδ hx hx' hk hmh'
    linarith

/-- At the new cutoff both branches meet at the new count exponent. -/
theorem short_at_tN {δ p : ℝ} (hJ : P.JN δ p ≠ 0) (hD : P.DN p ≠ 0) :
    P.shortNew δ p (P.tN δ p) = P.RNew δ p := by
  have hr : P.rN p (P.tN δ p) * P.DN p = P.aN p*P.tN δ p+2*p*P.Bc/P.lam-p := div_mul_cancel₀ _ hD
  have hT : P.tN δ p * P.JN δ p = P.numT δ p := div_mul_cancel₀ _ hJ
  have hR : (P.RNew δ p-1+δ) * P.JN δ p = (5/6-δ)*δ*(1-p)*P.cN p := by
    unfold RNew
    rw [show 1-δ+(5/6-δ)*δ*(1-p)*P.cN p/P.JN δ p-1+δ = (5/6-δ)*δ*(1-p)*P.cN p/P.JN δ p by ring]
    exact div_mul_cancel₀ _ hJ
  have key : (P.shortNew δ p (P.tN δ p)-P.RNew δ p) * (P.DN p * P.JN δ p) = 0 := by
    unfold shortNew
    unfold JN numT DN aN cN at *
    linear_combination (-δ*(1-p)*((5/6-δ)*(3-p-4*p/P.lam)+δ*(1-p)*(2-4*p/P.lam))) * hr
      + (-δ*(1-p)*(2-4*p/P.lam)) * hT + (-(3-p-4*p/P.lam)) * hR
  have hne : P.DN p * P.JN δ p ≠ 0 := mul_ne_zero hD hJ
  have := (mul_eq_zero.mp key).resolve_right hne
  linarith

theorem long_at_tN {δ p : ℝ} (hJ : P.JN δ p ≠ 0) :
    P.longExp δ (P.tN δ p) = P.RNew δ p := by
  have hT : P.tN δ p * P.JN δ p = P.numT δ p := div_mul_cancel₀ _ hJ
  have hR : (P.RNew δ p-1+δ) * P.JN δ p = (5/6-δ)*δ*(1-p)*P.cN p := by
    unfold RNew
    rw [show 1-δ+(5/6-δ)*δ*(1-p)*P.cN p/P.JN δ p-1+δ = (5/6-δ)*δ*(1-p)*P.cN p/P.JN δ p by ring]
    exact div_mul_cancel₀ _ hJ
  have key : (P.longExp δ (P.tN δ p)-P.RNew δ p) * P.JN δ p = 0 := by
    unfold longExp
    unfold JN numT at *
    linear_combination (5/6-δ) * hT - hR
  have := (mul_eq_zero.mp key).resolve_right hJ
  linarith

theorem max_at_tN {δ p : ℝ} (hJ : P.JN δ p ≠ 0) (hD : P.DN p ≠ 0) :
    max (P.shortNew δ p (P.tN δ p)) (P.longExp δ (P.tN δ p)) = P.RNew δ p := by
  rw [short_at_tN P hJ hD, long_at_tN P hJ, max_self]


end Parameters
end
end QRH.Record12518109Count
