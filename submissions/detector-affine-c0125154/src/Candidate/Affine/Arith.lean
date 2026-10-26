/- Copyright (c) 2026. Released under Apache 2.0. -/
import Mathlib.Tactic

set_option autoImplicit false

namespace DetectorAffine
noncomputable section

/-! Detector count with the affine plain capacity (Cycle61 Theorem 2.2).
The constants `lam` and `Bc` are `Cycle61.Arithmetic.lambda` and `Cycle61.Arithmetic.B`. -/

/-- Affine capacity constants of Cycle61 Theorem 2.2 (`Cycle61.Arithmetic.lambda`, `B`). -/
def lam : ℝ := 19312/4787
def Bc : ℝ := 1419985639/1436100000
/-- Plain-length window on which the affine capacity is used. -/
def mLo : ℝ := (Bc-lam/25)/2
def mHi : ℝ := 847/2000

def DN (p : ℝ) : ℝ := 3-p-4*p/lam
def aN (p : ℝ) : ℝ := 2-4*p/lam
def cN (p : ℝ) : ℝ := 1-2*p*Bc/lam
/-- Crossing of the inverse branch with the affine plain branch. -/
def rN (p t : ℝ) : ℝ := (aN p*t+2*p*Bc/lam-p)/DN p
def shortNew (δ p t : ℝ) : ℝ := 1-δ*(p+(1-p)*rN p t)
def inverseExp (δ p r : ℝ) : ℝ := 1-δ*(p+(1-p)*r)
def affineExp (δ p m : ℝ) : ℝ := 1-2*δ*m-2*(δ*p)*(Bc-2*m)/lam
def oldPlainExp (δ p κ m : ℝ) : ℝ := 1-2*δ*m-2*(δ*p)*(1-2*m)/(6*κ)
def longExp (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)
def JN (δ p : ℝ) : ℝ := (5/6-δ)*DN p+δ*(1-p)*aN p
def numT (δ p : ℝ) : ℝ := (5/6-δ)*DN p+δ*(1-p)*(aN p+cN p)
/-- New cutoff and the new detector count exponent. -/
def tN (δ p : ℝ) : ℝ := numT δ p/JN δ p
def RNew (δ p : ℝ) : ℝ := 1-δ+(5/6-δ)*δ*(1-p)*cN p/JN δ p
/-- The parameter box on which the new count replaces the old one. -/
def InRegion (δ p : ℝ) : Prop := 89/200 ≤ δ ∧ δ ≤ 97/200 ∧ 99/200 ≤ p ∧ p ≤ 1/2

instance (δ p : ℝ) : Decidable (InRegion δ p) := Classical.dec _

theorem lam_pos : 0 < lam := by norm_num [lam]
theorem mLo_gt : 41/100 < mLo := by norm_num [mLo, Bc, lam]
theorem mLo_le_mHi : mLo ≤ mHi := by norm_num [mLo, mHi, Bc, lam]

theorem DN_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < DN p := by
  unfold DN lam; nlinarith
theorem aN_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < aN p := by
  unfold aN lam; nlinarith
theorem cN_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < cN p := by
  unfold cN Bc lam; nlinarith

theorem affine_at_crossing (δ p t : ℝ) (hd : DN p ≠ 0) :
    affineExp δ p (t-rN p t) = shortNew δ p t := by
  have hr : rN p t * DN p = aN p*t+2*p*Bc/lam-p := div_mul_cancel₀ _ hd
  unfold affineExp shortNew
  unfold DN aN at hr
  linear_combination δ * hr

theorem short_ge_base {δ p t : ℝ} (hδ : 0 ≤ δ) (hp1 : p ≤ 1) (hr : rN p t ≤ 1) :
    1-δ ≤ shortNew δ p t := by
  unfold shortNew
  have : p+(1-p)*rN p t ≤ 1 := by nlinarith
  nlinarith

theorem inverse_le_short {δ p t r : ℝ} (hδ : 0 ≤ δ) (hp1 : p ≤ 1) (hr : rN p t ≤ r) :
    inverseExp δ p r ≤ shortNew δ p t := by
  unfold inverseExp shortNew
  have h1 := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1-p by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hδ]

/-- The affine plain exponent is nonincreasing in the plain length. -/
theorem affine_antitone {δ p m m' : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (hm : m' ≤ m) :
    affineExp δ p m ≤ affineExp δ p m' := by
  unfold affineExp
  have hl := lam_pos
  have hk : 4*p/lam ≤ 2 := by rw [div_le_iff₀ hl]; unfold lam at *; nlinarith
  have e : ∀ u : ℝ, 1-2*δ*u-2*(δ*p)*(Bc-2*u)/lam = 1-2*δ*p*Bc/lam-δ*(2-4*p/lam)*u := by
    intro u; field_simp; ring
  rw [e m, e m']
  have : 0 ≤ δ*(2-4*p/lam) := mul_nonneg hδ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hm this]

theorem affine_shift {δ p m : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (γ : ℝ)
    (hγ : 0 ≤ γ) : affineExp δ p (m-γ) ≤ affineExp δ p m+2*γ := by
  unfold affineExp
  have hl := lam_pos
  have hk : 0 ≤ 4*p/lam := by positivity
  have e : ∀ u : ℝ, 1-2*δ*u-2*(δ*p)*(Bc-2*u)/lam = 1-2*δ*p*Bc/lam-δ*(2-4*p/lam)*u := by
    intro u; field_simp; ring
  rw [e (m-γ), e m]
  have h2 : δ*(2-4*p/lam) ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h2 hγ]

theorem old_antitone {δ p κ m m' : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hp1 : p ≤ 1/2)
    (hk : 7/10 ≤ κ) (hm : m' ≤ m) : oldPlainExp δ p κ m ≤ oldPlainExp δ p κ m' := by
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
    (hrN : 23/37 ≤ rN x t) (hrN1 : rN x t ≤ 1) (hmN : mLo+γ ≤ t-rN x t)
    (htail : oldPlainExp δ x κ mHi ≤ shortNew δ x t)
    (hI0 : B ≤ C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B ≤ C*U^(1-2*δ*m+ε))
    (hI : 23/37 ≤ r → r < 1 → ν < (1-r)/2 → B ≤ C*U^(inverseExp δ x r+ε))
    (hA : mLo ≤ m → m ≤ mHi → B ≤ C*U^(affineExp δ x m+2*(δ*x)*ν+ε))
    (hP : mHi ≤ m → m < 1/2 → ν < (1-2*m)/(6*κ) → B ≤ C*U^(oldPlainExp δ x κ m+ε)) :
    B ≤ C*U^(max (shortNew δ x t) (longExp δ t)+ε+6*ν+5*γ) := by
  have hshort : shortNew δ x t ≤ max (shortNew δ x t) (longExp δ t) := le_max_left _ _
  have hlong : longExp δ t ≤ max (shortNew δ x t) (longExp δ t) := le_max_right _ _
  have hbase : 1-δ ≤ shortNew δ x t := short_ge_base hδ (by linarith) hrN1
  have promote (q : ℝ) (hq : B ≤ C*U^q)
      (hqt : q ≤ max (shortNew δ x t) (longExp δ t)+ε+6*ν+5*γ) :
      B ≤ C*U^(max (shortNew δ x t) (longExp δ t)+ε+6*ν+5*γ) :=
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
    have hl2 : longExp δ t = 1-δ+(5/6-δ)*(t-1) := rfl
    have e1 : (1+5*r)/6-δ*r = 1/6+(5/6-δ)*r := by ring
    have e2 : (5/6-δ)*(t+γ) = (5/6-δ)*(t-1)+(5/6-δ)+(5/6-δ)*γ := by ring
    linarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6) = 1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : rN x t ≤ r
  · by_cases hcap : (1-r)/2 ≤ ν
    · apply promote _ hI0
      have hh := mul_le_mul_of_nonneg_left hcap hδ
      have e : δ*((1-r)/2) = δ/2-δ*r/2 := by ring
      linarith
    · apply promote _ (hI (hrN.trans hrc) hr1' (lt_of_not_ge hcap))
      have := inverse_le_short (δ:=δ) hδ (by linarith) hrc
      linarith
  have hrc' : r < rN x t := lt_of_not_ge hrc
  have hmlo : t-rN x t-γ ≤ m := by linarith
  by_cases hm : 1/2 ≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    linarith
  have hm' : m < 1/2 := lt_of_not_ge hm
  by_cases hmh : m ≤ mHi
  · apply promote _ (hA (by linarith) hmh)
    have h1 := affine_antitone (p:=x) hδ hx hx' hmlo
    have h2 := affine_shift (p:=x) (m:=t-rN x t) hδ (by linarith) hx hx' γ hγ
    have h3 := affine_at_crossing δ x t (DN_pos hx hx').ne'
    linarith
  have hmh' : mHi ≤ m := (lt_of_not_ge hmh).le
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
    have := old_antitone (κ:=κ) hδ hx hx' hk hmh'
    linarith

/-- At the new cutoff both branches meet at the new count exponent. -/
theorem short_at_tN {δ p : ℝ} (hJ : JN δ p ≠ 0) (hD : DN p ≠ 0) :
    shortNew δ p (tN δ p) = RNew δ p := by
  have hr : rN p (tN δ p) * DN p = aN p*tN δ p+2*p*Bc/lam-p := div_mul_cancel₀ _ hD
  have hT : tN δ p * JN δ p = numT δ p := div_mul_cancel₀ _ hJ
  have hR : (RNew δ p-1+δ) * JN δ p = (5/6-δ)*δ*(1-p)*cN p := by
    unfold RNew
    rw [show 1-δ+(5/6-δ)*δ*(1-p)*cN p/JN δ p-1+δ = (5/6-δ)*δ*(1-p)*cN p/JN δ p by ring]
    exact div_mul_cancel₀ _ hJ
  have key : (shortNew δ p (tN δ p)-RNew δ p) * (DN p * JN δ p) = 0 := by
    unfold shortNew
    unfold JN numT DN aN cN at *
    linear_combination (-δ*(1-p)*((5/6-δ)*(3-p-4*p/lam)+δ*(1-p)*(2-4*p/lam))) * hr
      + (-δ*(1-p)*(2-4*p/lam)) * hT + (-(3-p-4*p/lam)) * hR
  have hne : DN p * JN δ p ≠ 0 := mul_ne_zero hD hJ
  have := (mul_eq_zero.mp key).resolve_right hne
  linarith

theorem long_at_tN {δ p : ℝ} (hJ : JN δ p ≠ 0) :
    longExp δ (tN δ p) = RNew δ p := by
  have hT : tN δ p * JN δ p = numT δ p := div_mul_cancel₀ _ hJ
  have hR : (RNew δ p-1+δ) * JN δ p = (5/6-δ)*δ*(1-p)*cN p := by
    unfold RNew
    rw [show 1-δ+(5/6-δ)*δ*(1-p)*cN p/JN δ p-1+δ = (5/6-δ)*δ*(1-p)*cN p/JN δ p by ring]
    exact div_mul_cancel₀ _ hJ
  have key : (longExp δ (tN δ p)-RNew δ p) * JN δ p = 0 := by
    unfold longExp
    unfold JN numT at *
    linear_combination (5/6-δ) * hT - hR
  have := (mul_eq_zero.mp key).resolve_right hJ
  linarith

theorem max_at_tN {δ p : ℝ} (hJ : JN δ p ≠ 0) (hD : DN p ≠ 0) :
    max (shortNew δ p (tN δ p)) (longExp δ (tN δ p)) = RNew δ p := by
  rw [short_at_tN hJ hD, long_at_tN hJ, max_self]

end
end DetectorAffine
