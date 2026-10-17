/- Generic actual-plane version of the accepted affine detector arithmetic.
OpenAI/Hailey Collet predecessor attribution retained. Apache-2.0. -/
import Candidate.Target830.Count.MarkedFiber

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.Target830.Physical.CountArithmetic
variable (P : Count.Plane)

def DN (p : ℝ) : ℝ := 3-p-4*p/(P.lambda)
def aN (p : ℝ) : ℝ := 2-4*p/(P.lambda)
def cN (p : ℝ) : ℝ := 1-2*p*(P.B)/(P.lambda)
/-- Crossing of the inverse branch with the affine plain branch. -/
def rN (p t : ℝ) : ℝ := (aN P p*t+2*p*(P.B)/(P.lambda)-p)/DN P p
def shortNew (δ p t : ℝ) : ℝ := 1-δ*(p+(1-p)*rN P p t)
def inverseExp (δ p r : ℝ) : ℝ := 1-δ*(p+(1-p)*r)
def affineExp (δ p m : ℝ) : ℝ := 1-2*δ*m-2*(δ*p)*((P.B)-2*m)/(P.lambda)
def oldPlainExp (δ p κ m : ℝ) : ℝ := 1-2*δ*m-2*(δ*p)*(1-2*m)/(6*κ)
def longExp (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)
def JN (δ p : ℝ) : ℝ := (5/6-δ)*DN P p+δ*(1-p)*aN P p
def numT (δ p : ℝ) : ℝ := (5/6-δ)*DN P p+δ*(1-p)*(aN P p+cN P p)
/-- New cutoff and the new detector count exponent. -/
def tN (δ p : ℝ) : ℝ := numT P δ p/JN P δ p
def RNew (δ p : ℝ) : ℝ := 1-δ+(5/6-δ)*δ*(1-p)*cN P p/JN P δ p
theorem plane_lambda_pos : 0 < P.lambda := Count.plane_lambda_pos P
theorem plane_lower_gt : 41/100 < Count.lowerPlain P := (Count.plane_plain_window P).1
theorem plane_lower_le_upper : Count.lowerPlain P ≤ Count.mHi := by
  cases P <;> norm_num [Count.lowerPlain,Count.mHi,kappa0,widthLower,widthUpper,Count.Plane.B,Count.Plane.lambda,SourcePlane.B,SourcePlane.lambda]

theorem DN_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < DN P p := by
  cases P <;> norm_num [DN,Count.Plane.lambda,SourcePlane.lambda] <;> nlinarith
theorem aN_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < aN P p := by
  cases P <;> norm_num [aN,Count.Plane.lambda,SourcePlane.lambda] <;> nlinarith
theorem cN_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < cN P p := by
  cases P <;> norm_num [cN,Count.Plane.B,Count.Plane.lambda,SourcePlane.B,SourcePlane.lambda] <;> nlinarith

theorem affine_at_crossing (δ p t : ℝ) (hd : DN P p ≠ 0) :
    affineExp P δ p (t-rN P p t) = shortNew P δ p t := by
  have hr : rN P p t * DN P p = aN P p*t+2*p*(P.B)/(P.lambda)-p := div_mul_cancel₀ _ hd
  unfold affineExp shortNew 
  unfold DN aN at hr
  linear_combination δ * hr

theorem short_ge_base {δ p t : ℝ} (hδ : 0 ≤ δ) (hp1 : p ≤ 1) (hr : rN P p t ≤ 1) :
    1-δ ≤ shortNew P δ p t := by
  unfold shortNew 
  have : p+(1-p)*rN P p t ≤ 1 := by nlinarith
  nlinarith

theorem inverse_le_short {δ p t r : ℝ} (hδ : 0 ≤ δ) (hp1 : p ≤ 1) (hr : rN P p t ≤ r) :
    inverseExp δ p r ≤ shortNew P δ p t := by
  unfold inverseExp shortNew 
  have h1 := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1-p by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hδ]

/-- The affine plain exponent is nonincreasing in the plain length. -/
theorem affine_antitone {δ p m m' : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (hm : m' ≤ m) :
    affineExp P δ p m ≤ affineExp P δ p m' := by
  unfold affineExp 
  have hl := plane_lambda_pos P
  have hk : 4*p/(P.lambda) ≤ 2 := by
    rw [div_le_iff₀ hl]
    have hl2 : (1:ℝ) ≤ P.lambda := by
      cases P <;> norm_num [Count.Plane.lambda,SourcePlane.lambda]
    nlinarith
  have e : ∀ u : ℝ, 1-2*δ*u-2*(δ*p)*((P.B)-2*u)/(P.lambda) = 1-2*δ*p*(P.B)/(P.lambda)-δ*(2-4*p/(P.lambda))*u := by
    intro u; field_simp; ring
  rw [e m, e m']
  have : 0 ≤ δ*(2-4*p/(P.lambda)) := mul_nonneg hδ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hm this]

theorem affine_shift {δ p m : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (γ : ℝ)
    (hγ : 0 ≤ γ) : affineExp P δ p (m-γ) ≤ affineExp P δ p m+2*γ := by
  unfold affineExp 
  have hl := plane_lambda_pos P
  have hk : 0 ≤ 4*p/(P.lambda) := by positivity
  have e : ∀ u : ℝ, 1-2*δ*u-2*(δ*p)*((P.B)-2*u)/(P.lambda) = 1-2*δ*p*(P.B)/(P.lambda)-δ*(2-4*p/(P.lambda))*u := by
    intro u; field_simp; ring
  rw [e (m-γ), e m]
  have h2 : δ*(2-4*p/(P.lambda)) ≤ 2 := by nlinarith
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
    (hrN : 23/37 ≤ rN P x t) (hrN1 : rN P x t ≤ 1) (hmN : (Count.lowerPlain P)+γ ≤ t-rN P x t)
    (htail : oldPlainExp δ x κ Count.mHi ≤ shortNew P δ x t)
    (hI0 : B ≤ C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B ≤ C*U^(1-2*δ*m+ε))
    (hI : 23/37 ≤ r → r < 1 → ν < (1-r)/2 → B ≤ C*U^(inverseExp δ x r+ε))
    (hA : (Count.lowerPlain P) ≤ m → m ≤ Count.mHi → B ≤ C*U^(affineExp P δ x m+2*(δ*x)*ν+ε))
    (hP : Count.mHi ≤ m → m < 1/2 → ν < (1-2*m)/(6*κ) → B ≤ C*U^(oldPlainExp δ x κ m+ε)) :
    B ≤ C*U^(max (shortNew P δ x t) (longExp δ t)+ε+6*ν+5*γ) := by
  have hshort : shortNew P δ x t ≤ max (shortNew P δ x t) (longExp δ t) := le_max_left _ _
  have hlong : longExp δ t ≤ max (shortNew P δ x t) (longExp δ t) := le_max_right _ _
  have hbase : 1-δ ≤ shortNew P δ x t := short_ge_base P hδ (by linarith) hrN1
  have promote (q : ℝ) (hq : B ≤ C*U^q)
      (hqt : q ≤ max (shortNew P δ x t) (longExp δ t)+ε+6*ν+5*γ) :
      B ≤ C*U^(max (shortNew P δ x t) (longExp δ t)+ε+6*ν+5*γ) :=
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
  by_cases hrc : rN P x t ≤ r
  · by_cases hcap : (1-r)/2 ≤ ν
    · apply promote _ hI0
      have hh := mul_le_mul_of_nonneg_left hcap hδ
      have e : δ*((1-r)/2) = δ/2-δ*r/2 := by ring
      linarith
    · apply promote _ (hI (hrN.trans hrc) hr1' (lt_of_not_ge hcap))
      have := inverse_le_short P (δ:=δ) hδ (by linarith) hrc
      linarith
  have hrc' : r < rN P x t := lt_of_not_ge hrc
  have hmlo : t-rN P x t-γ ≤ m := by linarith
  by_cases hm : 1/2 ≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    linarith
  have hm' : m < 1/2 := lt_of_not_ge hm
  by_cases hmh : m ≤ Count.mHi
  · apply promote _ (hA (by linarith) hmh)
    have h1 := affine_antitone P (p:=x) hδ hx hx' hmlo
    have h2 := affine_shift P (p:=x) (m:=t-rN P x t) hδ (by linarith) hx hx' γ hγ
    have h3 := affine_at_crossing P δ x t (DN_pos P hx hx').ne'
    linarith
  have hmh' : Count.mHi ≤ m := (lt_of_not_ge hmh).le
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
theorem short_at_tN {δ p : ℝ} (hJ : JN P δ p ≠ 0) (hD : DN P p ≠ 0) :
    shortNew P δ p (tN P δ p) = RNew P δ p := by
  have hr : rN P p (tN P δ p) * DN P p = aN P p*tN P δ p+2*p*(P.B)/(P.lambda)-p := div_mul_cancel₀ _ hD
  have hT : tN P δ p * JN P δ p = numT P δ p := div_mul_cancel₀ _ hJ
  have hR : (RNew P δ p-1+δ) * JN P δ p = (5/6-δ)*δ*(1-p)*cN P p := by
    unfold RNew 
    rw [show 1-δ+(5/6-δ)*δ*(1-p)*cN P p/JN P δ p-1+δ = (5/6-δ)*δ*(1-p)*cN P p/JN P δ p by ring]
    exact div_mul_cancel₀ _ hJ
  have key : (shortNew P δ p (tN P δ p)-RNew P δ p) * (DN P p * JN P δ p) = 0 := by
    unfold shortNew 
    unfold JN numT DN aN cN at *
    linear_combination (-δ*(1-p)*((5/6-δ)*(3-p-4*p/(P.lambda))+δ*(1-p)*(2-4*p/(P.lambda)))) * hr
      + (-δ*(1-p)*(2-4*p/(P.lambda))) * hT + (-(3-p-4*p/(P.lambda))) * hR
  have hne : DN P p * JN P δ p ≠ 0 := mul_ne_zero hD hJ
  have := (mul_eq_zero.mp key).resolve_right hne
  linarith

theorem long_at_tN {δ p : ℝ} (hJ : JN P δ p ≠ 0) :
    longExp δ (tN P δ p) = RNew P δ p := by
  have hT : tN P δ p * JN P δ p = numT P δ p := div_mul_cancel₀ _ hJ
  have hR : (RNew P δ p-1+δ) * JN P δ p = (5/6-δ)*δ*(1-p)*cN P p := by
    unfold RNew 
    rw [show 1-δ+(5/6-δ)*δ*(1-p)*cN P p/JN P δ p-1+δ = (5/6-δ)*δ*(1-p)*cN P p/JN P δ p by ring]
    exact div_mul_cancel₀ _ hJ
  have key : (longExp δ (tN P δ p)-RNew P δ p) * JN P δ p = 0 := by
    unfold longExp
    unfold JN numT at *
    linear_combination (5/6-δ) * hT - hR
  have := (mul_eq_zero.mp key).resolve_right hJ
  linarith

theorem max_at_tN {δ p : ℝ} (hJ : JN P δ p ≠ 0) (hD : DN P p ≠ 0) :
    max (shortNew P δ p (tN P δ p)) (longExp δ (tN P δ p)) = RNew P δ p := by
  rw [short_at_tN P hJ hD, long_at_tN P hJ, max_self]


end OAI.SevenEighths.Target830.Physical.CountArithmetic
end
#print axioms OAI.SevenEighths.Target830.Physical.CountArithmetic.affine_count_bound
#print axioms OAI.SevenEighths.Target830.Physical.CountArithmetic.max_at_tN
