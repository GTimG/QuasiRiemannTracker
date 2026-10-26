/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted from the same-supported-witness case split of the earlier return. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Count.Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.LewkoStage2Return
noncomputable section
def plainCurve (B lam cap δ p m : ℝ) : ℝ :=
 max (1-2*δ*m-2*δ*p*cap) (1-2*δ*m-2*δ*p*(B-2*m)/lam)

theorem plainCurve_eq (B lam cap δ p m : ℝ) (hδ : 0≤δ) (hp : 0≤p) :
 plainCurve B lam cap δ p m = 1-2*δ*m-2*δ*p*min cap ((B-2*m)/lam) := by
 unfold plainCurve
 simp only [mul_div_assoc]
 rcases le_total cap ((B-2*m)/lam) with h|h
 · rw [min_eq_left h]
   apply max_eq_left
   have hh:=mul_le_mul_of_nonneg_left h (show 0≤2*δ*p by positivity)
   linarith
 · rw [min_eq_right h]
   apply max_eq_right
   have hh:=mul_le_mul_of_nonneg_left h (show 0≤2*δ*p by positivity)
   linarith

theorem plainCurve_antitone {B lam cap δ p m m' : ℝ}
 (hl : 1<lam) (hδ : 0≤δ) (hp : 0≤p) (hp1 : p≤1/2) (hm : m'≤m) :
 plainCurve B lam cap δ p m≤plainCurve B lam cap δ p m' := by
 apply max_le_max
 · nlinarith [mul_le_mul_of_nonneg_left hm hδ]
 · simpa only [QRH.Record12518109Count.Parameters.affineExp,mul_assoc] using
   QRH.Record12518109Count.Parameters.affine_antitone
    (⟨B,lam,0,0,hl⟩ : QRH.Record12518109Count.Parameters) hδ hp hp1 hm

theorem plainCurve_shift {B lam cap δ p m g : ℝ}
 (hl : 1<lam) (hδ : 0≤δ) (hδ1 : δ≤1) (hp : 0≤p) (hp1 : p≤1/2) (hg : 0≤g) :
 plainCurve B lam cap δ p (m-g)≤plainCurve B lam cap δ p m+2*g := by
 apply max_le
 · have hh : 1-2*δ*m-2*δ*p*cap≤plainCurve B lam cap δ p m := le_max_left _ _
   have hh' := mul_le_mul_of_nonneg_right hδ1 hg
   nlinarith
 · have hh : 1-2*δ*m-2*δ*p*(B-2*m)/lam≤plainCurve B lam cap δ p m := le_max_right _ _
   have hs := QRH.Record12518109Count.Parameters.affine_shift
    (⟨B,lam,0,0,hl⟩ : QRH.Record12518109Count.Parameters) (m:=m) hδ hδ1 hp hp1 g hg
   dsimp [QRH.Record12518109Count.Parameters.affineExp] at hs
   simp only [mul_assoc] at hs hh ⊢
   linarith

theorem common_witness_count_bound (B C U δ x κ t r m ε ν γ cross target mLo mHi : ℝ)
    (plain : ℝ → ℝ)
    (plain_antitone : ∀ u v, v≤u → plain u≤plain v)
    (plain_shift : ∀ u g, 0≤g → plain (u-g)≤plain u+2*g)
    (plain_crossing : plain (t-cross)≤target)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6)
    (hx : 0 ≤ x) (hx' : x ≤ 1/2) (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4)
    (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hleft : t-r-γ ≤ m) (hright : r ≤ t+γ)
    (hrN : 23/37 ≤ cross) (hrN1 : cross ≤ 1) (hmN : mLo+γ ≤ t-cross)
    (hcross : 1-δ*(x+(1-x)*cross)=target)
    (htail : (1-2*δ*mHi-2*(δ*x)*(1-2*mHi)/(6*κ)) ≤ target)
    (hI0 : B ≤ C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B ≤ C*U^(1-2*δ*m+ε))
    (hI : 23/37 ≤ r → r < 1 → ν < (1-r)/2 → B ≤ C*U^((1-δ*(x+(1-x)*r))+ε))
    (hA : mLo ≤ m → m ≤ mHi → B ≤ C*U^(plain m+2*(δ*x)*ν+ε))
    (hP : mHi ≤ m → m < 1/2 → ν < (1-2*m)/(6*κ) → B ≤ C*U^((1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ))+ε)) :
    B ≤ C*U^(max (target) ((1-δ+(5/6-δ)*(t-1)))+ε+6*ν+5*γ) := by
  have hshort : target ≤ max (target) ((1-δ+(5/6-δ)*(t-1))) := le_max_left _ _
  have hlong : (1-δ+(5/6-δ)*(t-1)) ≤ max (target) ((1-δ+(5/6-δ)*(t-1))) := le_max_right _ _
  have hbase : 1-δ ≤ target := by
    rw [←hcross]
    nlinarith [mul_le_mul_of_nonneg_left hrN1 (show 0≤1-x by linarith)]
  have promote (q : ℝ) (hq : B ≤ C*U^q)
      (hqt : q ≤ max (target) ((1-δ+(5/6-δ)*(t-1)))+ε+6*ν+5*γ) :
      B ≤ C*U^(max (target) ((1-δ+(5/6-δ)*(t-1)))+ε+6*ν+5*γ) :=
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
    have hl2 : (1-δ+(5/6-δ)*(t-1)) = 1-δ+(5/6-δ)*(t-1) := rfl
    have e1 : (1+5*r)/6-δ*r = 1/6+(5/6-δ)*r := by ring
    have e2 : (5/6-δ)*(t+γ) = (5/6-δ)*(t-1)+(5/6-δ)+(5/6-δ)*γ := by ring
    linarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6) = 1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : cross ≤ r
  · by_cases hcap : (1-r)/2 ≤ ν
    · apply promote _ hI0
      have hh := mul_le_mul_of_nonneg_left hcap hδ
      have e : δ*((1-r)/2) = δ/2-δ*r/2 := by ring
      linarith
    · apply promote _ (hI (hrN.trans hrc) hr1' (lt_of_not_ge hcap))
      have hv := mul_le_mul_of_nonneg_left hrc (mul_nonneg hδ (show 0≤1-x by linarith))
      have hi : 1-δ*(x+(1-x)*r)≤target := by rw [←hcross];nlinarith
      linarith
  have hrc' : r < cross := lt_of_not_ge hrc
  have hmlo : t-cross-γ ≤ m := by linarith
  by_cases hm : 1/2 ≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    linarith
  have hm' : m < 1/2 := lt_of_not_ge hm
  by_cases hmh : m ≤ mHi
  · apply promote _ (hA (by linarith) hmh)
    have h1 := plain_antitone m (t-cross-γ) hmlo
    have h2 := plain_shift (t-cross) γ hγ
    have h3 := plain_crossing
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
    have hold := QRH.Record12518109Count.Parameters.old_antitone
      (⟨0,2,0,0,by norm_num⟩ : QRH.Record12518109Count.Parameters)
      (κ:=κ) (δ:=δ) (p:=x) hδ hx hx' hk hmh'
    dsimp [QRH.Record12518109Count.Parameters.oldPlainExp] at hold
    linarith

end
end QRH.LewkoStage2Return
#print axioms QRH.LewkoStage2Return.common_witness_count_bound
