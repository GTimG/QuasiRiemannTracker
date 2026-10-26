/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.ConeCertificates
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace OAI.SevenEighths.Record12518109Natural.Valuation
noncomputable section
open scoped Classical BigOperators

theorem affine_interval_bound {f : ℝ → ℝ} {a b A S M r : ℝ}
    (hf : ∀ z,f z=A+z*S) (hr : r ∈ Set.Icc a b)
    (ha : f a ≤ M) (hb : f b ≤ M) : f r ≤ M := by
  simp only [hf] at ha hb ⊢
  rcases le_total 0 S with h | h
  · have := mul_le_mul_of_nonneg_right hr.2 h
    linarith
  · have := mul_le_mul_of_nonpos_right hr.1 h
    linarith

theorem common_weighted_bound {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t)
    (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t)
    (rho : ℝ) (hr : 1/4 ≤ rho) (hrhi : rho ≤ 23/50) :
    commonValue rho (weighted s i j w) ≤
      max (3/19) (4*rho-5/4)*weighted s i j w 0 := by
  let x := weighted s i j w
  have h0 := common_endpoint0 s i j w hw hi hj
  have h1 := common_endpoint1 s i j w hw hi hj
  have h2 := common_endpoint2 s i j w hw hi hj
  change commonValue (1/4) x ≤ (3/19)*x 0 at h0
  change commonValue (107/304) x ≤ (3/19)*x 0 at h1
  change commonValue (23/50) x ≤ (59/100)*x 0 at h2
  change commonValue rho x ≤ max (3/19) (4*rho-5/4)*x 0
  by_cases hs : rho ≤ 107/304
  · rw [max_eq_left (by linarith : 4*rho-5/4 ≤ (3/19:ℝ))]
    exact affine_interval_bound (f:=fun z => commonValue z x)
      (a:=1/4) (b:=107/304) (r:=rho) (M:=(3/19)*x 0)
      (fun z => commonValue_affine z x) ⟨hr,hs⟩ h0 h1
  · have hs' : (107/304:ℝ) ≤ rho := (lt_of_not_ge hs).le
    rw [max_eq_right (by linarith : (3/19:ℝ) ≤ 4*rho-5/4)]
    have hf : ∀ z,commonValue z x-(4*z-5/4)*x 0=
        commonValue 0 x+(5/4)*x 0+
          z*(-max (x 0-x 1) 0-x 3+x 4-4*x 0) := by
      intro z
      rw [commonValue_affine]
      ring
    have hh := affine_interval_bound (f:=fun z => commonValue z x-(4*z-5/4)*x 0)
      (a:=107/304) (b:=23/50) (r:=rho) (M:=0) hf ⟨hs',hrhi⟩
      (by norm_num;linarith [h1]) (by norm_num;linarith [h2])
    linarith

theorem common_weighted_saving {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t)
    (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t)
    (rho delta E : ℝ) (hr : 1/4 ≤ rho) (hrhi : rho ≤ 23/50) :
    let x := weighted s i j w
    firstCommon rho delta (x 0) (x 1) (x 3) E (x 4) (x 5)-
      surplus (x 0) (x 1) (x 2) (x 3) ≤
      -(delta-max (3/19) (4*rho-5/4))*x 0-E := by
  have hh := common_weighted_bound s i j w hw hi hj rho hr hrhi
  dsimp only
  unfold commonValue firstCommon at *
  nlinarith

theorem rho_eq_local (delta : ℝ) : rho delta=LocalMoment.unmarkedDensity delta := rfl

theorem rho_extended_range {delta : ℝ} (hd : 405/662 ≤ delta) (hdhi : delta ≤ 3/4) :
    1/4 ≤ rho delta ∧ rho delta ≤ 23/50 := by
  have hden : 0 < 3*(5-2*delta) := by linarith
  have hlo : 10*delta/(3*(5-2*delta)) ≤ 3/4 := by
    rw [div_le_iff₀ hden]
    linarith
  have hhi : 27/50 ≤ 10*delta/(3*(5-2*delta)) := by
    rw [le_div_iff₀ hden]
    linarith
  unfold rho
  constructor <;> linarith

end
end OAI.SevenEighths.Record12518109Natural.Valuation
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.common_weighted_saving
