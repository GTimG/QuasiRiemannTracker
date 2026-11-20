/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from Hailey Collet's `Record1252270103Return/CountCurve.lean` (`common_witness_count_bound`,
Apache-2.0): the same-supported-witness case split with the improved inverse and ordinary pieces. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountCurve

/-!
# Return.ImprovedCurve

`improved_witness_count_bound` is `common_witness_count_bound` for an improved window. With
`a = x (1+2 g0)`, `k = 1 - x (1+2 g1)` (`x` the amplitude ratio), the free width `r` of a witness and its
plain length `m ≥ t - r - γ`:

* `r ≥ 1`: unmarked inverse (`hI0`) and the long piece;
* `Top ≤ r < 1`: native marked inverse (`hI`), paid at `Top` (`hnat`);
* `cross ≤ r < Top`: improved inverse (`hJ`, exponent `1 - δ (a + k r)`), paid at `cross` (`hcross`);
* `r < cross`: `m ≥ t - cross - γ`; `m ≥ 1/2` unmarked plain; `2m ≤ Top` improved ordinary (`hO`,
  exponent `1 - δ (a + 2 m k)`, paid at `m = t - cross` up to `2γ`); `Top < 2m`, `m ≤ mHi` the native
  plain curve (`hA`, paid at `Top/2`); `m > mHi` the natural tail.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qrh.MarkedAnchor.Return
noncomputable section

theorem improved_witness_count_bound
    (B C U δ x κ t r m ε ν γ cross target mHi Lft Top a k : ℝ)
    (plain : ℝ → ℝ)
    (plain_antitone : ∀ u v, v≤u → plain u≤plain v)
    (plain_top : plain (Top/2)≤target)
    (hC : 0≤C) (hU : 1≤U) (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hν : 0≤ν) (hγ : 0≤γ)
    (hleft : t-r-γ≤m) (hright : r≤t+γ)
    (hTop : 23/37≤Top) (hTop1 : Top≤1)
    (hkk : 0≤k) (hkk1 : k≤1)
    (hcrossL : Lft≤cross) (hplainL : Lft≤2*(t-cross-γ))
    (hcross : 1-δ*(a+k*cross)=target)
    (hord : 1-δ*(a+2*(t-cross)*k)≤target)
    (hnat : 1-δ*(x+(1-x)*Top)≤target)
    (htail : (1-2*δ*mHi-2*(δ*x)*(1-2*mHi)/(6*κ))≤target)
    (hI0 : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B≤C*U^(1-2*δ*m+ε))
    (hI : 23/37≤r → r<1 → ν<(1-r)/2 → B≤C*U^((1-δ*(x+(1-x)*r))+ε))
    (hJ : Lft≤r → r≤Top → B≤C*U^((1-δ*(a+k*r))+ε))
    (hO : Lft≤2*m → 2*m≤Top → B≤C*U^((1-δ*(a+2*m*k))+ε))
    (hA : Top/2≤m → m≤mHi → B≤C*U^(plain m+2*(δ*x)*ν+ε))
    (hP : mHi≤m → m<1/2 → ν<(1-2*m)/(6*κ) →
      B≤C*U^((1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ))+ε)) :
    B≤C*U^(max target (1-δ+(5/6-δ)*(t-1))+ε+6*ν+5*γ) := by
  have hshort : target≤max target (1-δ+(5/6-δ)*(t-1)) := le_max_left _ _
  have hbase : 1-δ≤target := by
    have h1 : x+(1-x)*Top≤1 := by nlinarith
    nlinarith
  have promote (q : ℝ) (hq : B≤C*U^q)
      (hqt : q≤max target (1-δ+(5/6-δ)*(t-1))+ε+6*ν+5*γ) :
      B≤C*U^(max target (1-δ+(5/6-δ)*(t-1))+ε+6*ν+5*γ) :=
    hq.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hqt) hC)
  have hdx : δ*x≤(5/6)*(1/2) := mul_le_mul hδ' hx' hx (by norm_num)
  have hδν : 2*(δ*x)*ν≤1*ν := mul_le_mul_of_nonneg_right (by linarith) hν
  have h2δν : 2*δ*ν≤2*ν := by
    have := mul_le_mul_of_nonneg_right hδ' hν; linarith
  by_cases hr1 : 1≤r
  · have hmax : max 1 ((1+5*r)/6)=(1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hlong : 1-δ+(5/6-δ)*(t-1)≤max target (1-δ+(5/6-δ)*(t-1)) := le_max_right _ _
    have hh := mul_le_mul_of_nonneg_left hright (show 0≤5/6-δ by linarith)
    have hcγ : (5/6-δ)*γ≤1*γ := mul_le_mul_of_nonneg_right (by linarith) hγ
    have e1 : (1+5*r)/6-δ*r=1/6+(5/6-δ)*r := by ring
    have e2 : (5/6-δ)*(t+γ)=(5/6-δ)*(t-1)+(5/6-δ)+(5/6-δ)*γ := by ring
    linarith
  have hr1' : r<1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6)=1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrT : Top≤r
  · by_cases hcap : (1-r)/2≤ν
    · apply promote _ hI0
      have hh := mul_le_mul_of_nonneg_left hcap hδ
      have e : δ*((1-r)/2)=δ/2-δ*r/2 := by ring
      linarith
    · apply promote _ (hI (hTop.trans hrT) hr1' (lt_of_not_ge hcap))
      have hv := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hrT) (mul_nonneg hδ (show 0≤1-x by linarith))
      have hi : 1-δ*(x+(1-x)*r)≤target := by nlinarith
      linarith
  have hrT' : r<Top := lt_of_not_ge hrT
  by_cases hrc : cross≤r
  · apply promote _ (hJ (hcrossL.trans hrc) hrT'.le)
    have hv := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hrc) (mul_nonneg hδ hkk)
    have hi : 1-δ*(a+k*r)≤target := by nlinarith
    linarith
  have hrc' : r<cross := lt_of_not_ge hrc
  have hmlo : t-cross-γ≤m := by linarith
  by_cases hm : 1/2≤m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    linarith
  have hm' : m<1/2 := lt_of_not_ge hm
  by_cases hmT : 2*m≤Top
  · apply promote _ (hO (by linarith) hmT)
    have hv := mul_le_mul_of_nonneg_left (show 2*(t-cross-γ)≤2*m by linarith) (mul_nonneg hδ hkk)
    have hdk : δ*k*(2*γ)≤1*(2*γ) := mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul hδ' hkk1 hkk (by norm_num : (0:ℝ)≤5/6)]) (by linarith)
    have e1 : 1-δ*(a+2*m*k)=1-δ*a-δ*k*(2*m) := by ring
    have e2 : 1-δ*(a+2*(t-cross)*k)=1-δ*a-δ*k*(2*(t-cross-γ))-δ*k*(2*γ) := by ring
    linarith
  have hmT' : Top/2≤m := by linarith
  by_cases hmh : m≤mHi
  · apply promote _ (hA hmT' hmh)
    have h1 := plain_antitone m (Top/2) hmT'
    linarith
  have hmh' : mHi≤m := (lt_of_not_ge hmh).le
  by_cases hcap : (1-2*m)/(6*κ)≤ν
  · apply promote _ hP0
    have hh := (div_le_iff₀ (show 0<6*κ by linarith)).mp hcap
    have hk6 : ν*(6*κ)≤ν*(9/2) := mul_le_mul_of_nonneg_left (by linarith) hν
    have hm6 : 1-2*m≤6*ν := by linarith
    have hh' := mul_le_mul_of_nonneg_left hm6 hδ
    have h6 : δ*(6*ν)≤6*ν := by
      have := mul_le_mul_of_nonneg_right hδ' (show 0≤6*ν by linarith); linarith
    have e : δ*(1-2*m)=δ-2*δ*m := by ring
    linarith
  · apply promote _ (hP hmh' hm' (lt_of_not_ge hcap))
    have hold := QRH.Record12518109Count.Parameters.old_antitone
      (⟨0,2,0,0,by norm_num⟩ : QRH.Record12518109Count.Parameters)
      (κ:=κ) (δ:=δ) (p:=x) hδ hx hx' hk hmh'
    dsimp [QRH.Record12518109Count.Parameters.oldPlainExp] at hold
    linarith

end
end Qrh.MarkedAnchor.Return
