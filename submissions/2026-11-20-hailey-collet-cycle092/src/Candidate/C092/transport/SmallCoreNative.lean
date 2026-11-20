/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uses the genuine Bebel/Sil/Collet native positive source and the original
OpenAI/Collet whole-slot initial energy. Inherited source notices remain in imports. -/
import Candidate.C092.transport.NativeStrip

set_option autoImplicit false
namespace QRH.Cycle092.SmallCore
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.NativeStrip
open QRH.Record12518109Source QRH.Record12518109Existence

/-- Exactly twice the largest original ordinary cap lambda*Y. -/
def radiusMin : ℝ := 5589/6250
def nativeCost : ℝ := 1/1000000000
/-- Absolute whole-slot quota, with a strict native-source collar. -/
def quota (n y V : ℝ) : ℝ := (V-n-y)/2-1/1000

theorem quota_guards {n y V : ℝ}
    (hy0 : QRH.Cycle090.sourceY0 ≤ y) (hy1 : y ≤ QRH.Cycle090.sourceY) (hn0 : y ≤ n) (hn1 : n ≤ QRH.Cycle090.sourceRatio*y)
    (hV0 : radiusMin ≤ V) (hV1 : V ≤ 98/100) :
    0<V ∧ 0<quota n y V ∧ n/V ≤ 1/2 ∧ y/V ≤ 1/2 ∧ quota n y V/V ≤ 1/8 := by
  have hnc : n ≤ QRH.Cycle090.sourceRatio*QRH.Cycle090.sourceY := hn1.trans
    (mul_le_mul_of_nonneg_left hy1 (by norm_num [QRH.Cycle090.sourceRatio]))
  have hV : 0<V := (by norm_num [radiusMin] : (0 : ℝ)<radiusMin).trans_le hV0
  refine ⟨hV,?_,?_,?_,?_⟩
  · dsimp [quota]
    norm_num [QRH.Cycle090.sourceY0,QRH.Cycle090.sourceY,QRH.Cycle090.sourceRatio,radiusMin] at hy0 hy1 hn0 hnc hV0 ⊢
    linarith
  · apply (div_le_iff₀ hV).mpr
    norm_num [QRH.Cycle090.sourceRatio,QRH.Cycle090.sourceY,radiusMin] at hnc hV0 ⊢
    linarith
  · apply (div_le_iff₀ hV).mpr
    norm_num [QRH.Cycle090.sourceY,radiusMin] at hy1 hV0 ⊢
    linarith
  · apply (div_le_iff₀ hV).mpr
    norm_num [quota,QRH.Cycle090.sourceY0] at hy0 ⊢
    linarith

/-- Every retained native rectangle is admissible to one actual fixed source.
No earlier-source or unproved moment contract is used. -/
theorem native_admissible {n y V x z s : ℝ}
    (hy0 : QRH.Cycle090.sourceY0 ≤ y) (hy1 : y ≤ QRH.Cycle090.sourceY) (hn0 : y ≤ n) (hn1 : n ≤ QRH.Cycle090.sourceRatio*y)
    (hV0 : radiusMin ≤ V) (hV1 : V ≤ 98/100)
    (hb : Box (n/V) (y/V) (quota n y V/V) x z s) :
    (Qrh.TwoSlot.AnchorContinuum.PositiveSource.face nativeCost).Admissible x z s 1 := by
  have hg := quota_guards hy0 hy1 hn0 hn1 hV0 hV1
  obtain ⟨hx,hz,hpair,hs,hsl⟩ := hb
  have hxhi : x ≤ 1/2 := by rcases hpair with h | h <;> linarith [h.1,h.2,hg.2.2.1,hg.2.2.2.1]
  have hzhi : z ≤ 1/2 := by rcases hpair with h | h <;> linarith [h.1,h.2,hg.2.2.1,hg.2.2.2.1]
  have hsum : x+z ≤ n/V+y/V := by rcases hpair with h | h <;> linarith [h.1,h.2]
  have hq : quota n y V ≤ V/8 := by
    have h := (div_le_iff₀ hg.1).mp hg.2.2.2.2
    linarith
  have hnum : n+y+(2+10*nativeCost)*quota n y V ≤ V*(1-nativeCost) := by
    have hident : n+y+2*quota n y V=V-1/500 := by dsimp [quota]; ring
    dsimp [nativeCost] at *
    nlinarith
  have hbudget : n/V+y/V+(2+10*nativeCost)*(quota n y V/V) ≤ 1-nativeCost := by
    rw [show n/V+y/V+(2+10*nativeCost)*(quota n y V/V)=
      (n+y+(2+10*nativeCost)*quota n y V)/V by ring]
    exact (div_le_iff₀ hg.1).mpr (by nlinarith [hnum])
  have hsl' := mul_le_mul_of_nonneg_left hsl
    (show 0 ≤ 2+10*nativeCost by norm_num [nativeCost])
  dsimp [SourceFace.Admissible,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face]
  simp only [mul_one]
  refine ⟨hx,hxhi,hz,hzhi,hs,?_,by linarith⟩
  have hsq := hsl.trans hg.2.2.2.2
  norm_num [nativeCost] at *
  linarith

theorem native_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    UniformUnitFaceSource (Qrh.TwoSlot.AnchorContinuum.PositiveSource.face nativeCost) :=
  Qrh.TwoSlot.AnchorContinuum.PositiveSource.source
    (by norm_num [nativeCost]) (by norm_num [nativeCost]) hβ

/-- The native erasure cost pays P2 throughout the closed small-core cohort,
even for response up to one. The actual energy application is in SmallCoreEnergy. -/
theorem native_price {n y V e L rounding : ℝ}
    (hy0 : QRH.Cycle090.sourceY0 ≤ y) (hy1 : y ≤ QRH.Cycle090.sourceY)
    (hV0 : radiusMin ≤ V) (hV1 : V ≤ 98/100)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hL : L ≤ QRH.Cycle090.sourceWidth n y-(u : ℝ)) (hr : rounding ≤ 1/100000) :
    e*max 0 (L-quota n y V+rounding)<
      (u : ℝ)-(rho : ℝ)/2+(5/6)*max 0 ((H : ℝ)-V) := by
  have hg := sourceGain_antitone hy0 hy1
  have hg0 : QRH.Cycle090.sourceGain QRH.Cycle090.sourceY0 ≤ (3/1000 : ℝ) := by
    norm_num [QRH.Cycle090.sourceGain,QRH.Cycle090.sourceY0,QRH.Cycle090.sourceSeam,QRH.Cycle090.lowerGain,QRH.Cycle090.upperGain,QRH.Cycle090.sourceY]
  have hleft : L-quota n y V+rounding ≤ (1-V)/2+401/100000 := by
    dsimp [quota,QRH.Cycle090.sourceWidth] at *
    norm_num [u] at hL
    linarith
  have hnonneg : 0 ≤ (1-V)/2+401/100000 := by linarith
  have hmax := max_le hnonneg hleft
  have he := mul_le_mul he1 hmax (le_max_left _ _) (by norm_num : (0 : ℝ) ≤ 1)
  have hH : 0 ≤ (H : ℝ)-V := by norm_num [H,u] at *; linarith
  rw [max_eq_right hH]
  norm_num [u,rho,H] at *
  linarith

end
end QRH.Cycle092.SmallCore
#print axioms QRH.Cycle092.SmallCore.native_admissible
#print axioms QRH.Cycle092.SmallCore.native_source
