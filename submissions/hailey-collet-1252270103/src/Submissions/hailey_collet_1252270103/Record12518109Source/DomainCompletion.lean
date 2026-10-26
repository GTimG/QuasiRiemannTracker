/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.InitialMoment

set_option autoImplicit false

namespace QRH.Record12518109Source
noncomputable section

/-- The scalar capacity of the natural initial moment. -/
def NaturalCapacity (K m₁ m₂ z Q : ℝ) : Prop := m₁+m₂+K*z ≤ Q

/-- R17 is imposed before puncture/divisor deletion. Each descendant only
shortens these three coordinates. -/
structure DownwardCaps (f : SourceFace) (K m₁ m₂ z Q : ℝ) : Prop where
  K_nonneg : 0 ≤ K
  lambda_nonneg : 0 ≤ f.lam
  plain₁ : m₁ ≤ f.plainHi*Q
  plain₂ : m₂ ≤ f.plainHi*Q
  slot : z ≤ f.slotHi*Q
  affine : m₁+m₂+f.lam*z ≤ f.B*Q
  natural_slot : m₁+m₂+K*(f.slotLo*Q) ≤ Q
  natural_plain : max m₁ m₂+f.plainLo*Q+K*z ≤ Q

/-- Every coordinatewise shortening is admitted by the previous affine face
or the natural capacity. This includes zero slots and simultaneous lower-edge
crossings. Analytic moment estimates are supplied separately. -/
theorem downward_completion {f : SourceFace} {K m₁ m₂ z Q : ℝ}
    (h : DownwardCaps f K m₁ m₂ z Q)
    {n₁ n₂ s : ℝ} (hn₁ : n₁ ≤ m₁) (hn₂ : n₂ ≤ m₂) (hs : s ≤ z) :
    f.Admissible n₁ n₂ s Q ∨ NaturalCapacity K n₁ n₂ s Q := by
  by_cases hslot : f.slotLo*Q ≤ s
  · by_cases hp₁ : f.plainLo*Q ≤ n₁
    · by_cases hp₂ : f.plainLo*Q ≤ n₂
      · left
        refine ⟨hp₁,hn₁.trans h.plain₁,hp₂,hn₂.trans h.plain₂,
          hslot,hs.trans h.slot,?_⟩
        have := mul_le_mul_of_nonneg_left hs h.lambda_nonneg
        linarith [h.affine]
      · right
        have hp₂' := le_of_lt (lt_of_not_ge hp₂)
        have hm₁ := le_max_left m₁ m₂
        have hKs := mul_le_mul_of_nonneg_left hs h.K_nonneg
        dsimp only [NaturalCapacity]
        linarith [h.natural_plain]
    · right
      have hp₁' := le_of_lt (lt_of_not_ge hp₁)
      have hm₂ := le_max_right m₁ m₂
      have hKs := mul_le_mul_of_nonneg_left hs h.K_nonneg
      dsimp only [NaturalCapacity]
      linarith [h.natural_plain]
  · right
    have hs' := le_of_lt (lt_of_not_ge hslot)
    have hKs := mul_le_mul_of_nonneg_left hs' h.K_nonneg
    dsimp only [NaturalCapacity]
    linarith [h.natural_slot]

/-- R20 caps the actual first geometry, before subsequent shortening. -/
structure FirstGeometry (F u t mmax P Q : ℝ) : Prop where
  radius_lower : F-u ≤ Q
  radius_upper : Q ≤ F+5*u/4
  plain_lower : t-u ≤ P
  plain_upper : P ≤ t

def firstSlotCap (f : SourceFace) (P Q : ℝ) : ℝ := (f.B*Q-P)/f.lam

/-- Six domain reserves imply R17 for the one fixed first-geometry cap.
The scalar interval certificates establish these reserves uniformly. -/
theorem first_cap_admission {f : SourceFace} {K F u t mmax P Q m₁ m₂ : ℝ}
    (hK : 0 ≤ K) (hL : 0 < f.lam)
    (hu : 0 ≤ f.plainHi)
    (hQ : FirstGeometry F u t mmax P Q)
    (hP : m₁+m₂ = P) (hm₁ : m₁ ≤ mmax) (hm₂ : m₂ ≤ mmax)
    (hBLo : 0 ≤ f.B-f.lam*f.slotLo)
    (hBHi : 0 ≤ f.B-f.lam*f.slotHi)
    (hNLo : 0 ≤ 1-K*f.slotLo)
    (hCoeff : 1-f.plainLo-K*f.B/f.lam ≤ 0)
    (hslotLo : t ≤ (f.B-f.lam*f.slotLo)*(F-u))
    (hslotHi : (f.B-f.lam*f.slotHi)*(F+5*u/4) ≤ t-u)
    (hplain : mmax ≤ f.plainHi*(F-u))
    (hnaturalSlot : t ≤ (1-K*f.slotLo)*(F-u))
    (hnaturalPlain : mmax ≤
      (1-f.plainLo-K*f.B/f.lam)*(F+5*u/4)+(K/f.lam)*(t-u)) :
    f.slotLo*Q ≤ firstSlotCap f P Q ∧
      firstSlotCap f P Q ≤ f.slotHi*Q ∧
      DownwardCaps f K m₁ m₂ (firstSlotCap f P Q) Q := by
  have hL0 := ne_of_gt hL
  have hz : f.lam*firstSlotCap f P Q = f.B*Q-P := by
    dsimp [firstSlotCap]
    field_simp
  have hlo : f.slotLo*Q ≤ firstSlotCap f P Q := by
    have := mul_le_mul_of_nonneg_left hQ.radius_lower hBLo
    apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith only [hz,hslotLo,this,hQ.plain_upper]
  have hhi : firstSlotCap f P Q ≤ f.slotHi*Q := by
    have := mul_le_mul_of_nonneg_left hQ.radius_upper hBHi
    apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith only [hz,hslotHi,this,hQ.plain_lower]
  refine ⟨hlo,hhi,⟨hK,hL.le,?_,?_,hhi,?_,?_,?_⟩⟩
  · exact hm₁.trans (hplain.trans (mul_le_mul_of_nonneg_left hQ.radius_lower hu))
  · exact hm₂.trans (hplain.trans (mul_le_mul_of_nonneg_left hQ.radius_lower hu))
  · linarith only [hz,hP]
  · have := mul_le_mul_of_nonneg_left hQ.radius_lower hNLo
    nlinarith only [hP,hnaturalSlot,this,hQ.plain_upper]
  · have hc := mul_le_mul_of_nonpos_left hQ.radius_upper hCoeff
    have hkp : (K/f.lam)*(t-u) ≤ (K/f.lam)*P :=
      mul_le_mul_of_nonneg_left hQ.plain_lower (div_nonneg hK hL.le)
    have hm : max m₁ m₂ ≤ mmax := max_le hm₁ hm₂
    have hid : Q-(max m₁ m₂+f.plainLo*Q+K*firstSlotCap f P Q) =
        (1-f.plainLo-K*f.B/f.lam)*Q+(K/f.lam)*P-max m₁ m₂ := by
      dsimp [firstSlotCap]
      field_simp
      <;> ring
    linarith only [hc,hkp,hm,hnaturalPlain,hid]

end
end QRH.Record12518109Source

#print axioms QRH.Record12518109Source.downward_completion
#print axioms QRH.Record12518109Source.first_cap_admission
