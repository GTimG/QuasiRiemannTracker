/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Tactic

/-! Exact affine detector minimax with both plain-capacity branches.
The estimates supplied to this finite lemma must refer to the same rows. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

/-- If the inverse arm is larger than the target, both plain arms are
small. The maximum of the two plain branches cannot be dropped. -/
theorem two_plain_minimax {a b c₁ d₁ c₂ d₂ r m t R : ℝ}
    (hb : 0 < b) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hlength : t ≤ r+m)
    (hcross₁ : d₁*a+b*c₁-b*d₁*t ≤ (b+d₁)*R)
    (hcross₂ : d₂*a+b*c₂-b*d₂*t ≤ (b+d₂)*R) :
    min (a-b*r) (max (c₁-d₁*m) (c₂-d₂*m)) ≤ R := by
  by_cases hi : a-b*r ≤ R
  · exact (min_le_left _ _).trans hi
  · apply (min_le_right _ _).trans
    apply max_le
    · nlinarith [mul_nonneg hd₁ (sub_nonneg.mpr hlength)]
    · nlinarith [mul_nonneg hd₂ (sub_nonneg.mpr hlength)]

/-- Branches for an original response slope v. Only the auxiliary count
pays the full repeated mark capacity; the physical response is unchanged. -/
def inverseArm (ν v r : ℝ) : ℝ := 1-v/2-(ν-v/2)*r
def plainCapArm (c ν v m : ℝ) : ℝ := 1-v*c-2*ν*m
def plainBudgetArm (B L ν v m : ℝ) : ℝ :=
  1-v*B/L-2*(ν-v/L)*m
def longArm (ν t : ℝ) : ℝ := 1/6+(5/6-ν)*t

/-- The repeated-mark short detector count, conditional solely on the
literal inverse and BOTH plain moment bounds and their crossing payments. -/
theorem short_count {B L c ν v r m t R count : ℝ}
    (hν : 0 < ν-v/2) (hν0 : 0 ≤ ν) (hνL : 0 ≤ ν-v/L)
    (hlength : t ≤ r+m)
    (hi : count ≤ inverseArm ν v r)
    (hp : count ≤ max (plainCapArm c ν v m) (plainBudgetArm B L ν v m))
    (hc : (2*ν)*(1-v/2)+(ν-v/2)*(1-v*c)-
      (ν-v/2)*(2*ν)*t ≤ (ν-v/2+2*ν)*R)
    (hB : (2*(ν-v/L))*(1-v/2)+(ν-v/2)*(1-v*B/L)-
      (ν-v/2)*(2*(ν-v/L))*t ≤ (ν-v/2+2*(ν-v/L))*R) :
    count ≤ R := by
  apply (le_min hi hp).trans
  exact two_plain_minimax hν (by linarith) (by linarith) hlength hc hB

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

def crossingDen (ν p A : ℝ) : ℝ :=
  (5/6-ν)*(A+1-p)+ν*(1-p)*A
def crossingCut (ν p A Z : ℝ) : ℝ :=
  1+ν*(1-p)*(1-Z)/crossingDen ν p A
def crossingRate (ν p A Z : ℝ) : ℝ :=
  1-ν+(5/6-ν)*ν*(1-p)*(1-Z)/crossingDen ν p A

/-- The common short/long crossing is an exact rational identity, without
requiring an optimizer or identifying one plain branch as binding. -/
theorem crossing_identity (ν p A Z : ℝ) (hJ : crossingDen ν p A ≠ 0) :
    A*(1-ν*p)+(1-p)*(1-ν*Z)-ν*(1-p)*A*crossingCut ν p A Z =
      (A+1-p)*crossingRate ν p A Z := by
  unfold crossingCut crossingRate
  apply mul_right_cancel₀ hJ
  field_simp [hJ]
  unfold crossingDen
  ring

theorem long_at_crossing (ν p A Z : ℝ) :
    longArm ν (crossingCut ν p A Z) = crossingRate ν p A Z := by
  unfold longArm crossingCut crossingRate
  ring

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

private theorem crossing_payment {a b c d t t₀ R R₀ : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : t₀ ≤ t) (hR : R₀ ≤ R)
    (heq : d*a+b*c-b*d*t₀=(b+d)*R₀) :
    d*a+b*c-b*d*t ≤ (b+d)*R := by
  have h₁ := mul_nonneg (mul_nonneg hb hd) (sub_nonneg.mpr ht)
  have h₂ := mul_nonneg (add_nonneg hb hd) (sub_nonneg.mpr hR)
  nlinarith

/-- Both short plain branches are controlled at the larger of their two
cutoffs. All three witnesses remain on the same event. -/
theorem at_maximum_cutoff {ν p A₁ Z₁ A₂ Z₂ r m count : ℝ}
    (hν : 0 < ν) (hp : p < 1) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hJ₁ : crossingDen ν p A₁ ≠ 0) (hJ₂ : crossingDen ν p A₂ ≠ 0)
    (hlength : max (crossingCut ν p A₁ Z₁) (crossingCut ν p A₂ Z₂) ≤ r+m)
    (hi : count ≤ 1-ν*p-ν*(1-p)*r)
    (hpcount : count ≤ max (1-ν*Z₁-ν*A₁*m) (1-ν*Z₂-ν*A₂*m)) :
    count ≤ max (crossingRate ν p A₁ Z₁) (crossingRate ν p A₂ Z₂) := by
  have hb : 0 < ν*(1-p) := mul_pos hν (by linarith)
  have identity₁ : (ν*A₁)*(1-ν*p)+(ν*(1-p))*(1-ν*Z₁)-
      (ν*(1-p))*(ν*A₁)*crossingCut ν p A₁ Z₁ =
      (ν*(1-p)+ν*A₁)*crossingRate ν p A₁ Z₁ := by
    have hh := congrArg (fun x : ℝ => ν*x) (crossing_identity ν p A₁ Z₁ hJ₁)
    nlinarith only [hh]
  have identity₂ : (ν*A₂)*(1-ν*p)+(ν*(1-p))*(1-ν*Z₂)-
      (ν*(1-p))*(ν*A₂)*crossingCut ν p A₂ Z₂ =
      (ν*(1-p)+ν*A₂)*crossingRate ν p A₂ Z₂ := by
    have hh := congrArg (fun x : ℝ => ν*x) (crossing_identity ν p A₂ Z₂ hJ₂)
    nlinarith only [hh]
  apply (le_min hi hpcount).trans
  exact two_plain_minimax hb (mul_nonneg hν.le hA₁) (mul_nonneg hν.le hA₂)
    hlength
    (crossing_payment hb.le (mul_nonneg hν.le hA₁) (le_max_left _ _)
      (le_max_left _ _) identity₁)
    (crossing_payment hb.le (mul_nonneg hν.le hA₂) (le_max_right _ _)
      (le_max_right _ _) identity₂)

/-- The long witness at the common maximum cutoff is the maximum of the
individual crossing rates. -/
theorem long_at_maximum_cutoff {ν p A₁ Z₁ A₂ Z₂ : ℝ} (hν : ν ≤ 5/6) :
    longArm ν (max (crossingCut ν p A₁ Z₁) (crossingCut ν p A₂ Z₂)) =
      max (crossingRate ν p A₁ Z₁) (crossingRate ν p A₂ Z₂) := by
  have mono : Monotone (longArm ν) := by
    intro a b hab
    unfold longArm
    nlinarith
  rw [mono.map_max, long_at_crossing, long_at_crossing]

end
end Qrh.JointDetector.RepeatedMarks
