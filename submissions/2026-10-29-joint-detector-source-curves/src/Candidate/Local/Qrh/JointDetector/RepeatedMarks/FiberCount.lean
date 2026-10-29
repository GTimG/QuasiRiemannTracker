/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateBounds
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.InverseCount

/-! Finite count assembly. Every moment hypothesis below refers to exactly
the same actual witness fiber; no independent row selections are combined. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

/-- Buffered detector lengths lose only the inverse affine slope times the
length buffer. Both plain-capacity branches are retained simultaneously. -/
theorem buffered_short_minimax {ν p A₁ Z₁ A₂ Z₂ r m ε : ℝ}
    (hν : 0 < ν) (hp : p < 1) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hJ₁ : crossingDen ν p A₁ ≠ 0) (hJ₂ : crossingDen ν p A₂ ≠ 0)
    (hε : 0 ≤ ε)
    (hlength : max (crossingCut ν p A₁ Z₁) (crossingCut ν p A₂ Z₂) ≤ r+m+ε) :
    min (1-ν*p-ν*(1-p)*r) (max (1-ν*Z₁-ν*A₁*m) (1-ν*Z₂-ν*A₂*m)) ≤
      max (crossingRate ν p A₁ Z₁) (crossingRate ν p A₂ Z₂)+ν*(1-p)*ε := by
  let c := min (1-ν*p-ν*(1-p)*r) (max (1-ν*Z₁-ν*A₁*m) (1-ν*Z₂-ν*A₂*m))
  have hb : 0 ≤ ν*(1-p)*ε := by positivity
  have hi : c-ν*(1-p)*ε ≤ 1-ν*p-ν*(1-p)*(r+ε) := by
    have hh : c ≤ 1-ν*p-ν*(1-p)*r := min_le_left _ _
    nlinarith only [hh]
  have hpcount : c-ν*(1-p)*ε ≤ max (1-ν*Z₁-ν*A₁*m) (1-ν*Z₂-ν*A₂*m) := by
    have hh : c ≤ max (1-ν*Z₁-ν*A₁*m) (1-ν*Z₂-ν*A₂*m) := min_le_right _ _
    linarith
  have h := at_maximum_cutoff hν hp hA₁ hA₂ hJ₁ hJ₂
    (show max (crossingCut ν p A₁ Z₁) (crossingCut ν p A₂ Z₂) ≤ (r+ε)+m by linarith)
    hi hpcount
  change c ≤ _
  linarith

/-- Combining two actual moment consequences requires their common fiber.
The power minimum is taken before any cell/amplitude supremum. -/
theorem count_from_two_bounds {count U C a b R loss : ℝ}
    (hU : 1 ≤ U) (hC : 0 ≤ C)
    (ha : count ≤ C*U^(a+loss)) (hb : count ≤ C*U^(b+loss))
    (hexp : min a b ≤ R) : count ≤ C*U^(R+loss) := by
  have hbound : count ≤ C*U^(min a b+loss) := by
    by_cases hab : a ≤ b
    · simpa only [min_eq_left hab] using ha
    · simpa only [min_eq_right (le_of_not_ge hab)] using hb
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU (by linarith)) hC)

/-- The buffered repeated short count, ready for the actual inverse/plain
response bridges. The moment bounds retain their literal original response. -/
theorem short_fiber_count {count U C B L c ν v r m ε loss : ℝ}
    (hU : 1 ≤ U) (hC : 0 ≤ C) (hν : 0 < ν) (hνhi : ν ≤ 3/4)
    (hv0 : 0 ≤ v) (hv : v ≤ ν) (hB0 : 0 ≤ B) (hB : B ≤ 1)
    (hL : 3/2 ≤ L) (hε : 0 ≤ ε)
    (hlength : max (crossingCut ν (v/(2*ν)) 2 (2*(v/(2*ν))*c))
      (crossingCut ν (v/(2*ν)) (2-4*(v/(2*ν))/L) (2*(v/(2*ν))*B/L)) ≤ r+m+ε)
    (hi : count ≤ C*U^(inverseArm ν v r+loss))
    (hp : count ≤ C*U^(max (plainCapArm c ν v m) (plainBudgetArm B L ν v m)+loss)) :
    count ≤ C*U^(rawRepeatedCountRate B L c ν v+ν*ε+loss) := by
  let p := v/(2*ν)
  have hp0 : 0 ≤ p := div_nonneg hv0 (by positivity)
  have hphalf : p ≤ 1/2 := (div_le_iff₀ (by positivity : 0<2*ν)).mpr (by linarith)
  have hp1 : p < 1 := by linarith
  have hcoef := budget_coefficients hB0 hB hL hp0 hphalf
  have hJ₁ := branch_den_pos hν hνhi hphalf (by norm_num : (0:ℝ)<2)
  have hJ₂ := branch_den_pos hν hνhi hphalf (by linarith : 0<2-4*p/L)
  have he := buffered_short_minimax hν hp1 (by norm_num : (0:ℝ)≤2)
    (by linarith : 0≤2-4*p/L) hJ₁.ne' hJ₂.ne' hε hlength
  have hpiden : 2*ν*p=v := by dsimp [p]; field_simp
  have hI : 1-ν*p-ν*(1-p)*r = inverseArm ν v r := by
    unfold inverseArm
    nlinarith only [hpiden, congrArg (fun x : ℝ => x*r) hpiden]
  have hP₁ : 1-ν*(2*p*c)-ν*2*m = plainCapArm c ν v m := by
    unfold plainCapArm
    nlinarith only [congrArg (fun x : ℝ => x*c) hpiden]
  have hP₂ : 1-ν*(2*p*B/L)-ν*(2-4*p/L)*m = plainBudgetArm B L ν v m := by
    unfold plainBudgetArm
    have hL0 : L≠0 := by linarith
    field_simp [hL0]
    nlinarith only [hpiden, congrArg (fun x : ℝ => x*B) hpiden,
      congrArg (fun x : ℝ => x*m) hpiden]
  rw [hI,hP₁,hP₂] at he
  apply count_from_two_bounds hU hC hi hp
  have hfirst : max (crossingRate ν p 2 (2*p*c))
      (crossingRate ν p (2-4*p/L) (2*p*B/L)) ≤ rawRepeatedCountRate B L c ν v :=
    le_max_left _ _
  have hbuffer : ν*(1-p)*ε ≤ ν*ε := by
    have hh := mul_nonneg (mul_nonneg hν.le hp0) hε
    nlinarith only [hh]
  linarith

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

/-- Complete finite witness regime split. Long inverse and no-slot plain
arms remain explicit inherited moment consequences on the SAME fiber. -/
theorem full_fiber_count {count U C B L c ν v r m ε loss : ℝ}
    (hU : 1 ≤ U) (hC : 0 ≤ C) (hν : 0 < ν) (hνhi : ν ≤ 3/4)
    (hv0 : 0 ≤ v) (hv : v ≤ ν) (hB0 : 0 ≤ B) (hB : B ≤ 1)
    (hL : 3/2 ≤ L) (hε : 0 ≤ ε)
    (hrcap : r ≤ max (crossingCut ν (v/(2*ν)) 2 (2*(v/(2*ν))*c))
      (crossingCut ν (v/(2*ν)) (2-4*(v/(2*ν))/L) (2*(v/(2*ν))*B/L))+ε)
    (hlength : max (crossingCut ν (v/(2*ν)) 2 (2*(v/(2*ν))*c))
      (crossingCut ν (v/(2*ν)) (2-4*(v/(2*ν))/L) (2*(v/(2*ν))*B/L)) ≤ r+m+ε)
    (hi : r < 1 → m < B/2 → count ≤ C*U^(inverseArm ν v r+loss))
    (hp : r < 1 → m < B/2 → count ≤ C*U^(max (plainCapArm c ν v m) (plainBudgetArm B L ν v m)+loss))
    (hlong : 1 ≤ r → count ≤ C*U^(longArm ν r+loss))
    (htail : B/2 ≤ m → count ≤ C*U^(1-2*ν*m+loss)) :
    count ≤ C*U^(rawRepeatedCountRate B L c ν v+ε+loss) := by
  by_cases hr : r < 1
  · by_cases hm : m < B/2
    · have he := short_fiber_count hU hC hν hνhi hv0 hv hB0 hB hL hε hlength (hi hr hm) (hp hr hm)
      apply he.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hU
      nlinarith
    · apply (htail (le_of_not_gt hm)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hU
      have ht : 1-ν*B ≤ rawRepeatedCountRate B L c ν v := le_max_right _ _
      nlinarith
  · apply (hlong (le_of_not_gt hr)).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow_of_exponent_le hU
    have he := long_at_maximum_cutoff (p:=v/(2*ν)) (A₁:=2) (Z₁:=2*(v/(2*ν))*c)
      (A₂:=2-4*(v/(2*ν))/L) (Z₂:=2*(v/(2*ν))*B/L) (by linarith : ν≤5/6)
    have ht : max (crossingRate ν (v/(2*ν)) 2 (2*(v/(2*ν))*c))
      (crossingRate ν (v/(2*ν)) (2-4*(v/(2*ν))/L) (2*(v/(2*ν))*B/L)) ≤
      rawRepeatedCountRate B L c ν v := le_max_left _ _
    have hgap := mul_nonneg (show 0≤(5/6:ℝ)-ν by linarith) (sub_nonneg.mpr hrcap)
    have heps := mul_nonneg hν.le hε
    unfold longArm at he ⊢
    nlinarith

end
end Qrh.JointDetector.RepeatedMarks
