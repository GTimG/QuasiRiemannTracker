/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.InitialMoment

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open Record12518109Source

/-- Every shortening enters the earlier global face directly. No individual
plain lower edge or natural-fallback condition occurs. -/
theorem global_shortening_admission (B lam h m₁ m₂ cap M n₁ n₂ s : ℝ)
    (hlam : 0 ≤ lam) (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hs : 0 ≤ s)
    (h₁ : n₁ ≤ m₁) (h₂ : n₂ ≤ m₂) (hslot : s ≤ cap)
    (hcap : cap ≤ h*M) (hbudget : m₁+m₂+lam*cap ≤ B*M) :
    (SourceFace.mk B lam 0 B 0 h).Admissible n₁ n₂ s M := by
  have hmarked := mul_le_mul_of_nonneg_left hslot hlam
  have hnmarked := mul_nonneg hlam hs
  change 0*M ≤ n₁ ∧ n₁ ≤ B*M ∧ 0*M ≤ n₂ ∧ n₂ ≤ B*M ∧
    0*M ≤ s ∧ s ≤ h*M ∧ n₁+n₂+lam*s ≤ B*M
  refine ⟨by simpa using hn₁,by linarith,by simpa using hn₂,
    by linarith,by simpa using hs,hslot.trans hcap,by linarith⟩

/-- The pure RAW retained cap enforces both affine capacity and the finite
upper slot edge. This is used before every further deletion or shortening. -/
theorem global_first_cap (B lam h P Q m₁ m₂ n₁ n₂ s : ℝ)
    (hlam : 0 < lam) (hP : m₁+m₂ ≤ P)
    (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hs : 0 ≤ s)
    (h₁ : n₁ ≤ m₁) (h₂ : n₂ ≤ m₂)
    (hslot : s ≤ min ((B*Q-P)/lam) (h*Q)) :
    (SourceFace.mk B lam 0 B 0 h).Admissible n₁ n₂ s Q := by
  have hz : lam*((B*Q-P)/lam) = B*Q-P :=
    mul_div_cancel₀ _ (ne_of_gt hlam)
  apply global_shortening_admission B lam h m₁ m₂
    (min ((B*Q-P)/lam) (h*Q)) Q n₁ n₂ s hlam.le hn₁ hn₂ hs h₁ h₂ hslot
    (min_le_right _ _)
  have hc := mul_le_mul_of_nonneg_left (min_le_left ((B*Q-P)/lam) (h*Q)) hlam.le
  linarith

/-- C28's three erasure branches are all retained. This pays the zero floor,
affine-cap loss and upper-width loss individually, without an old LOW partner. -/
theorem raw_low_three_branches (a g q B lam h F t b c delta f B12 D : ℝ)
    (hq : 0 ≤ q) (hB : B ≤ 1) (hlam : 1 < lam)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hdc : delta ≤ c)
    (hB12 : 0 ≤ B12) (hdB : delta ≤ B12) (hD : 0 ≤ D) (hf : 0 ≤ f)
    (hh : 0 ≤ h) (hqh : q*h ≤ 1)
    (hgap : g = a-q*(b+(t-B*F)/lam))
    (hcap : (B*F-t)/lam ≤ h*F) :
    -a-B12-D + q*max 0 (max
      (b-f-(B*(F-delta)-(t-c+f))/lam)
      (b-f-h*(F-delta))) ≤ -min a g := by
  have hlam0 : 0 < lam := by linarith
  have hcB : 0 ≤ c-B*delta := by nlinarith
  have hqdiv : 0 ≤ q/lam := div_nonneg hq hlam0.le
  have hqfac : 0 ≤ q*(1-1/lam) := by
    apply mul_nonneg hq
    have : 1/lam ≤ 1 := (div_le_one hlam0).mpr (by linarith)
    linarith
  have hzero : -a-B12-D ≤ -min a g := by
    have := min_le_left a g
    linarith
  have heq : -a-B12-D+q*(b-f-(B*(F-delta)-(t-c+f))/lam) =
      -g-B12-D-(q/lam)*(c-B*delta)-q*(1-1/lam)*f := by
    rw [hgap]
    field_simp
    <;> ring
  have haff : -a-B12-D+q*(b-f-(B*(F-delta)-(t-c+f))/lam) ≤ -min a g := by
    rw [heq]
    have := min_le_right a g
    have hx := mul_nonneg hqdiv hcB
    have hy := mul_nonneg hqfac hf
    linarith
  have heqh : -a-B12-D+q*(b-f-h*(F-delta)) =
      -g+q*((B*F-t)/lam-h*F)+q*h*delta-B12-D-q*f := by
    rw [hgap]
    field_simp
    <;> ring
  have hup : -a-B12-D+q*(b-f-h*(F-delta)) ≤ -min a g := by
    rw [heqh]
    have := min_le_right a g
    have hx := mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hcap)
    have hy : q*h*delta ≤ B12 :=
      (mul_le_mul_of_nonneg_right hqh hdelta).trans (by simpa using hdB)
    have hz := mul_nonneg hq hf
    linarith
  rcases le_total 0 (max (b-f-(B*(F-delta)-(t-c+f))/lam) (b-f-h*(F-delta))) with hmax | hmax
  · rw [max_eq_right hmax]
    rcases le_total (b-f-(B*(F-delta)-(t-c+f))/lam) (b-f-h*(F-delta)) with h' | h'
    · simpa only [max_eq_right h'] using hup
    · simpa only [max_eq_left h'] using haff
  · simpa only [max_eq_left hmax, mul_zero, add_zero] using hzero

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.global_shortening_admission
#print axioms QRH.Record1252270103Low.global_first_cap
#print axioms QRH.Record1252270103Low.raw_low_three_branches
