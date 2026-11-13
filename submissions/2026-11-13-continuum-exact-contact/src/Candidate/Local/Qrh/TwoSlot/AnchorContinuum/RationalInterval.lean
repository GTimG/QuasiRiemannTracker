/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Signed rational intervals for exact parameter enclosures. These lemmas prove
containment for ordinary real arithmetic; they assert no analytic estimate. -/
import Mathlib.Tactic

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.RationalInterval
noncomputable section

structure Box where
  lo : ℚ
  hi : ℚ

def Box.Contains (B : Box) (x : ℝ) : Prop := (B.lo:ℝ) ≤ x ∧ x ≤ (B.hi:ℝ)
def point (q : ℚ) : Box := ⟨q,q⟩
def add (A B : Box) : Box := ⟨A.lo+B.lo,A.hi+B.hi⟩
def neg (A : Box) : Box := ⟨-A.hi,-A.lo⟩
def sub (A B : Box) : Box := add A (neg B)
def mul (A B : Box) : Box :=
  ⟨min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi)),
   max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi))⟩
def inv (B : Box) : Box := ⟨1/B.hi,1/B.lo⟩
def div (A B : Box) : Box := mul A (inv B)

theorem point_sound (q : ℚ) : (point q).Contains q := ⟨le_rfl,le_rfl⟩

theorem Box.transport {B : Box} {x y : ℝ} (hx : B.Contains x) (he : x = y) : B.Contains y :=
  he ▸ hx

theorem add_sound {A B : Box} {x y : ℝ} (hx : A.Contains x) (hy : B.Contains y) :
    (add A B).Contains (x+y) := by
  rcases hx with ⟨hx0,hx1⟩
  rcases hy with ⟨hy0,hy1⟩
  constructor <;> dsimp [add] <;> push_cast <;> linarith

theorem neg_sound {A : Box} {x : ℝ} (hx : A.Contains x) : (neg A).Contains (-x) := by
  rcases hx with ⟨hx0,hx1⟩
  constructor <;> dsimp [neg] <;> push_cast <;> linarith

theorem sub_sound {A B : Box} {x y : ℝ} (hx : A.Contains x) (hy : B.Contains y) :
    (sub A B).Contains (x-y) := by
  simpa only [sub,sub_eq_add_neg] using add_sound hx (neg_sound hy)

theorem scaled_bounds {l u y : ℝ} (hy : l ≤ y ∧ y ≤ u) (c : ℝ) :
    min (c*l) (c*u) ≤ c*y ∧ c*y ≤ max (c*l) (c*u) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hc),
      (mul_le_mul_of_nonneg_left hy.2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hc)),
      (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hc)).trans (le_max_left _ _)⟩

theorem mul_sound {A B : Box} {x y : ℝ} (hx : A.Contains x) (hy : B.Contains y) :
    (mul A B).Contains (x*y) := by
  constructor <;> dsimp [Box.Contains,mul] <;> push_cast
  · apply le_trans _ (show min (x*(B.lo:ℝ)) (x*(B.hi:ℝ)) ≤ x*y from (scaled_bounds hy x).1)
    apply le_min
    · have h0 : min ((A.lo:ℝ)*(B.lo:ℝ)) ((A.hi:ℝ)*(B.lo:ℝ)) ≤ x*(B.lo:ℝ) := by
        simpa only [mul_comm] using (scaled_bounds hx (B.lo:ℝ)).1
      apply le_trans _ h0
      apply le_min
      · exact (min_le_left _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_left _ _)
    · have h0 : min ((A.lo:ℝ)*(B.hi:ℝ)) ((A.hi:ℝ)*(B.hi:ℝ)) ≤ x*(B.hi:ℝ) := by
        simpa only [mul_comm] using (scaled_bounds hx (B.hi:ℝ)).1
      apply le_trans _ h0
      apply le_min
      · exact (min_le_left _ _).trans (min_le_right _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
  · apply le_trans (scaled_bounds hy x).2
    apply max_le
    · have h0 : x*(B.lo:ℝ) ≤ max ((A.lo:ℝ)*(B.lo:ℝ)) ((A.hi:ℝ)*(B.lo:ℝ)) := by
        simpa only [mul_comm] using (scaled_bounds hx (B.lo:ℝ)).2
      apply le_trans h0
      apply max_le
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
    · have h0 : x*(B.hi:ℝ) ≤ max ((A.lo:ℝ)*(B.hi:ℝ)) ((A.hi:ℝ)*(B.hi:ℝ)) := by
        simpa only [mul_comm] using (scaled_bounds hx (B.hi:ℝ)).2
      apply le_trans h0
      apply max_le
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)

theorem inv_sound {B : Box} {x : ℝ} (hB : 0 < B.lo) (hx : B.Contains x) :
    (inv B).Contains (1/x) := by
  have hl : (0:ℝ) < B.lo := by exact_mod_cast hB
  have hp : 0 < x := hl.trans_le hx.1
  constructor <;> dsimp [inv] <;> push_cast
  · exact one_div_le_one_div_of_le hp hx.2
  · exact one_div_le_one_div_of_le hl hx.1

theorem div_sound {A B : Box} {x y : ℝ} (hx : A.Contains x) (hy : B.Contains y)
    (hB : 0 < B.lo) : (div A B).Contains (x/y) := by
  simpa only [div,div_eq_mul_inv,one_div,one_mul] using mul_sound hx (inv_sound hB hy)

end
end Qrh.TwoSlot.AnchorContinuum.RationalInterval
