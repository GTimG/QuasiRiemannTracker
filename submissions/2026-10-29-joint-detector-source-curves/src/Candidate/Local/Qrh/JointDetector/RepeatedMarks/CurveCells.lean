/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks.CurveCells
noncomputable section
set_option autoImplicit false
open Set

/-- The actual lower density cut of one curved source step. -/
def q (k e0 ev v : ℝ) : ℝ := k/(e0+ev*v)
def crossingWidth (k e0 ev split : ℝ) : ℝ := (k/split-e0)/ev

theorem denominator_pos {e0 ev v : ℝ} (he0 : 0<e0) (hev : 0≤ev) (hv : 0≤v) :
 0<e0+ev*v := by positivity

theorem q_antitone {k e0 ev v w : ℝ}
 (hk : 0≤k) (he0 : 0<e0) (hev : 0≤ev) (hv : 0≤v) (hvw : v≤w) :
 q k e0 ev w≤q k e0 ev v := by
 unfold q
 apply div_le_div_of_nonneg_left hk (denominator_pos he0 hev hv)
 nlinarith only [mul_le_mul_of_nonneg_left hvw hev]

theorem q_bounds {k e0 ev V v : ℝ}
 (hk : 0≤k) (he0 : 0<e0) (hev : 0≤ev) (hv : v∈Icc (0:ℝ) V) :
 q k e0 ev V≤q k e0 ev v ∧ q k e0 ev v≤q k e0 ev 0 := by
 exact ⟨q_antitone hk he0 hev hv.1 hv.2,q_antitone hk he0 hev (by norm_num) hv.1⟩

theorem crossing_denominator {k e0 ev split : ℝ} (hev : ev≠0) :
 e0+ev*crossingWidth k e0 ev split=k/split := by
 unfold crossingWidth
 field_simp [hev]
 <;> ring

theorem q_crossing {k e0 ev split : ℝ} (hk : k≠0) (hev : ev≠0) (hsplit : split≠0) :
 q k e0 ev (crossingWidth k e0 ev split)=split := by
 unfold q
 rw [crossing_denominator hev]
 field_simp [hk,hsplit]

theorem crossing_mem {k e0 ev split V : ℝ}
 (hk : 0<k) (he0 : 0<e0) (hev : 0<ev) (hV : 0≤V)
 (hsplit : 0<split) (hlo : q k e0 ev V<split) (hhi : split≤q k e0 ev 0) :
 crossingWidth k e0 ev split∈Ico (0:ℝ) V := by
 have hd : 0<e0+ev*V := denominator_pos he0 hev.le hV
 have hhi0 : split≤k/e0 := by simpa [q] using hhi
 have hhi' : split*e0≤k := (le_div_iff₀ he0).mp hhi0
 have hlo' : k<split*(e0+ev*V) := (div_lt_iff₀ hd).mp hlo
 constructor
 · unfold crossingWidth
   apply div_nonneg _ hev.le
   exact sub_nonneg.mpr ((le_div_iff₀ hsplit).2 (by nlinarith only [hhi']))
 · unfold crossingWidth
   apply (div_lt_iff₀ hev).2
   have hh : k/split<e0+ev*V := (div_lt_iff₀ hsplit).2 (by nlinarith only [hlo'])
   linarith

theorem q_crossing_sides {k e0 ev split V v : ℝ}
 (hk : 0<k) (he0 : 0<e0) (hev : 0<ev) (hV : 0≤V)
 (hsplit : 0<split) (hlo : q k e0 ev V<split) (hhi : split≤q k e0 ev 0)
 (hv : 0≤v) :
 (v≤crossingWidth k e0 ev split → split≤q k e0 ev v) ∧
 (crossingWidth k e0 ev split≤v → q k e0 ev v≤split) := by
 have hvc := crossing_mem hk he0 hev hV hsplit hlo hhi
 have hq := q_crossing (e0:=e0) hk.ne' hev.ne' hsplit.ne'
 constructor
 · intro hh
   rw [←hq]
   exact q_antitone hk.le he0 hev.le hv hh
 · intro hh
   rw [←hq]
   exact q_antitone hk.le he0 hev.le hvc.1 hh

/-- Below the divider crossing only the ray is active; above it the
constant and ray cells meet on their common density boundary. -/
theorem cell_cover {k e0 ev a r V v ν : ℝ}
 (hk : 0<k) (he0 : 0<e0) (hev : 0<ev) (ha : 0<a) (hr : 0<r)
 (hV : 0≤V) (hv : v∈Icc (0:ℝ) V) (hν : q k e0 ev v≤ν) (hνhi : ν≤3/4)
 (hsplitlo : q k e0 ev V<a/r) (hsplithi : a/r≤q k e0 ev 0) :
 let vc:=crossingWidth k e0 ev (a/r)
 (v∈Icc vc V ∧ ν∈Icc (q k e0 ev v) (a/r) ∧ max a (r*ν)=a) ∨
 (v∈Icc vc V ∧ ν∈Icc (a/r) (3/4) ∧ max a (r*ν)=r*ν) ∨
 (0<vc ∧ v∈Icc (0:ℝ) vc ∧ ν∈Icc (q k e0 ev v) (3/4) ∧ a/r≤ν ∧ max a (r*ν)=r*ν) := by
 dsimp only
 let vc:=crossingWidth k e0 ev (a/r)
 have hvc := crossing_mem hk he0 hev hV (div_pos ha hr) hsplitlo hsplithi
 have hqvc : q k e0 ev vc=a/r := q_crossing hk.ne' hev.ne' (div_pos ha hr).ne'
 have hRay {ν : ℝ} (h : a/r≤ν) : max a (r*ν)=r*ν := by
  rw [max_eq_right]
  exact (div_le_iff₀ hr).mp h |>.trans_eq (mul_comm ν r)
 by_cases hvbefore : v≤vc
 · have hq : a/r≤q k e0 ev v := by
    rw [←hqvc]
    exact q_antitone hk.le he0 hev.le hv.1 hvbefore
   by_cases hvcpos : 0<vc
   · right;right
     exact ⟨hvcpos,⟨hv.1,hvbefore⟩,⟨hν,hνhi⟩,hq.trans hν,hRay (hq.trans hν)⟩
   · right;left
     have hvcEq : vc=0 := le_antisymm (le_of_not_gt hvcpos) hvc.1
     exact ⟨⟨by change vc≤v;rw [hvcEq];exact hv.1,hv.2⟩,⟨hq.trans hν,hνhi⟩,hRay (hq.trans hν)⟩
 · have hvl : vc≤v := le_of_lt (lt_of_not_ge hvbefore)
   by_cases hn : ν≤a/r
   · left
     refine ⟨⟨hvl,hv.2⟩,⟨hν,hn⟩,?_⟩
     rw [max_eq_left]
     have hh := (le_div_iff₀ hr).mp hn
     nlinarith only [hh]
   · right;left
     have hn' : a/r≤ν := le_of_lt (lt_of_not_ge hn)
     exact ⟨⟨hvl,hv.2⟩,⟨hn',hνhi⟩,hRay hn'⟩

/-- When the crossing is below the whole density range there is only one
ray cell, including its moving lower boundary. -/
theorem ray_cell_cover {k e0 ev a r V v ν : ℝ}
 (hk : 0≤k) (he0 : 0<e0) (hev : 0≤ev) (hr : 0<r)
 (hv : v∈Icc (0:ℝ) V) (hν : q k e0 ev v≤ν) (hνhi : ν≤3/4)
 (hsplit : a/r≤q k e0 ev V) :
 v∈Icc (0:ℝ) V ∧ ν∈Icc (q k e0 ev v) (3/4) ∧ max a (r*ν)=r*ν := by
 have hq := (q_bounds hk he0 hev hv).1
 have ha : a≤r*ν := by
  have hh := (div_le_iff₀ hr).mp (hsplit.trans (hq.trans hν))
  nlinarith only [hh]
 exact ⟨hv,⟨hν,hνhi⟩,max_eq_right ha⟩

/-- In the pure repeated branch the divider is the density itself. -/
theorem pure_cell_cover {k e0 ev V v ν : ℝ}
 (hv : v∈Icc (0:ℝ) V) (hν : q k e0 ev v≤ν) (hνhi : ν≤3/4) :
 v∈Icc (0:ℝ) V ∧ ν∈Icc (q k e0 ev v) (3/4) ∧ (1:ℝ)*ν=ν :=
 ⟨hv,⟨hν,hνhi⟩,one_mul _⟩

end
end Qrh.JointDetector.RepeatedMarks.CurveCells

#print axioms Qrh.JointDetector.RepeatedMarks.CurveCells.cell_cover
