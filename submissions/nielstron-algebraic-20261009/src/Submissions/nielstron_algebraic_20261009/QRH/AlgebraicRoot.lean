import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QRH.Algebraic
noncomputable section

def cubic (e : ℝ) : ℝ := 657*e^3-954*e^2+21*e+20

theorem cubic_strictAnti : StrictAntiOn cubic (Set.Icc (1/6:ℝ) (1/5:ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hxx : x*x ≤ (1/25:ℝ) := by
    have h := mul_le_mul hx.2 hx.2 hx0 (by norm_num : (0:ℝ) ≤ 1/5)
    norm_num at h ⊢
    exact h
  have hyy : y*y ≤ (1/25:ℝ) := by
    have h := mul_le_mul hy.2 hy.2 hy0 (by norm_num : (0:ℝ) ≤ 1/5)
    norm_num at h ⊢
    exact h
  have hxy1 : x*y ≤ (1/25:ℝ) := by
    have h := mul_le_mul hx.2 hy.2 hy0 (by norm_num : (0:ℝ) ≤ 1/5)
    norm_num at h ⊢
    exact h
  have hcoef : 657*(y*y+x*y+x*x)-954*(y+x)+21 < 0 := by
    nlinarith [hx.1,hy.1]
  have hprod := mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hcoef
  have hid : cubic y-cubic x = (y-x)*(657*(y*y+x*y+x*x)-954*(y+x)+21) := by
    unfold cubic
    ring
  linarith

theorem exists_unique_root : ∃! e : ℝ, e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ) ∧ cubic e=0 := by
  have hc : Continuous cubic := by
    unfold cubic
    exact (((continuous_const.mul (continuous_id.pow 3)).sub
      (continuous_const.mul (continuous_id.pow 2))).add
      (continuous_const.mul continuous_id)).add continuous_const
  have hr : (0:ℝ) ∈ Set.Icc (cubic (1/5)) (cubic (1/6)) := by
    norm_num [cubic]
  obtain ⟨e,he,hzero⟩ := intermediate_value_Icc' (by norm_num : (1/6:ℝ) ≤ 1/5) hc.continuousOn hr
  refine ⟨e,⟨he,hzero⟩,?_⟩
  intro a ha
  exact cubic_strictAnti.injOn ha.1 he (ha.2.trans hzero.symm)

def root : ℝ := Classical.choose exists_unique_root
theorem root_spec : root ∈ Set.Icc (1/6:ℝ) (1/5:ℝ) ∧ cubic root=0 :=
  (Classical.choose_spec exists_unique_root).1

def limitingTheta : ℝ := 11/12-root/4

theorem root_lt_of_cubic_neg {e : ℝ} (he : e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ))
    (hp : cubic e<0) : root<e := by
  by_contra hn
  have hle : e ≤ root := le_of_not_gt hn
  have hh := cubic_strictAnti.antitoneOn he root_spec.1 hle
  rw [root_spec.2] at hh
  linarith

theorem lt_root_of_cubic_pos {e : ℝ} (he : e ∈ Set.Icc (1/6:ℝ) (1/5:ℝ))
    (hp : 0<cubic e) : e<root := by
  by_contra hn
  have hle : root ≤ e := le_of_not_gt hn
  have hh := cubic_strictAnti.antitoneOn root_spec.1 he hle
  rw [root_spec.2] at hh
  linarith

theorem root_narrow : root ∈ Set.Icc (1/6:ℝ) (167/1000:ℝ) := by
  refine ⟨root_spec.1.1, ?_⟩
  exact (root_lt_of_cubic_neg (by norm_num) (by norm_num [cubic])).le

theorem limitingTheta_lower :
    (874957019420098946128603850561452982 / 1000000000000000000000000000000000000:ℝ) < limitingTheta := by
  have h := root_lt_of_cubic_neg
    (e:=11/3-4*(874957019420098946128603850561452982 / 1000000000000000000000000000000000000:ℝ))
    (by norm_num) (by norm_num [cubic])
  unfold limitingTheta
  linarith

theorem limitingTheta_upper :
    limitingTheta < (874957019420098946128603850561452983 / 1000000000000000000000000000000000000:ℝ) := by
  have h := lt_root_of_cubic_pos
    (e:=11/3-4*(874957019420098946128603850561452983 / 1000000000000000000000000000000000000:ℝ))
    (by norm_num) (by norm_num [cubic])
  unfold limitingTheta
  linarith

theorem limitingTheta_lt_N24 :
    limitingTheta < (874957019420098946128604623 / 1000000000000000000000000000:ℝ) := by
  exact limitingTheta_upper.trans (by norm_num)

/-- A uniform bound arbitrarily close to the endpoint gives the endpoint itself.
This is only the order-theoretic closure step, not an analytic hypothesis proof. -/
theorem le_limit_of_bounds_above {β ceiling : ℝ} (hc : limitingTheta<ceiling)
    (h : ∀ θ : ℝ, limitingTheta<θ → θ<ceiling → β≤θ) : β≤limitingTheta := by
  by_contra hn
  have hb : limitingTheta<β := lt_of_not_ge hn
  let θ := (limitingTheta+min β ceiling)/2
  have hm : limitingTheta<min β ceiling := lt_min hb hc
  have ht : limitingTheta<θ := by dsimp [θ]; linarith
  have htc : θ<ceiling := by dsimp [θ]; linarith [min_le_right β ceiling]
  have htb : θ<β := by dsimp [θ]; linarith [min_le_left β ceiling]
  exact (not_lt_of_ge (h θ ht htc)) htb

end
end QRH.Algebraic

