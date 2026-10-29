/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.sil_density_split_20261026.CubeFree.Second.Selection

/-!
Whole-slot amplification needs a prefix with the selected average slope.
Sorting is unnecessary: take nonnegative slope surplus first, then negative
surplus. Every partial selection in this order has nonnegative total surplus.
The greedy overshoot costs only one slot mesh, independently of slot count.
-/
namespace Qrh.JointDetector.BalancedSlotSelection
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

theorem balanced_subset {ι : Type*} (J : Finset ι) (w energy : ι → ℝ)
    (δ target mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (ht : 0 ≤ target) (hfull : target ≤ ∑ i ∈ J, w i)
    (henergy : δ*(∑ i ∈ J, w i) ≤ ∑ i ∈ J, energy i) :
    ∃ R : Finset ι, R ⊆ J ∧ target ≤ ∑ i ∈ R, w i ∧
      (∑ i ∈ R, w i) ≤ target+mesh ∧
      δ*(∑ i ∈ R, w i) ≤ ∑ i ∈ R, energy i := by
  classical
  let surplus : ι → ℝ := fun i => energy i-δ*w i
  let good := J.filter (fun i => 0 ≤ surplus i)
  let bad := J \ good
  have hgJ : good ⊆ J := Finset.filter_subset _ _
  have hbJ : bad ⊆ J := Finset.sdiff_subset
  have hdisj : Disjoint good bad := Finset.disjoint_left.mpr
    (fun _ hi hb => (Finset.mem_sdiff.mp hb).2 hi)
  have hunion : good ∪ bad = J := Finset.union_sdiff_of_subset hgJ
  have htotal : 0 ≤ ∑ i ∈ J, surplus i := by
    simpa only [surplus, Finset.sum_sub_distrib, ← Finset.mul_sum] using sub_nonneg.mpr henergy
  have hfinish (R : Finset ι) (hR : R ⊆ J)
      (hlo : target ≤ ∑ i ∈ R, w i) (hhi : (∑ i ∈ R, w i) ≤ target+mesh)
      (hbal : 0 ≤ ∑ i ∈ R, surplus i) :
      ∃ R : Finset ι, R ⊆ J ∧ target ≤ ∑ i ∈ R, w i ∧
        (∑ i ∈ R, w i) ≤ target+mesh ∧
        δ*(∑ i ∈ R, w i) ≤ ∑ i ∈ R, energy i := by
    refine ⟨R,hR,hlo,hhi,?_⟩
    have hh : 0 ≤ (∑ i ∈ R, energy i)-δ*(∑ i ∈ R, w i) := by
      simpa only [surplus, Finset.sum_sub_distrib, ← Finset.mul_sum] using hbal
    exact sub_nonneg.mp hh
  by_cases hg : target ≤ ∑ i ∈ good, w i
  · obtain ⟨R,hR,hlo,hhi⟩ := QRH.SilDensitySplit.CubeFree.Second.Selection.upward_subset
      good w target mesh hm (fun i hi => hw i (hgJ hi))
      (fun i hi => hwm i (hgJ hi)) ht hg
    apply hfinish R (hR.trans hgJ) hlo (hhi.trans (min_le_right _ _))
    exact Finset.sum_nonneg fun i hi => (Finset.mem_filter.mp (hR hi)).2
  · have hneed : 0 ≤ target-(∑ i ∈ good, w i) := by linarith
    have hbadFull : target-(∑ i ∈ good, w i) ≤ ∑ i ∈ bad, w i := by
      rw [← hunion, Finset.sum_union hdisj] at hfull
      linarith
    obtain ⟨R,hR,hlo,hhi⟩ := QRH.SilDensitySplit.CubeFree.Second.Selection.upward_subset
      bad w (target-(∑ i ∈ good, w i)) mesh hm
      (fun i hi => hw i (hbJ hi)) (fun i hi => hwm i (hbJ hi)) hneed hbadFull
    have hdR : Disjoint good R := hdisj.mono_right hR
    have hneg (i : ι) (hi : i ∈ bad) : surplus i ≤ 0 := by
      have hn : i ∉ good := (Finset.mem_sdiff.mp hi).2
      have hj : i ∈ J := hbJ hi
      have hh : ¬ 0 ≤ surplus i := fun hp => hn (Finset.mem_filter.mpr ⟨hj,hp⟩)
      exact le_of_lt (lt_of_not_ge hh)
    have hbSum : (∑ i ∈ bad, surplus i) ≤ ∑ i ∈ R, surplus i := by
      rw [← Finset.sum_sdiff hR]
      have hn : (∑ i ∈ bad \ R, surplus i) ≤ 0 :=
        Finset.sum_nonpos fun i hi => hneg i (Finset.mem_sdiff.mp hi).1
      linarith
    apply hfinish (good ∪ R) (Finset.union_subset hgJ (hR.trans hbJ))
    · rw [Finset.sum_union hdR]; linarith
    · rw [Finset.sum_union hdR]
      have hh := hhi.trans (min_le_right _ _)
      linarith
    · rw [Finset.sum_union hdR]
      rw [← hunion, Finset.sum_union hdisj] at htotal
      linarith

/-- Complete copies of the selected word followed by one balanced subset
cross any bounded source scale. There is one mesh overshoot in total;
the number of complete copies is bounded before the slot count is known. -/
theorem repeated_balanced_subset {ι : Type*} (J : Finset ι) (w energy : ι → ℝ)
    (δ target mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (ht : 0 ≤ target) (hW : 0 < ∑ i ∈ J, w i)
    (henergy : δ*(∑ i ∈ J, w i) ≤ ∑ i ∈ J, energy i) :
    ∃ (n : ℕ) (R : Finset ι), R ⊆ J ∧
      (n:ℝ) ≤ target/(∑ i ∈ J, w i) ∧
      target ≤ (n:ℝ)*(∑ i ∈ J, w i)+(∑ i ∈ R, w i) ∧
      (n:ℝ)*(∑ i ∈ J, w i)+(∑ i ∈ R, w i) ≤ target+mesh ∧
      δ*((n:ℝ)*(∑ i ∈ J, w i)+(∑ i ∈ R, w i)) ≤
        (n:ℝ)*(∑ i ∈ J, energy i)+(∑ i ∈ R, energy i) := by
  let W := ∑ i ∈ J, w i
  let n : ℕ := ⌊target/W⌋₊
  have hdiv : 0 ≤ target/W := div_nonneg ht hW.le
  have hlo : (n:ℝ) ≤ target/W := Nat.floor_le hdiv
  have hhi : target/W < (n:ℝ)+1 := Nat.lt_floor_add_one (target/W)
  have hrest0 : 0 ≤ target-(n:ℝ)*W :=
    sub_nonneg.mpr ((le_div_iff₀ hW).mp hlo)
  have hrestW : target-(n:ℝ)*W ≤ W := by
    have hh := (div_lt_iff₀ hW).mp hhi
    nlinarith
  obtain ⟨R,hR,hRlo,hRhi,hRenergy⟩ := balanced_subset J w energy δ
    (target-(n:ℝ)*W) mesh hm hw hwm hrest0 hrestW henergy
  refine ⟨n,R,hR,hlo,?_,?_,?_⟩
  · change target ≤ (n:ℝ)*W+(∑ i ∈ R, w i)
    linarith
  · change (n:ℝ)*W+(∑ i ∈ R, w i) ≤ target+mesh
    linarith
  · have hs := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    nlinarith

end
end Qrh.JointDetector.BalancedSlotSelection

#print axioms Qrh.JointDetector.BalancedSlotSelection.balanced_subset
#print axioms Qrh.JointDetector.BalancedSlotSelection.repeated_balanced_subset
