/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.BalancedSlotSelection

/-! Finite repeated-slot extraction. The multiplicity bound is fixed by a
positive aggregate width cutoff, before the eventual finite slot type. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

/-- An upward balanced selection at target minus one mesh gives a word
inside the requested capacity. No individual upper bound on energy is used. -/
theorem repeated_below_capacity {ι : Type*} (J : Finset ι) (w energy : ι → ℝ)
    (δ target mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (ht : mesh ≤ target) (hW : 0 < ∑ i ∈ J, w i)
    (henergy : δ*(∑ i ∈ J, w i) ≤ ∑ i ∈ J, energy i) :
    ∃ (n : ℕ) (R : Finset ι), R ⊆ J ∧
      (n:ℝ) ≤ target/(∑ i ∈ J, w i) ∧
      target-mesh ≤ (n:ℝ)*(∑ i ∈ J, w i)+(∑ i ∈ R, w i) ∧
      (n:ℝ)*(∑ i ∈ J, w i)+(∑ i ∈ R, w i) ≤ target ∧
      δ*((n:ℝ)*(∑ i ∈ J, w i)+(∑ i ∈ R, w i)) ≤
        (n:ℝ)*(∑ i ∈ J, energy i)+(∑ i ∈ R, energy i) := by
  obtain ⟨n,R,hR,hn,hlo,hhi,he⟩ :=
    BalancedSlotSelection.repeated_balanced_subset J w energy δ (target-mesh) mesh
      hm hw hwm (sub_nonneg.mpr ht) hW henergy
  refine ⟨n,R,hR,hn.trans ?_,hlo,?_,he⟩
  · exact div_le_div_of_nonneg_right (by linarith) hW.le
  · linarith

/-- A fixed positive total-width cutoff bounds all repetition counts; the
right side is independent of the slot count and of its individual widths. -/
theorem repetition_count_bound {n : ℕ} {target width wmin zmax : ℝ}
    (hw : 0 < wmin) (hwidth : wmin ≤ width) (ht : 0 ≤ target)
    (hmax : target ≤ zmax) (hn : (n:ℝ) ≤ target/width) :
    (n:ℝ) ≤ zmax/wmin := by
  have hwidth0 : 0 < width := hw.trans_le hwidth
  apply hn.trans
  exact (div_le_div_of_nonneg_left ht hw hwidth).trans
    (div_le_div_of_nonneg_right hmax hw.le)

/-- The complete copies and the final subset are one bounded multiplicity
vector. This is the finite index by which actual rows are partitioned. -/
def multiplicity {ι : Type*} [DecidableEq ι] (n : ℕ) (R : Finset ι) (i : ι) : ℕ :=
  n + if i ∈ R then 1 else 0

theorem multiplicity_le {ι : Type*} [DecidableEq ι] (n : ℕ) (R : Finset ι) (i : ι) :
    multiplicity n R i ≤ n+1 := by
  unfold multiplicity
  split_ifs <;> omega

/-- Exact total width and energy bookkeeping for the repeated word. -/
theorem sum_multiplicity {ι : Type*} [DecidableEq ι] (J R : Finset ι)
    (hR : R ⊆ J) (n : ℕ) (f : ι → ℝ) :
    (∑ i ∈ J, (multiplicity n R i : ℝ)*f i) =
      (n:ℝ)*(∑ i ∈ J, f i)+(∑ i ∈ R, f i) := by
  simp only [multiplicity, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hR h,h⟩⟩

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

/-- A fixed response gap gives a fixed positive width of factors above the
slightly lower slope. This allows OAI's individually clipped bins to be used
without assuming any individual exceptional-character upper slope. -/
theorem high_slope_support_width {ι : Type*} (J : Finset ι)
    (w energy error : ι → ℝ) (δ β smin loss : ℝ)
    (hw : ∀ i ∈ J, 0 ≤ w i) (herr : ∀ i ∈ J, 0 ≤ error i)
    (hδ : 0 ≤ δ) (hβ : 0 ≤ β) (hs : smin ≤ ∑ i ∈ J, w i)
    (hupper : ∀ i ∈ J, energy i ≤ w i+error i)
    (herrors : (∑ i ∈ J, error i) ≤ loss)
    (hlower : (δ+β)*(∑ i ∈ J, w i)-loss ≤ ∑ i ∈ J, energy i)
    (hbudget : 4*loss ≤ β*smin) :
    β*smin/2 ≤ ∑ i ∈ J.filter (fun i => δ*w i ≤ energy i), w i := by
  classical
  let good := J.filter (fun i => δ*w i ≤ energy i)
  have hbound (i : ι) (hi : i ∈ J) : energy i ≤
      δ*w i+(if i ∈ good then w i else 0)+error i := by
    by_cases hg : i ∈ good
    · rw [if_pos hg]
      nlinarith [hupper i hi, mul_nonneg hδ (hw i hi)]
    · rw [if_neg hg]
      have hn : energy i < δ*w i := by
        apply lt_of_not_ge
        intro hh
        exact hg (Finset.mem_filter.mpr ⟨hi,hh⟩)
      linarith [herr i hi]
  have hsum := Finset.sum_le_sum hbound
  have hid : (∑ i ∈ J, if i ∈ good then w i else 0) = ∑ i ∈ good, w i := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hid] at hsum
  have hβS := mul_le_mul_of_nonneg_left hs hβ
  change β*smin/2 ≤ ∑ i ∈ good, w i
  nlinarith

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

/-- Exact polynomial identity for the repeated word; its factors and their
natural zeros are retained, with no coefficient change. -/
theorem prod_multiplicity {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (J R : Finset ι) (hR : R ⊆ J) (n : ℕ) (f : ι → M) :
    (∏ i ∈ J, (f i)^(multiplicity n R i)) =
      (∏ i ∈ J, f i)^n * (∏ i ∈ R, f i) := by
  simp only [multiplicity, pow_add, Finset.prod_mul_distrib, ← Finset.prod_pow]
  congr 1
  simp only [pow_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hR h,h⟩⟩

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

/-- A repetition budget fixed from the aggregate cutoffs suffices for every
requested capacity. Its bound precedes the eventual slot count and scale. -/
theorem bounded_positive_repetition {ι : Type*} (J : Finset ι)
    (w energy error : ι → ℝ) (δ β smin loss mesh target zmax : ℝ) (K : ℕ)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (herr : ∀ i ∈ J, 0 ≤ error i) (hδ : 0 ≤ δ) (hβ : 0 < β)
    (hsmin : 0 < smin) (hs : smin ≤ ∑ i ∈ J, w i)
    (hupper : ∀ i ∈ J, energy i ≤ w i+error i)
    (herrors : (∑ i ∈ J, error i) ≤ loss)
    (hlower : (δ+β)*(∑ i ∈ J, w i)-loss ≤ ∑ i ∈ J, energy i)
    (hbudget : 4*loss ≤ β*smin) (hm : 0 ≤ mesh)
    (ht : mesh ≤ target) (hmax : target ≤ zmax)
    (hK : zmax/(β*smin/2)+1 ≤ (K:ℝ)) :
    ∃ (good : Finset ι) (n : ℕ) (R : Finset ι), good ⊆ J ∧ R ⊆ good ∧ n+1≤K ∧
      target-mesh ≤ (n:ℝ)*(∑ i ∈ good,w i)+(∑ i ∈ R,w i) ∧
      (n:ℝ)*(∑ i ∈ good,w i)+(∑ i ∈ R,w i) ≤ target ∧
      δ*(target-mesh) ≤ (n:ℝ)*(∑ i ∈ good,energy i)+(∑ i ∈ R,energy i) := by
  classical
  let good := J.filter (fun i => δ*w i≤energy i)
  have hg : good ⊆ J := Finset.filter_subset _ _
  have hwidth : β*smin/2 ≤ ∑ i ∈ good,w i :=
    high_slope_support_width J w energy error δ β smin loss hw herr hδ hβ.le hs
      hupper herrors hlower hbudget
  have hwidth0 : 0 < β*smin/2 := by positivity
  have hW : 0 < ∑ i ∈ good,w i := hwidth0.trans_le hwidth
  have he : δ*(∑ i ∈ good,w i) ≤ ∑ i ∈ good,energy i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
  obtain ⟨n,R,hR,hn,hlo,hhi,henergy⟩ := repeated_below_capacity good w energy δ target mesh
    hm (fun i hi => hw i (hg hi)) (fun i hi => hwm i (hg hi)) ht hW he
  have hnK : (n:ℝ)+1 ≤ K := by
    have hh := repetition_count_bound hwidth0 hwidth (hm.trans ht) hmax hn
    linarith
  refine ⟨good,n,R,hg,hR,by exact_mod_cast hnK,hlo,hhi,?_⟩
  exact (mul_le_mul_of_nonneg_left hlo hδ).trans henergy

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

theorem bounded_positive_repetition_all_targets {ι : Type*} (J : Finset ι)
    (w energy error : ι → ℝ) (δ β smin loss mesh target zmax : ℝ) (K : ℕ)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (herr : ∀ i ∈ J, 0 ≤ error i) (hδ : 0 ≤ δ) (hβ : 0 < β)
    (hsmin : 0 < smin) (hs : smin ≤ ∑ i ∈ J, w i)
    (hupper : ∀ i ∈ J, energy i ≤ w i+error i)
    (herrors : (∑ i ∈ J, error i) ≤ loss)
    (hlower : (δ+β)*(∑ i ∈ J, w i)-loss ≤ ∑ i ∈ J, energy i)
    (hbudget : 4*loss ≤ β*smin) (hm : 0 ≤ mesh)
    (ht : 0 ≤ target) (hmax : target ≤ zmax)
    (hK : zmax/(β*smin/2)+1 ≤ (K:ℝ)) :
    ∃ (good : Finset ι) (n : ℕ) (R : Finset ι), good ⊆ J ∧ R ⊆ good ∧ n+1≤K ∧
      target-mesh ≤ (n:ℝ)*(∑ i ∈ good,w i)+(∑ i ∈ R,w i) ∧
      (n:ℝ)*(∑ i ∈ good,w i)+(∑ i ∈ R,w i) ≤ target ∧
      δ*(target-mesh) ≤ (n:ℝ)*(∑ i ∈ good,energy i)+(∑ i ∈ R,energy i) := by
  by_cases htm : mesh ≤ target
  · exact bounded_positive_repetition J w energy error δ β smin loss mesh target zmax K
      hw hwm herr hδ hβ hsmin hs hupper herrors hlower hbudget hm htm hmax hK
  · have hK1 : 1 ≤ K := by
      have hz : 0 ≤ zmax/(β*smin/2) := div_nonneg (ht.trans hmax) (by positivity)
      have hh : (1:ℝ) ≤ K := by linarith
      exact_mod_cast hh
    refine ⟨∅,0,∅,Finset.empty_subset _,Finset.empty_subset _,by simpa using hK1,?_,?_,?_⟩
    · simp only [Finset.sum_empty,Nat.cast_zero,zero_mul,add_zero]
      linarith
    · simpa using ht
    · simp only [Finset.sum_empty,Nat.cast_zero,zero_mul,add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hδ (by linarith)

end
end Qrh.JointDetector.RepeatedMarks
