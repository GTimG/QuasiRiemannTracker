/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatch
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Extraction

/-! A bounded repeated word is a literal subcollection of one fixed finite
copied slot type. Its exact width is charged to the parent source. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

def copyPrefix (n K : ℕ) (hn : n≤K) : Finset (Fin K) :=
  Finset.univ.image (Fin.castLE hn)

theorem card_copyPrefix (n K : ℕ) (hn : n≤K) : (copyPrefix n K hn).card=n := by
  rw [copyPrefix,Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact Fin.ext (congrArg (fun j : Fin K => j.val) hab)

theorem val_lt_of_mem_copyPrefix {n K : ℕ} {hn : n≤K} {j : Fin K}
    (hj : j∈copyPrefix n K hn) : j.val<n := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
  exact i.isLt

def copyWord {ι : Type*} [DecidableEq ι] (good R : Finset ι) (n K : ℕ) (hn : n<K) :
    Finset (ι×Fin K) :=
  good.product (copyPrefix n K hn.le) ∪ R.product {⟨n,hn⟩}

private theorem copy_parts_disjoint {ι : Type*} [DecidableEq ι]
    (good R : Finset ι) (n K : ℕ) (hn : n<K) :
    Disjoint (good.product (copyPrefix n K hn.le)) (R.product {⟨n,hn⟩}) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hlt := val_lt_of_mem_copyPrefix (Finset.mem_product.mp hx).2
  have heq : x.2=⟨n,hn⟩ := Finset.mem_singleton.mp (Finset.mem_product.mp hy).2
  rw [heq] at hlt
  exact (Nat.lt_irrefl n) hlt

theorem copyWord_subset {ι : Type*} [DecidableEq ι] (J good R : Finset ι)
    (hg : good⊆J) (hR : R⊆good) (n K : ℕ) (hn : n<K) :
    copyWord good R n K hn⊆J.product Finset.univ := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · exact Finset.mem_product.mpr ⟨hg (Finset.mem_product.mp hx).1,Finset.mem_univ _⟩
  · exact Finset.mem_product.mpr ⟨hg (hR (Finset.mem_product.mp hx).1),Finset.mem_univ _⟩

theorem copyWord_sum {ι : Type*} [DecidableEq ι] (good R : Finset ι)
    (n K : ℕ) (hn : n<K) (f : ι→ℝ) :
    (∑ i∈copyWord good R n K hn,f i.1) =
      (n:ℝ)*(∑ i∈good,f i)+(∑ i∈R,f i) := by
  rw [copyWord,Finset.sum_union (copy_parts_disjoint good R n K hn)]
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product,Finset.sum_product]
  simp only [Finset.sum_const,card_copyPrefix,Finset.card_singleton,nsmul_eq_mul,Nat.cast_one,one_mul]
  rw [←Finset.mul_sum]

/-- The original factors, including natural zeros, are copied without any
coefficient change. -/
theorem copyWord_prod {ι A : Type*} [DecidableEq ι] [CommMonoid A] (good R : Finset ι)
    (n K : ℕ) (hn : n<K) (f : ι→A) :
    (∏ i∈copyWord good R n K hn,f i.1) =
      (∏ i∈good,f i)^n*(∏ i∈R,f i) := by
  rw [copyWord,Finset.prod_union (copy_parts_disjoint good R n K hn)]
  simp only [Finset.product_eq_sprod]
  rw [Finset.prod_product,Finset.prod_product]
  simp only [Finset.prod_const,card_copyPrefix,Finset.card_singleton,pow_one]
  rw [Finset.prod_pow]

end
end Qrh.JointDetector.RepeatedMarks
