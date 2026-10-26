/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
import Candidate.Cycle25.Numerator.Imported.FullWFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle25.Weighted.FullWContour
local notation "O" => HeckeFamily.O

theorem fullW_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u ≤ n ∧ grid u ≤ m) :
    finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),
      finiteCentralFullWRows S hS hmax η (cubeBinRows R idx grid i j) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralFullWRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i j u).mp hu with ⟨_,hi,hj⟩
  simp only [hi,hj]

theorem fullW_dyadic_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e U : ℝ) (a H : FreeRow→ℝ)
    (hR : ∀u∈R,u.val≠1 ∧ rowNorm u≤ U) :
    finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H =
      ∑k∈smallDyadicIndices U,
        finiteCentralFullWRows S hS hmax η (R∩dyadicRows 1 k) T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralFullWRows
  exact retained_dyadic_sum R U hR _

theorem fullW_cells_norm_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B U : ℝ) (idx grid : FreeRow→ℕ)
    (n m : ℕ) (N : ℂ) (A : ℝ) (hA : 0≤ A)
    (hR : ∀u∈R,u.val≠1 ∧ rowNorm u≤ U)
    (hlabel : ∀u∈R,idx u ≤ n ∧ grid u ≤ m)
    (hcell : ∀k∈smallDyadicIndices U,∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
      (cubeBinRows (R∩dyadicRows 1 k) idx grid i j).Nonempty →
      ‖finiteCentralFullWRows S hS hmax η (cubeBinRows (R∩dyadicRows 1 k) idx grid i j)
        T hT W Yp W0 W1 X Y Z e (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*B)/N‖≤ A) :
    ‖finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)/N‖ ≤
      ((smallDyadicIndices U).card:ℝ)*(n+1:ℕ)*(m+1:ℕ)*A := by
  rw [fullW_dyadic_partition S hS hmax η R T hT W Yp W0 W1 X Y Z e U _ _ hR,
    Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices U,(n+1:ℕ)*(m+1:ℕ)*A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      rw [fullW_bin_partition S hS hmax η (R∩dyadicRows 1 k) T hT W Yp W0 W1 X Y Z e B
        idx grid n m (fun u hu=>hlabel u (Finset.mem_inter.mp hu).1),Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),A := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro j hj
          by_cases hn : (cubeBinRows (R∩dyadicRows 1 k) idx grid i j).Nonempty
          · exact hcell k hk i hi j hj hn
          · have hempty:=Finset.not_nonempty_iff_eq_empty.mp hn
            simpa only [hempty,finiteCentralFullWRows,Finset.sum_empty,zero_div,norm_zero] using hA
        _ = _ := by simp;ring
    _ = _ := by simp;ring
end
end OAI.SevenEighths.Target830.Physical.FiniteNumerator

#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.fullW_bin_partition
#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.fullW_dyadic_partition
#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.fullW_cells_norm_bound
