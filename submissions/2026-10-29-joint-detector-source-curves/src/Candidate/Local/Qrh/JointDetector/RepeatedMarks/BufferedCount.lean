/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ActualWitnesses

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows

/-- Finite buffered-bin assembly. Each child keeps the original family on
its actual rows. Witness extension elsewhere is immaterial, and the literal
supported detector (including its long tail) is lowered to one common slope. -/
theorem count_of_buffered_witnesses {Label : Type} [Fintype Label]
    (rows : Finset FreeRow) (family : FreeRow→Label→Character)
    (hχ : ∀u : rows,∀j,(family u.val j).residue≠1)
    (U a₀ ε T allowance e tstar K : ℝ) (n : ℕ)
    (hU : 1<U) (hT : 2<T) (he : 0<e) (hn : 0<n)
    (hwidth : (49/100:ℝ)≤(n:ℝ)*e)
    (ha₀ : 51/100<a₀) (hK : 0≤K)
    (hzero : ∀u : rows,a₀+e≤HeckeDetectorZeros.zeroMaximum (family u.val) (hχ u) T)
    (hconstruct : ∀(F : Finset FreeRow)(hF : F⊆rows),F.Nonempty →
      ∀(a : ℝ)(i : ℕ),i≤n → a₀≤a → a≤1 →
      (∀u : F,a≤HeckeDetectorZeros.zeroMaximum (family u.val)
        (fun j=>hχ ⟨u.val,hF u.property⟩ j) ((3*i:ℕ)*T)) →
      (∀u : F,HeckeDetectorZeros.zeroMaximum (family u.val)
        (fun j=>hχ ⟨u.val,hF u.property⟩ j) (3*(i+1:ℕ)*T)<a+2*e) →
      ∃χ : FreeRow→Label→Character,(∀u∈F,χ u=family u) ∧
        Nonempty (∀u,SupportedWitness (χ u) U a ε tstar T allowance i))
    (hcount : ∀F : Finset FreeRow,F⊆rows → ∀(i : ℕ),i≤n →
      ∀χ : FreeRow→Label→Character,(∀u∈F,χ u=family u) →
      (∀u,SupportedWitness (χ u) U a₀ ε tstar T allowance i) → (F.card:ℝ)≤K) :
    (rows.card:ℝ)≤((n+1:ℕ):ℝ)*(⌈1/e⌉₊+2:ℕ)*K := by
  by_cases hneRows : rows.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hneRows]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨u₀,hu₀⟩ := hneRows
  obtain ⟨index,hindex⟩ := finite_buffered_free_bins rows family hχ T e a₀ n hT he hn hwidth hzero
  let f (u : FreeRow) := if hu : u∈rows then index ⟨u,hu⟩ else index ⟨u₀,hu₀⟩
  let child (p : Fin (n+1)×Fin (⌈1/e⌉₊+2)) := rows.filter (fun u=>f u=p)
  have hchild (p : Fin (n+1)×Fin (⌈1/e⌉₊+2)) : ((child p).card:ℝ)≤K := by
    have hsub : child p⊆rows := Finset.filter_subset _ _
    by_cases hne : (child p).Nonempty
    · have hd (u : child p) := hindex ⟨u.val,hsub u.property⟩
      have hid (u : child p) : index ⟨u.val,hsub u.property⟩=p :=
        by simpa only [f,dite_eq_left (hsub u.property)] using (Finset.mem_filter.mp u.property).2
      have hdata (u : child p) :
          a₀≤51/100+e*p.2.val ∧ 51/100+e*p.2.val≤1 ∧
          51/100+e*p.2.val≤HeckeDetectorZeros.zeroMaximum (family u.val)
            (fun j=>hχ ⟨u.val,hsub u.property⟩ j) ((3*p.1.val:ℕ)*T) ∧
          HeckeDetectorZeros.zeroMaximum (family u.val)
            (fun j=>hχ ⟨u.val,hsub u.property⟩ j) (3*(p.1.val+1:ℕ)*T)<51/100+e*p.2.val+2*e := by
        simpa only [hid u,Nat.cast_mul,Nat.cast_ofNat] using hd u
      obtain ⟨u,hu⟩ := hne
      obtain ⟨χ,hχ',⟨w⟩⟩ := hconstruct (child p) hsub ⟨u,hu⟩ _ p.1.val
        (Nat.le_of_lt_succ p.1.isLt) (hdata ⟨u,hu⟩).1 (hdata ⟨u,hu⟩).2.1
        (fun u=>(hdata u).2.2.1) (fun u=>(hdata u).2.2.2)
      have haBase := (hdata ⟨u,hu⟩).1
      exact hcount (child p) hsub p.1.val (Nat.le_of_lt_succ p.1.isLt) χ hχ'
        (fun u=>lower_supported_slope (w u) hU a₀ haBase)
    · simpa [Finset.not_nonempty_iff_eq_empty.mp hne] using hK
  have hpartition : rows.card=∑p, (child p).card := by
    simpa [child] using (Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
      (f:=f) (by simp))
  rw [hpartition,Nat.cast_sum]
  calc _ ≤ ∑p : Fin (n+1)×Fin (⌈1/e⌉₊+2),K := Finset.sum_le_sum (fun p _=>hchild p)
    _ = _ := by simp [mul_assoc]

end
end Qrh.JointDetector.RepeatedMarks
