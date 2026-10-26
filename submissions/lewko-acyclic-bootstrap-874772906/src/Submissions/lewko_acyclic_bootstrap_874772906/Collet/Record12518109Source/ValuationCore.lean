/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cones
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

theorem residue_add_left (i j : ℕ) : residue (i+6) j=residue i j := by
  unfold residue
  push_cast
  omega
theorem residue_add_right (i j : ℕ) : residue i (j+6)=residue i j := by
  unfold residue
  push_cast
  omega

def orderedStepLeft (c : Cell) : ℝ :=
  (2-17/50-17/25)*(c.q/K)+1+17/50*(c.q/c.priorL)+17/25*(c.q/c.priorL)*c.priorB
def orderedStepRight (c : Cell) : ℝ := 1+17/25*(c.q/c.priorL)*(1-c.priorB)

theorem orderedLow_add_left (c : Cell) (i j : ℕ) :
    orderedLow c (i+6) j=orderedLow c i j-6*orderedStepLeft c := by
  simp only [orderedLow,localR,localL,localO,residue_add_left,residue_add_right,
    Nat.cast_add,Nat.cast_ofNat,orderedStepLeft]
  ring
theorem orderedLow_add_right (c : Cell) (i j : ℕ) :
    orderedLow c i (j+6)=orderedLow c i j-6*orderedStepRight c := by
  simp only [orderedLow,localR,localL,localO,residue_add_left,residue_add_right,
    Nat.cast_add,Nat.cast_ofNat,orderedStepRight]
  ring

/-- Finite residue representatives and nonincreasing six-step increments
cover every pair of strictly positive prime multiplicities. -/
theorem six_reduction (f : ℕ → ℕ → ℝ)
    (hbase : ∀ i j : ℕ, 0  <  i  →  i  ≤  6  →  0  <  j  →  j  ≤  6  →  f i j  ≤  0)
    (hleft : ∀ i j : ℕ, 0  <  i  →  0  <  j  →  f (i+6) j  ≤  f i j)
    (hright : ∀ i j : ℕ, 0  <  i  →  0  <  j  →  f i (j+6)  ≤  f i j) :
    ∀ i j : ℕ, 0  <  i  →  0  <  j  →  f i j  ≤  0 := by
  have h : ∀ n : ℕ, ∀ i j : ℕ, i+j = n  →  0  <  i  →  0  <  j  →  f i j  ≤  0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih => 
      intro i j hij hi hj
      by_cases hi6 : i ≤ 6
      · by_cases hj6 : j ≤ 6
        · exact hbase i j hi hi6 hj hj6
        · have hj' : 0  <  j-6 := by omega
          have hrec:=ih (i+(j-6)) (by omega) i (j-6) rfl hi hj'
          have hs:=hright i (j-6) hi hj'
          simpa [Nat.sub_add_cancel (by omega : 6 ≤ j)] using hs.trans hrec
      · have hi' : 0  <  i-6 := by omega
        have hrec:=ih ((i-6)+j) (by omega) (i-6) j rfl hi' hj
        have hs:=hleft (i-6) j hi' hj
        simpa [Nat.sub_add_cancel (by omega : 6 ≤ i)] using hs.trans hrec
  intro i j hi hj
  exact h (i+j) i j rfl hi hj

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.six_reduction
