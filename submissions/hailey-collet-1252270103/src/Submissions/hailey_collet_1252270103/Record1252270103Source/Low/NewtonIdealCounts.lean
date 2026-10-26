/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.NewtonMass
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Record1252270103Source
local notation "O" => ActualEisensteinCubic.O

def idealDividingPool (P : Finset (Ideal O)) (I : Ideal O) : Finset (Ideal O) :=
  P.filter (fun p=>p ∣ I)

def idealSetIndicator (S : Finset (Ideal O)) (I : Ideal O) : ℝ :=
  if ∀p∈S,p ∣ I then 1 else 0

def idealDvdIndicator (D I : Ideal O) : ℝ := if D ∣ I then 1 else 0

theorem ideal_dividing_pool_mul (P : Finset (Ideal O)) (D u : Ideal O)
    (hp : ∀p∈P,Prime p) :
    idealDividingPool P (D*u) = idealDividingPool P D ∪ idealDividingPool P u := by
  ext p
  by_cases hm : p∈P
  · simp only [idealDividingPool,Finset.mem_filter,Finset.mem_union,hm,true_and,(hp p hm).dvd_mul]
  · simp only [idealDividingPool,Finset.mem_filter,Finset.mem_union,hm,false_and,or_self]

theorem ideal_dividing_pool_disjoint (P : Finset (Ideal O)) (D u : Ideal O)
    (hp : ∀p∈P,Prime p) (hc : IsCoprime D u) :
    Disjoint (idealDividingPool P D) (idealDividingPool P u) := by
  apply Finset.disjoint_left.mpr
  intro p hd hu
  exact (hp p (Finset.mem_filter.mp hd).1).not_isUnit
    (hc.isUnit_of_dvd' (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp hu).2)

/-- The frozen and residual counts split only under actual coprimality. -/
theorem ideal_dividing_pool_count (P : Finset (Ideal O)) (D u : Ideal O)
    (hp : ∀p∈P,Prime p) (hc : IsCoprime D u) :
    (idealDividingPool P (D*u)).card = (idealDividingPool P D).card+(idealDividingPool P u).card := by
  rw [ideal_dividing_pool_mul P D u hp,Finset.card_union_of_disjoint
    (ideal_dividing_pool_disjoint P D u hp hc)]

/-- Shifted Newton is asserted before the pole; r0 is the actual frozen count. -/
theorem ideal_correction_shifted_powerset (P : Finset (Ideal O)) (D u : Ideal O)
    (hp : ∀p∈P,Prime p) (hc : IsCoprime D u)
    (hsmall : (idealDividingPool P (D*u)).card < P.card) :
    (P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P (D*u)).card) =
      ∑S∈(idealDividingPool P u).powerset,
        newtonCoefficient P.card (idealDividingPool P D).card S.card := by
  have hcount := ideal_dividing_pool_count P D u hp hc
  have hr : ((idealDividingPool P D).card:ℝ)+(idealDividingPool P u).card < P.card := by
    exact_mod_cast hcount ▸ hsmall
  have hn := corrected_pool_newton_powerset (idealDividingPool P u)
    P.card (idealDividingPool P D).card hr
  rw [hcount,Nat.cast_add]
  simpa only [sub_add_eq_sub_sub] using hn

/-- A finite polynomial in divisibility indicators, defined on every ideal,
including ideals outside the support where the rational correction has a pole. -/
def idealNewtonPolynomial (P : Finset (Ideal O)) (r0 depth : ℕ) (u : Ideal O) : ℝ :=
  ∑S∈P.powerset.filter (fun S=>S.card≤depth),
    newtonCoefficient P.card r0 S.card*idealSetIndicator S u

theorem dividing_powerset_filter (P : Finset (Ideal O)) (u : Ideal O) :
    (idealDividingPool P u).powerset = P.powerset.filter (fun S=>∀p∈S,p∣u) := by
  ext S
  simp only [Finset.mem_powerset,Finset.mem_filter,idealDividingPool,Finset.subset_iff]
  aesop

/-- The truncated polynomial agrees with the exact finite Newton sum whenever
its actual residual divisor count is within the fixed depth. -/
theorem idealNewtonPolynomial_on_support (P : Finset (Ideal O)) (r0 depth : ℕ) (u : Ideal O)
    (hcount : (idealDividingPool P u).card ≤ depth) :
    idealNewtonPolynomial P r0 depth u =
      ∑S∈(idealDividingPool P u).powerset,newtonCoefficient P.card r0 S.card := by
  rw [dividing_powerset_filter]
  unfold idealNewtonPolynomial
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hs : ∀p∈S,p∣u
  · have hsub : S ⊆ idealDividingPool P u := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_powerset.mp hS) hp,hs p hp⟩
    have hcard : S.card≤depth := (Finset.card_le_card hsub).trans hcount
    simp [idealSetIndicator,hs,hcard]
  · simp [idealSetIndicator,hs]

theorem ideal_correction_shifted_polynomial (P : Finset (Ideal O)) (D u : Ideal O) (depth : ℕ)
    (hp : ∀p∈P,Prime p) (hc : IsCoprime D u)
    (hcount : (idealDividingPool P u).card ≤ depth)
    (hsmall : (idealDividingPool P (D*u)).card < P.card) :
    (P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P (D*u)).card) =
      idealNewtonPolynomial P (idealDividingPool P D).card depth u := by
  rw [idealNewtonPolynomial_on_support P _ depth u hcount]
  exact ideal_correction_shifted_powerset P D u hp hc hsmall

/-- Marked-factor avoidance is a genuine pool prerequisite, not inferred from
squarefreeness of the ordinary pair. -/
theorem ideal_dividing_pool_drop_marked (P : Finset (Ideal O)) (M I J : Ideal O)
    (hp : ∀p∈P,Prime p) (havoid : ∀p∈P,¬p∣M) :
    idealDividingPool P (M*I*J)=idealDividingPool P (I*J) := by
  rw [mul_assoc,ideal_dividing_pool_mul P M (I*J) hp]
  have hz : idealDividingPool P M=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hm
    exact havoid p (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hm).2
  rw [hz,Finset.empty_union]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.ideal_dividing_pool_count
#print axioms QRH.Record1252270103Low.ideal_correction_shifted_polynomial
#print axioms QRH.Record1252270103Low.ideal_dividing_pool_drop_marked
