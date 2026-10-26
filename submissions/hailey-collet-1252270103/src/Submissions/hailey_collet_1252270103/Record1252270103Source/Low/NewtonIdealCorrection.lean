/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.NewtonIdealAllocation
import Mathlib.Algebra.BigOperators.Associated

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Record1252270103Source
local notation "O" => ActualEisensteinCubic.O

theorem pool_avoids_marked_product {ι : Type*} (P : Finset (Ideal O))
    (slots : Finset ι) (marked : ι→Ideal O) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,∀i∈slots,¬p∣marked i) :
    ∀p∈P,¬p∣∏i∈slots,marked i := by
  intro p hm
  exact (hp p hm).not_dvd_finsetProd (havoid p hm)

theorem ideal_set_indicator_drop_marked (P S : Finset (Ideal O)) (M I J : Ideal O)
    (hp : ∀p∈P,Prime p) (hS : S⊆P) (havoid : ∀p∈P,¬p∣M) :
    idealSetIndicator S (M*I*J)=idealSetIndicator S (I*J) := by
  have heq : (∀p∈S,p∣M*I*J) ↔ (∀p∈S,p∣I*J) := by
    apply forall_congr'
    intro p
    apply forall_congr'
    intro hm
    rw [mul_assoc,(hp p (hS hm)).dvd_mul]
    simp only [havoid p (hS hm),false_or]
  simp only [idealSetIndicator,heq]

theorem idealNewtonPolynomial_drop_marked (P : Finset (Ideal O))
    (r0 depth : ℕ) (M I J : Ideal O) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,¬p∣M) :
    idealNewtonPolynomial P r0 depth (M*I*J)=idealNewtonPolynomial P r0 depth (I*J) := by
  unfold idealNewtonPolynomial
  apply Finset.sum_congr rfl
  intro S hS
  rw [ideal_set_indicator_drop_marked P S M I J hp
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) havoid]

/-- The actual shifted rational correction equals a fixed finite polynomial
of two ordinary ideal-divisibility projectors. Every support prerequisite is
explicit: frozen/residual coprimality, marked-slot avoidance, squarefreeness,
the fixed residual depth, and strict distance from the pole. -/
theorem ideal_correction_rectangular (P : Finset (Ideal O)) (D M I J : Ideal O)
    (depth : ℕ) (hp : ∀p∈P,Prime p) (hc : IsCoprime D (M*I*J))
    (havoid : ∀p∈P,¬p∣M) (hsf : Squarefree (I*J))
    (hdepth : (idealDividingPool P (I*J)).card≤depth)
    (hpole : (idealDividingPool P (D*(M*I*J))).card<P.card) :
    (P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P (D*(M*I*J))).card)=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),
        ∑A∈S.powerset,newtonCoefficient P.card (idealDividingPool P D).card S.card *
          (idealDvdIndicator (∏p∈A,p) I*idealDvdIndicator (∏p∈S\A,p) J) := by
  have hr : (idealDividingPool P (M*I*J)).card≤depth := by
    rwa [ideal_dividing_pool_drop_marked P M I J hp havoid]
  rw [ideal_correction_shifted_polynomial P D (M*I*J) depth hp hc hr hpole,
    idealNewtonPolynomial_drop_marked P _ depth M I J hp havoid,
    idealNewtonPolynomial_assignments P _ depth I J hp hsf]

/-- The same exact identity with the marked product written as the original
finite family. Avoidance is required for every marked slot. -/
theorem ideal_correction_marked_slots {ι : Type*} (P : Finset (Ideal O))
    (slots : Finset ι) (marked : ι→Ideal O) (D I J : Ideal O)
    (depth : ℕ) (hp : ∀p∈P,Prime p)
    (hc : IsCoprime D ((∏i∈slots,marked i)*I*J))
    (havoid : ∀p∈P,∀i∈slots,¬p∣marked i) (hsf : Squarefree (I*J))
    (hdepth : (idealDividingPool P (I*J)).card≤depth)
    (hpole : (idealDividingPool P (D*((∏i∈slots,marked i)*I*J))).card<P.card) :
    (P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P (D*((∏i∈slots,marked i)*I*J))).card)=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),
        ∑A∈S.powerset,newtonCoefficient P.card (idealDividingPool P D).card S.card *
          (idealDvdIndicator (∏p∈A,p) I*idealDvdIndicator (∏p∈S\A,p) J) :=
  ideal_correction_rectangular P D (∏i∈slots,marked i) I J depth hp hc
    (pool_avoids_marked_product P slots marked hp havoid) hsf hdepth hpole

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.pool_avoids_marked_product
#print axioms QRH.Record1252270103Low.idealNewtonPolynomial_drop_marked
#print axioms QRH.Record1252270103Low.ideal_correction_marked_slots
