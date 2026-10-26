/- Copyright (c) 2026 Sil. Apache-2.0.
The finite uncoupling behind the repeated-prime Poisson step. Cross factors
are moved into the row variable; no factor is discarded as independent.
The resulting bounds use literal finite operator norms, not OptimalBound. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SievePairPoisson

set_option autoImplicit false
namespace Candidate.FourthPower.SieveUncoupling
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open SexticSieve SieveCoupling SieveOperator
local notation "Id" => Ideal ActualEisensteinCubic.O
local notation "Coord" => EisensteinEPrimaryPhase.Coord

def crossKernel (U V R T K : Id) : ℂ :=
  rowValue T U * star (rowValue R V) * star (rowValue K (R*U)) * rowValue K (T*V)

def crossPhase (U V : Id) (r t : Coord) : ℂ :=
  phase (ray U) t * star (phase (ray V) r)

theorem crossPhase_norm (U V : Id) (r t : Coord) : ‖crossPhase U V r t‖ ≤ 1 := by
  rw [crossPhase, norm_mul, norm_star]
  exact (mul_le_mul (phase_norm_le _ _) (phase_norm_le _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The repeated-prime parts U,V enlarge the opposite frequency variable.
This is why the coefficients need not be allowed to depend on that variable. -/
theorem cross_factor (U V R T K : Id)
    (hU : Supported U) (hV : Supported V) (hR : Supported R) (hT : Supported T) :
    crossKernel U V R T K = crossPhase U V (ray R) (ray T) *
      star (rowValue K U) * rowValue K V *
      star (rowValue (K*V) R) * rowValue (K*U) T := by
  have split (A B : Id) : rowValue K (A*B) = rowValue K A * rowValue K B :=
    map_mul (idealRowHom (primaryGenerator K)) A B
  rw [crossKernel, split, split, row_reciprocity T U hT hU, row_reciprocity R V hR hV,
    row_mul K V R, row_mul K U T]
  simp only [star_mul, crossPhase]
  ring

theorem frozen_sum (U V K : Id) (Rs Ts : Finset Id) (r t : Coord)
    (hU : Supported U) (hV : Supported V)
    (hR : ∀ R ∈ Rs, Supported R ∧ ray R = r)
    (hT : ∀ T ∈ Ts, Supported T ∧ ray T = t) (a b : Id → ℂ) :
    (∑ R ∈ Rs, ∑ T ∈ Ts, a R * b T * crossKernel U V R T K) =
      crossPhase U V r t * star (rowValue K U) * rowValue K V *
      (∑ R ∈ Rs, a R * star (rowValue (K*V) R)) *
      (∑ T ∈ Ts, b T * rowValue (K*U) T) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hTs
  apply Finset.sum_congr rfl
  intro R hRs
  rw [cross_factor U V R T K hU hV (hR R hRs).1 (hT T hTs).1,
    (hR R hRs).2, (hT T hTs).2]
  ring

theorem finite_bilinear {α : Type*} (s : Finset α) (w f g : α → ℂ)
    (hw : ∀ k ∈ s, ‖w k‖ ≤ 1) :
    ‖∑ k ∈ s, w k * f k * g k‖^2 ≤
      (∑ k ∈ s, ‖f k‖^2) * (∑ k ∈ s, ‖g k‖^2) := by
  have ht : ‖∑ k ∈ s, w k * f k * g k‖ ≤ ∑ k ∈ s, ‖f k‖ * ‖g k‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun k => ‖f k‖) (fun k => ‖g k‖))

theorem frozen_bound (U V : Id) (Ks Rs Ts : Finset Id) (r t : Coord)
    (hU : Supported U) (hV : Supported V)
    (hR : ∀ R ∈ Rs, Supported R ∧ ray R = r)
    (hT : ∀ T ∈ Ts, Supported T ∧ ray T = t) (a b : Id → ℂ) :
    ‖∑ K ∈ Ks, ∑ R ∈ Rs, ∑ T ∈ Ts, a R * b T * crossKernel U V R T K‖^2 ≤
      (∑ K ∈ Ks, ‖∑ R ∈ Rs, a R * star (rowValue (K*V) R)‖^2) *
      (∑ K ∈ Ks, ‖∑ T ∈ Ts, b T * rowValue (K*U) T‖^2) := by
  simp_rw [frozen_sum U V _ Rs Ts r t hU hV hR hT a b]
  apply finite_bilinear
  intro K _
  simp only [norm_mul, norm_star]
  have hp := crossPhase_norm U V r t
  have hu : ‖rowValue K U‖ ≤ 1 := idealRowHom_norm _ _
  have hv : ‖rowValue K V‖ ≤ 1 := idealRowHom_norm _ _
  exact (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) hp) (norm_nonneg _)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hu).trans hv)

open IdealMobiusDivisorSum

theorem product_fiber_card (Ds Ks : Finset Id) (Q : Id) (hQ : Q ≠ 0) :
    ((Ds ×ˢ Ks).filter (fun z => z.1*z.2 = Q)).card ≤ (idealDivisors Q).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro z hz
    exact (mem_idealDivisors hQ).mpr ⟨z.2, (Finset.mem_filter.mp hz).2.symm⟩
  · intro z hz t ht hzt
    apply Prod.ext hzt
    have he := (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp ht).2.symm
    have hn : t.1 ≠ 0 := by
      intro h
      have hzero := (Finset.mem_filter.mp ht).2
      rw [h, zero_mul] at hzero
      exact hQ hzero.symm
    rw [hzt] at he
    exact mul_left_cancel₀ hn he

/-- The frequencies enlarged by the repeated-prime part have only divisor
multiplicity. The inner coefficients remain common to every original row. -/
theorem product_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ds Ks Qs columns : Finset Id) (L : ℝ), 0 ≤ L →
      (∀ D ∈ Ds, ∀ K ∈ Ks, D*K ∈ Qs) →
      (∀ Q ∈ Qs, Q ≠ 0 ∧ (Ideal.absNorm Q : ℝ) ≤ L) →
      ∀ a : Id → ℂ,
        (∑ D ∈ Ds, ∑ K ∈ Ks, ‖∑ I ∈ columns, a I * rowValue (D*K) I‖^2) ≤
          C*L^ε * squaredNorm Qs columns * coefficientMass columns a := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro Ds Ks Qs columns L hL hmap hQs a
  let F : Id → ℝ := fun Q => ‖∑ I ∈ columns, a I * rowValue Q I‖^2
  have hmaps : ∀ z ∈ Ds ×ˢ Ks, z.1*z.2 ∈ Qs := fun z hz =>
    hmap z.1 (Finset.mem_product.mp hz).1 z.2 (Finset.mem_product.mp hz).2
  have hfib : (∑ z ∈ Ds ×ˢ Ks, F (z.1*z.2)) ≤ C*L^ε * ∑ Q ∈ Qs, F Q := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Q hQ
    have hc : (((Ds ×ˢ Ks).filter (fun z => z.1*z.2 = Q)).card : ℝ) ≤ C*L^ε := by
      calc
        _ ≤ ((idealDivisors Q).card : ℝ) := Nat.cast_le.mpr (product_fiber_card Ds Ks Q (hQs Q hQ).1)
        _ ≤ C*(Ideal.absNorm Q : ℝ)^ε := hdiv Q (hQs Q hQ).1
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hQs Q hQ).2 hε.le) hC.le
    calc
      _ = (((Ds ×ˢ Ks).filter (fun z => z.1*z.2 = Q)).card : ℝ) * F Q := by
        rw [show (∑ z ∈ (Ds ×ˢ Ks).filter (fun z => z.1*z.2 = Q), F (z.1*z.2)) =
            ∑ _z ∈ (Ds ×ˢ Ks).filter (fun z => z.1*z.2 = Q), F Q from
          Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2])]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have hbase : (∑ Q ∈ Qs, F Q) ≤ squaredNorm Qs columns * coefficientMass columns a :=
    energy_bound Qs columns a
  calc
    _ = ∑ z ∈ Ds ×ˢ Ks, F (z.1*z.2) := (Finset.sum_product _ _ _).symm
    _ ≤ C*L^ε * ∑ Q ∈ Qs, F Q := hfib
    _ ≤ C*L^ε * (squaredNorm Qs columns * coefficientMass columns a) :=
      mul_le_mul_of_nonneg_left hbase (mul_nonneg hC.le (Real.rpow_nonneg hL _))
    _ = _ := by ring

end
end Candidate.FourthPower.SieveUncoupling
