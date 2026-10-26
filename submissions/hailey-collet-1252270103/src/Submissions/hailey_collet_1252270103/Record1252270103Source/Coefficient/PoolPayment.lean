/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedAmplifier

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

def dividingPool (P : Finset O) (a : O) : Finset O := P.filter (fun p => p ∣ a)

theorem pool_partition_card (P : Finset O) (a : O) :
    (dividingPool P a).card+(eligiblePool P a).card=P.card := by
  exact Finset.card_filter_add_card_filter_not (s:=P) (fun p=>p∣a)

theorem eligiblePool_nonempty_of_card_lt (P : Finset O) (a : O)
    (h : (dividingPool P a).card < P.card) : (eligiblePool P a).Nonempty := by
  have hh := pool_partition_card P a
  apply Finset.card_pos.mp
  omega

/-- The usual P>2R support condition gives the exact coefficient bound, without
using it as a comparison between two non-diagonal quadratic norms. -/
theorem correctedCoefficient_norm_le_two {α : Type*} (P : Finset O)
    (a : α → O) (c : α → ℂ) (i : α)
    (hP : P.Nonempty) (hhalf : 2*(dividingPool P (a i)).card ≤ P.card) :
    ‖correctedCoefficient P a c i‖ ≤ 2*‖c i‖ := by
  have hpart := pool_partition_card P (a i)
  have hPpos : 0<P.card := hP.card_pos
  have hepos : 0<(eligiblePool P (a i)).card := by omega
  have hn : (0:ℝ)<(eligiblePool P (a i)).card := Nat.cast_pos.mpr hepos
  have hr : (P.card:ℝ)≤2*((eligiblePool P (a i)).card:ℝ) := by exact_mod_cast (show P.card≤2*(eligiblePool P (a i)).card by omega)
  unfold correctedCoefficient
  rw [norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hn).mpr hr) (norm_nonneg _)

/-- CA6 for every actual frequency. Zero columns are retained in S, preserving
the actual Fourier-cardinality and full-zero-filter conventions. -/
theorem corrected_pool_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset O) (hP : P.Nonempty) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hg : ∀ p ∈ P, goodLambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hsq : ∀ i ∈ S, c i ≠ 0 → ∀ p ∈ P, ¬p^2 ∣ a i)
    (hsmall : ∀ i ∈ S, c i ≠ 0 → (dividingPool P (a i)).card < P.card)
    (h : O) :
    ‖gaussPolynomial S a ha c h‖^2 ≤ (P.card : ℝ)⁻¹ *
      ∑ p ∈ P, ‖gaussPolynomial S a ha (correctedCoefficient P a c) (p^6*h)‖^2 := by
  rw [corrected_pool_identity S a ha c P hP hp hs hg hc hsq
    (fun i hi hci=>eligiblePool_nonempty_of_card_lt P (a i) (hsmall i hi hci)) h]
  exact norm_average_sq P hP _

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.pool_partition_card
#print axioms OAI.SevenEighths.Record1252270103Source.correctedCoefficient_norm_le_two
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_pool_bound
