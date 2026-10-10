import Cycle25.Numerator.Imported.NumeratorActualError
import Cycle25.Numerator.Imported.RowConductor

/-! The exact multiplicative conductor deficit of repeated physical error primes. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

theorem repeated_prime_square_dvd (u : FreeRow) (P : HeckeInverseAmplification.PrimeIdeal) (hs : Supported P.val)
    (hj : 2 ≤ multiplicity (primaryGenerator P.val) u.val) :
    P.val ^ 2 ∣ (Ideal.span {u.val} : Ideal O) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hm : p ^ multiplicity p u.val ∣ u.val := ⟨unitPart u p hp, (unitPart_spec u p hp).1⟩
  have hdiv : p ^ 2 ∣ u.val := (pow_dvd_pow p hj).trans hm
  rw [←span_primaryGenerator_of_supported P.val hs,Ideal.span_singleton_pow]
  exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hdiv

def repeatedErrorPrimes (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal) : Finset HeckeInverseAmplification.PrimeIdeal :=
  T.filter (fun P => P.val ∣ Ideal.span {u.val} ∧ 2 ≤ multiplicity (primaryGenerator P.val) u.val)

theorem repeated_deficit_product (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal) :
    (∏ P : T, (repeatedDeficit u P.val : ℝ)) =
      ∏ P ∈ repeatedErrorPrimes u T, (P.val.absNorm : ℝ) := by
  calc
    _ = ∏ P ∈ T, (repeatedDeficit u P : ℝ) := Finset.prod_coe_sort T _
    _ = _ := by
      simp only [repeatedDeficit,repeatedErrorPrimes,Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro P hP
      split_ifs <;> rfl


theorem radical_repeated_deficit (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) :
    ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) *
      (∏ P : T, (repeatedDeficit u P.val : ℝ)) ≤
        (Ideal.span {u.val} : Ideal O).absNorm := by
  let R := repeatedErrorPrimes u T
  have hdiv (P : R) : P.val.val ^ 2 ∣ (Ideal.span {u.val} : Ideal O) := by
    have hm := Finset.mem_filter.mp P.property
    exact repeated_prime_square_dvd u P.val (hT P.val hm.1) hm.2.2
  have hh := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    (fun P : R => P.val.val) (fun P => P.val.property)
    (fun P Q h => Subtype.ext (Subtype.ext h)) (fun _ => 2)
    (fun _ => by norm_num) hdiv
  simp only [show (2 : ℕ) - 1 = 1 by norm_num,pow_one] at hh
  have hh' : ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) *
      (∏ P : R, (P.val.val.absNorm : ℝ)) ≤ (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast hh
  rw [repeated_deficit_product]
  have he := Finset.prod_coe_sort R (fun P : HeckeInverseAmplification.PrimeIdeal => (P.val.absNorm : ℝ))
  rw [he] at hh'
  exact hh'

theorem conductor_repeated_deficit (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (C Cu : ℝ) (hC : 0 ≤ C)
    (hCu : Cu ≤ C * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ)) :
    Cu * (∏ P : T, (repeatedDeficit u P.val : ℝ)) ≤
      C * (Ideal.span {u.val} : Ideal O).absNorm := by
  have hd := radical_repeated_deficit u T hT
  have hn : 0 ≤ ∏ P : T, (repeatedDeficit u P.val : ℝ) :=
    Finset.prod_nonneg (fun _ _ => NNReal.coe_nonneg _)
  exact (mul_le_mul_of_nonneg_right hCu hn).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd hC)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
