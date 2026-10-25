/- Copyright (c) 2026 Sil. Apache-2.0.
The repeated-prime cross factors in the sextic root-number calculation.
This is the character-algebra part of de Faveri Lemma 3.3; the connection
to the paired Gauss sum is a separate obligation, not a hypothesis here. -/
import Candidate.Feedback.FourthPower.SieveOperator
import Candidate.Feedback.FourthPower.SievePrimitive

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.SieveCoupling
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ActualEisensteinCubic
open UniqueFactorizationMonoid SexticSieve SievePrimitive
local notation "Id" => Ideal ActualEisensteinCubic.O

def sharp (I : Id) : Id := ∏ P : PrimeIndex I, P.val^(exponent I P - 1)

theorem radical_product (I : Id) (hI : I ≠ 0) :
    (∏ P : PrimeIndex I, P.val) = I.radical :=
  (span_finitePrimeModulus _).symm.trans (span_modulus I hI)

theorem normal_form (I : Id) (hI : I ≠ 0) : I.radical * sharp I = I := by
  rw [← radical_product I hI, sharp, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ P : PrimeIndex I, P.val^(exponent I P) := by
      apply Finset.prod_congr rfl
      intro P _
      rw [← pow_succ', Nat.sub_add_cancel (exponent_pos I P)]
    _ = I := by
      dsimp only [exponent]
      rw [Finset.prod_coe_sort (s := primeSupport I)
        (f := fun P => P^((normalizedFactors I).count P))]
      rw [primeSupport, ← Finset.prod_multiset_count]
      exact Ideal.prod_normalizedFactors_eq_self hI

theorem radical_supported (I : Id) (hI : Supported I) : Supported I.radical :=
  SixthDecomposition.supported_dvd hI (Ideal.dvd_iff_le.mpr I.le_radical)

theorem sharp_supported (I : Id) (hI : Supported I) : Supported (sharp I) :=
  SixthDecomposition.supported_dvd hI ⟨I.radical, by rw [mul_comm, normal_form I hI.1]⟩

theorem norm_normal_form (I : Id) (hI : I ≠ 0) :
    (Ideal.absNorm I.radical : ℝ) * Ideal.absNorm (sharp I) = Ideal.absNorm I := by
  have h := congrArg (fun J : Id => (Ideal.absNorm J : ℝ)) (normal_form I hI)
  simpa only [map_mul, Nat.cast_mul] using h

theorem row_mul (R S I : Id) : rowValue (R*S) I = rowValue R I * rowValue S I := by
  simp only [rowValue, primaryGenerator_mul, idealRowHom_argument_mul]

theorem row_norm_one (R I : Id) (hR : Supported R) (hI : Supported I)
    (hcop : IsCoprime I R) : ‖rowValue R I‖ = 1 := by
  have hs : rowValue R I ^ 6 = 1 := by
    dsimp only [rowValue]
    rw [← idealRowHom_argument_pow _ 6 I hI, idealRowHom_sixth_mask _ I hI,
      (primaryGenerator_spec R (supported_primaryGenerator_ne_zero R hR)).1, ite_eq_left hcop]
  have hn := congrArg norm hs
  simp only [norm_pow, norm_one] at hn
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (6 : ℕ) ≠ 0)).mp
    (hn.trans (one_pow 6).symm)

theorem radical_coprime (I J : Id) (hcop : IsCoprime I J) : IsCoprime I.radical J.radical :=
  (hcop.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr I.le_radical)).of_isCoprime_of_dvd_right
    (Ideal.dvd_iff_le.mpr J.le_radical)

/-- The two cross terms remain correlated through the repeated-prime parts.
Only the squarefree pair cancels to a fixed finite ray phase. -/
theorem cross_coupling (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) :
    rowValue I J.radical * star (rowValue J I.radical) =
      SieveOperator.phase (SieveOperator.ray J.radical) (SieveOperator.ray I.radical) *
        rowValue (sharp I) J.radical * star (rowValue (sharp J) I.radical) := by
  have hRI := radical_supported I hI
  have hRJ := radical_supported J hJ
  have hn := row_norm_one J.radical I.radical hRJ hRI (radical_coprime I J hcop)
  have hunit : rowValue J.radical I.radical * star (rowValue J.radical I.radical) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hn]
    norm_num
  have hbase : rowValue I.radical J.radical * star (rowValue J.radical I.radical) =
      SieveOperator.phase (SieveOperator.ray J.radical) (SieveOperator.ray I.radical) := by
    rw [SieveOperator.row_reciprocity _ _ hRI hRJ, mul_assoc, hunit, mul_one]
  have hi : rowValue I J.radical = rowValue I.radical J.radical * rowValue (sharp I) J.radical := by
    rw [← row_mul, normal_form I hI.1]
  have hj : rowValue J I.radical = rowValue J.radical I.radical * rowValue (sharp J) I.radical := by
    rw [← row_mul, normal_form J hJ.1]
  rw [hi, hj, star_mul]
  calc
    _ = (rowValue I.radical J.radical * star (rowValue J.radical I.radical)) *
        rowValue (sharp I) J.radical * star (rowValue (sharp J) I.radical) := by ring
    _ = _ := by rw [hbase]

theorem column_coupling (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) :
    rowValue J.radical I * star (rowValue I.radical J) =
      SieveOperator.phase (SieveOperator.ray I.radical) (SieveOperator.ray J.radical) *
        rowValue J.radical (sharp I) * star (rowValue I.radical (sharp J)) := by
  have hRI := radical_supported I hI
  have hRJ := radical_supported J hJ
  have hn := row_norm_one I.radical J.radical hRI hRJ (radical_coprime I J hcop).symm
  have hunit : rowValue I.radical J.radical * star (rowValue I.radical J.radical) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hn]
    norm_num
  have hbase : rowValue J.radical I.radical * star (rowValue I.radical J.radical) =
      SieveOperator.phase (SieveOperator.ray I.radical) (SieveOperator.ray J.radical) := by
    rw [SieveOperator.row_reciprocity _ _ hRJ hRI, mul_assoc, hunit, mul_one]
  have split (K L : Id) (hK : K ≠ 0) :
      rowValue L K = rowValue L K.radical * rowValue L (sharp K) := by
    dsimp only [rowValue]
    rw [← map_mul, normal_form K hK]
  rw [split I J.radical hI.1, split J I.radical hJ.1, star_mul]
  calc
    _ = (rowValue J.radical I.radical * star (rowValue I.radical J.radical)) *
        rowValue J.radical (sharp I) * star (rowValue I.radical (sharp J)) := by ring
    _ = _ := by rw [hbase]

end
end Candidate.Feedback.FourthPower.SieveCoupling
