/- Copyright (c) 2026 Sil. Apache-2.0.
Reuses the baseline's unique sixth-power factorization. All masks are retained.
This finite identity does not assert the outstanding sextic large-sieve bound. -/
import Candidate.SilPrior.FourthPower.SexticSieve
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CenteredExceptionalCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SixthDecomposition
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open UniqueFactorizationMonoid SexticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem remainder_powerFree (I : Id) : PowerFree 6 (sixthRemainder I) := by
  intro P hP hd
  have hpos : 0 < valuation P P :=
    Multiset.count_pos.mpr ((mem_normalizedFactors_iff hP.ne_zero).mpr ⟨hP,dvd_rfl⟩)
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors
    (pow_ne_zero 6 hP.ne_zero) (sixthRemainder_ne_zero I)).mp hd
  have hc := (Multiset.le_iff_count.mp hle) P
  change valuation (P^6) P ≤ valuation (sixthRemainder I) P at hc
  rw [valuation_pow] at hc
  have ht := sixthRemainder_valuation_lt I P
  omega

theorem supported_dvd {I J : Id} (hI : Supported I) (hJ : J ∣ I) : Supported J := by
  obtain ⟨B,rfl⟩ := hJ
  exact ((supported_mul_iff J B).mp hI).1

theorem remainder_supported (I : Id) (hI : Supported I) : Supported (sixthRemainder I) :=
  supported_dvd hI ⟨sixthQuotient I^6,(sixth_normal_form I hI.1).symm⟩

theorem quotient_supported (I : Id) (hI : Supported I) : Supported (sixthQuotient I) := by
  apply supported_dvd hI
  apply (dvd_pow_self (sixthQuotient I) (by decide : 6 ≠ 0)).trans
  exact ⟨sixthRemainder I, by rw [mul_comm, sixth_normal_form I hI.1]⟩

def maskedCoefficient (a : Id → ℂ) (D I : Id) : ℂ :=
  a I * (if IsCoprime I D then 1 else 0)

theorem row_sum_extraction (R : Id) (hR : Supported R) (columns : Finset Id)
    (hc : ∀ I ∈ columns, Supported I) (a : Id → ℂ) :
    (∑ I ∈ columns, a I * rowValue R I) =
      ∑ I ∈ columns, maskedCoefficient a (sixthQuotient R) I * rowValue (sixthRemainder R) I := by
  apply Finset.sum_congr rfl
  intro I hI
  have he : rowValue R I = rowValue (sixthRemainder R) I *
      (if IsCoprime I (sixthQuotient R) then 1 else 0) := by
    calc
      _ = rowValue (sixthRemainder R * sixthQuotient R^6) I := by rw [sixth_normal_form R hR.1]
      _ = _ := row_sixth_power _ _ I (quotient_supported R hR) (hc I hI)
  rw [he]
  dsimp [maskedCoefficient]
  ring

def rootFiber (rows : Finset Id) (D : Id) : Finset Id :=
  rows.filter (fun R => sixthQuotient R = D)

def reducedRows (rows : Finset Id) (D : Id) : Finset Id :=
  (rootFiber rows D).image sixthRemainder

theorem remainder_injective_on_fiber (rows : Finset Id) (hrows : ∀ R ∈ rows, Supported R)
    (D : Id) : Set.InjOn sixthRemainder (rootFiber rows D) := by
  intro I hI J hJ hIJ
  obtain ⟨hI,hID⟩ := Finset.mem_filter.mp hI
  obtain ⟨hJ,hJD⟩ := Finset.mem_filter.mp hJ
  calc
    I = sixthRemainder I * sixthQuotient I^6 := (sixth_normal_form I (hrows I hI).1).symm
    _ = sixthRemainder J * sixthQuotient J^6 := by rw [hIJ,hID,hJD]
    _ = J := sixth_normal_form J (hrows J hJ).1

theorem exact_energy_decomposition (rows columns : Finset Id)
    (hr : ∀ R ∈ rows, Supported R) (hc : ∀ I ∈ columns, Supported I) (a : Id → ℂ) :
    energy rows columns a =
      ∑ D ∈ rows.image sixthQuotient, energy (reducedRows rows D) columns (maskedCoefficient a D) := by
  unfold energy
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun R hR => Finset.mem_image.mpr ⟨R,hR,rfl⟩ : ∀ R ∈ rows, sixthQuotient R ∈ rows.image sixthQuotient)]
  apply Finset.sum_congr rfl
  intro D _
  rw [reducedRows, Finset.sum_image (remainder_injective_on_fiber rows hr D)]
  apply Finset.sum_congr rfl
  intro R hR
  obtain ⟨hR,hRD⟩ := Finset.mem_filter.mp hR
  rw [row_sum_extraction R (hr R hR) columns hc a,hRD]

theorem row_scale (I : Id) (hI : Supported I) (A : ℝ) (hA : (Ideal.absNorm I : ℝ) ≤ A) :
    (Ideal.absNorm (sixthRemainder I) : ℝ) ≤
      A / (Ideal.absNorm (sixthQuotient I) : ℝ)^6 := by
  have hq : 0 < (Ideal.absNorm (sixthQuotient I) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (sixthQuotient_ne_zero I)))
  apply (le_div_iff₀ (pow_pos hq 6)).mpr
  have he := congrArg (fun J : Id => (Ideal.absNorm J : ℝ)) (sixth_normal_form I hI.1)
  simp only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] at he
  exact he.trans_le hA

theorem column_sixth_power (R I D : Id) (hR : Supported R) (hD : Supported D) :
    rowValue R (I*D^6) = rowValue R I * (if IsCoprime D R then 1 else 0) := by
  dsimp only [rowValue]
  rw [map_mul,map_pow,← idealRowHom_argument_pow _ 6 D hD,idealRowHom_sixth_mask _ D hD,
    (primaryGenerator_spec R (supported_primaryGenerator_ne_zero R hR)).1]

theorem central_root_weight (D : Id) :
    ((Ideal.absNorm D : ℝ)^6)^(-(1/2 : ℝ)) = (Ideal.absNorm D : ℝ)^(-3 : ℝ) := by
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _) 6]
  norm_num

/-- Absolute root masses are summable, also after any small divisor loss
that leaves the exponent greater than one. -/
theorem root_weight_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun D : {I : Id // Supported I} => (Ideal.absNorm D.val : ℝ)^(-σ)) := by
  have ht := (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ)
    (by simpa using hσ)).comp_injective (i := fun D : {I : Id // Supported I} => D.val)
    Subtype.val_injective
  apply ht.congr
  intro D
  simp only [Function.comp_def,CubicEisenstein.fullIdealWeight,ite_eq_right D.property.1]
  have hN : 0 < (Ideal.absNorm D.val : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.property.1))
  simpa only [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos hN (-(σ : ℂ)))

end
end Candidate.SilPrior.FourthPower.SixthDecomposition
