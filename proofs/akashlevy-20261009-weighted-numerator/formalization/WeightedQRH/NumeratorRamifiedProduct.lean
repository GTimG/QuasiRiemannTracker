import WeightedQRH.NumeratorPrimeExpansion
import OAI.NumberTheory.DirichletL.PrimeRows.FirstContinuation

/-! Finite coefficient expansion and subpower mass of the actual ramified product. -/
noncomputable section
open scoped BigOperators NNReal Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def actualRamifiedCoefficients (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : QuadraticCoefficients :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedCorrectionCoefficients p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)

theorem actual_ramified_expansion (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z =
      (actualRamifiedCoefficients η u P hs x z).eval ((P.val.absNorm : ℂ) ^ (-w)) := by
  dsimp only [ramifiedCorrection, actualRamifiedCoefficients]
  erw [ramified_correction_expansion]
  simp only [span_primaryGenerator_of_supported P.val hs]

theorem actual_ramified_coefficient_mass (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ) ≤ P.val.absNorm) (x z : ℂ) (sigma : ℝ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma) :
    (actualRamifiedCoefficients η u P hs x z).mass ((P.val.absNorm : ℝ) ^ (-sigma)) ≤ 579 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p} = P.val := span_primaryGenerator_of_supported P.val hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hh := ramified_correction_coefficient_mass p hp hg.1 hg.2
    (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x z sigma
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) (actualACube_norm_le η p)
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp))
    hx hsigma hz hxw (multiplicity p u.val) (multiplicity_lt_six u p hp)
  change (ramifiedCorrectionCoefficients p hp hg.1 (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)).mass _ ≤ _
  simpa only [hspan] using hh

def ramifiedCoefficientVector (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (P : ramifiedPrimes S u) : Fin 3 → ℂ :=
  (actualRamifiedCoefficients η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x z).vector

def ramifiedTupleCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (j : ramifiedPrimes S u → Fin 3) : ℂ :=
  ∏ P, ramifiedCoefficientVector S hS η u x z P (j P)

def ramifiedTupleScale (S : Finset (Ideal O)) (u : FreeRow)
    (j : ramifiedPrimes S u → Fin 3) : ℝ≥0 := ∏ P, primeScale P.val ^ (j P).val

theorem ramified_product_expansion (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    ramifiedProduct S hS η u x w z =
      ∑ j : ramifiedPrimes S u → Fin 3,
        ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w) := by
  have he (j : ramifiedPrimes S u → Fin 3) :
      (∏ P, ramifiedCoefficientVector S hS η u x z P (j P) *
        ((primeScale P.val : ℂ) ^ (-w)) ^ (j P).val) =
      ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w) := by
    rw [Finset.prod_mul_distrib]
    unfold ramifiedTupleCoefficient ramifiedTupleScale
    congr 1
    have hh := map_prod (positiveCpowHom (-w)) (fun P : ramifiedPrimes S u =>
      primeScale P.val ^ (j P).val) Finset.univ
    simpa only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] using hh.symm
  simp_rw [← he]
  rw [← Fintype.prod_sum (fun P : ramifiedPrimes S u => fun j : Fin 3 =>
    ramifiedCoefficientVector S hS η u x z P j * ((primeScale P.val : ℂ) ^ (-w)) ^ j.val)]
  unfold ramifiedProduct
  change (∏ P : ramifiedPrimes S u,
    ramifiedCorrection η u P.val
      (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z) = _
  apply Finset.prod_congr rfl
  intro P hP
  rw [ramifiedCoefficientVector, quadratic_vector_eval, actual_ramified_expansion]
  rfl

theorem ramified_product_coefficient_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (sigma : ℝ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma) :
    (∑ j : ramifiedPrimes S u → Fin 3,
      ‖ramifiedTupleCoefficient S hS η u x z j‖ *
        (ramifiedTupleScale S u j : ℝ) ^ (-sigma)) ≤ 579 ^ (ramifiedPrimes S u).card := by
  have he (j : ramifiedPrimes S u → Fin 3) :
      ‖ramifiedTupleCoefficient S hS η u x z j‖ * (ramifiedTupleScale S u j : ℝ) ^ (-sigma) =
      ∏ P : ramifiedPrimes S u,
        ‖ramifiedCoefficientVector S hS η u x z P (j P) *
          ((primeScale P.val : ℂ) ^ (-(sigma : ℂ))) ^ (j P).val‖ := by
    have hpos : 0 < (ramifiedTupleScale S u j : ℝ) := by
      unfold ramifiedTupleScale
      exact_mod_cast Finset.prod_pos (fun (P : ramifiedPrimes S u) _ => pow_pos (lt_of_lt_of_le
        (by norm_num : (0 : ℝ≥0) < 1) (primeScale_one_le P.val)) _)
    have hn := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-(sigma : ℂ))
    simp only [Complex.neg_re, Complex.ofReal_re] at hn
    rw [← hn]
    simp only [Complex.neg_re, Complex.ofReal_re, ← norm_mul]
    unfold ramifiedTupleCoefficient ramifiedTupleScale
    have hh := map_prod (positiveCpowHom (-(sigma : ℂ))) (fun P : ramifiedPrimes S u =>
      primeScale P.val ^ (j P).val) Finset.univ
    simp only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hh
    rw [hh, ← Finset.prod_mul_distrib, norm_prod]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun P : ramifiedPrimes S u => fun j : Fin 3 =>
    ‖ramifiedCoefficientVector S hS η u x z P j * ((primeScale P.val : ℂ) ^ (-(sigma : ℂ))) ^ j.val‖)]
  calc
    _ ≤ ∏ _P : ramifiedPrimes S u, (579 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro P hP
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      · intro P hP
        unfold ramifiedCoefficientVector
        rw [quadratic_vector_mass _ _ _ (by
          have := primeScale_one_le P.val
          exact lt_of_lt_of_le zero_lt_one this)]
        exact actual_ramified_coefficient_mass η u P.val _
          (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
          x z sigma hx hsigma hz hxw
    _ = _ := by simp

end WeightedQRH.Numerator
