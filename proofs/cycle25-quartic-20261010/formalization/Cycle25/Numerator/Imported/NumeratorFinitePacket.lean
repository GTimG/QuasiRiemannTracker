import Cycle25.Numerator.Imported.NumeratorActualError

/-! Finite products of physical local coefficient polynomials. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def finiteCoefficient {ι : Type*} [Fintype ι] {n : ℕ} (c : ι → Fin n → ℂ)
    (j : ι → Fin n) : ℂ := ∏ i, c i (j i)

def finiteScale {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (j : ι → Fin n) : ℝ≥0 := ∏ i, Q i ^ (j i).val

theorem finiteScale_one_le {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ i, 1 ≤ Q i) (j : ι → Fin n) : 1 ≤ finiteScale Q j := by
  exact Finset.one_le_prod (fun i _ => one_le_pow₀ (hQ i))

theorem finite_packet_term {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (j : ι → Fin n) :
    (∏ i, c i (j i) * ((Q i : ℂ)^(-w))^(j i).val) =
      finiteCoefficient c j * (finiteScale Q j : ℂ)^(-w) := by
  rw [Finset.prod_mul_distrib]
  unfold finiteCoefficient finiteScale
  congr 1
  have hh := map_prod (positiveCpowHom (-w)) (fun i => Q i ^ (j i).val) Finset.univ
  simpa only [map_pow,positiveCpowHom,MonoidHom.coe_mk,OneHom.coe_mk] using hh.symm

theorem finite_packet_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) :
    (∏ i, ∑ j : Fin n, c i j * ((Q i : ℂ)^(-w))^j.val) =
      ∑ j : ι → Fin n, finiteCoefficient c j * (finiteScale Q j : ℂ)^(-w) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_packet_term Q c w j

theorem finite_packet_mass {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ i, 1 ≤ Q i) (c : ι → Fin n → ℂ) (sigma : ℝ) :
    (∑ j : ι → Fin n, ‖finiteCoefficient c j‖ * (finiteScale Q j : ℝ)^(-sigma)) =
      ∏ i, ∑ j : Fin n, ‖c i j * ((Q i : ℂ)^(-(sigma : ℂ)))^j.val‖ := by
  have he (j : ι → Fin n) : ‖finiteCoefficient c j‖ * (finiteScale Q j : ℝ)^(-sigma) =
      ∏ i, ‖c i (j i) * ((Q i : ℂ)^(-(sigma : ℂ)))^(j i).val‖ := by
    rw [←norm_prod,finite_packet_term,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by
        have hh := finiteScale_one_le Q hQ j
        exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh))]
    simp only [Complex.neg_re,Complex.ofReal_re]
  simp_rw [he]
  exact (Fintype.prod_sum (fun i : ι => fun j : Fin n =>
    ‖c i j * ((Q i : ℂ)^(-(sigma : ℂ)))^j.val‖)).symm

def errorCoefficientVector (η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (P : T) : Fin 4 → ℂ :=
  (actualErrorCoefficients η u P.val (hT P.val P.property) x z).vector

def errorTupleCoefficient (η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (j : T → Fin 4) : ℂ :=
  finiteCoefficient (errorCoefficientVector η u T hT x z) j

def errorTupleScale (T : Finset PrimeIdeal) (j : T → Fin 4) : ℝ≥0 :=
  finiteScale (fun P : T => primeScale P.val) j

theorem error_product_expansion (η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x w z : ℂ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    (∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x w z) =
      ∑ j : T → Fin 4, errorTupleCoefficient η u T hT x z j * (errorTupleScale T j : ℂ)^(-w) := by
  calc
    _ = ∏ P : T, ∑ j : Fin 4, errorCoefficientVector η u T hT x z P j *
        ((primeScale P.val : ℂ)^(-w))^j.val := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [errorCoefficientVector,cubic_vector_eval,actual_error_expansion η u P.val _
        (hη P.val P.property) x w z (hQ P.val P.property) hx hz]
      rfl
    _ = _ := finite_packet_expansion (fun P : T => primeScale P.val)
      (errorCoefficientVector η u T hT x z) w

theorem error_product_coefficient_mass (η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) :
    (∑ j : T → Fin 4, ‖errorTupleCoefficient η u T hT x z j‖ *
      (errorTupleScale T j : ℝ)^(-(1 / 2 - rho))) ≤
      ∏ P : T, 2880 * errorSize u P.val * (repeatedDeficit u P.val : ℝ)^rho := by
  have hmass := finite_packet_mass (fun P : T => primeScale P.val)
    (fun P => primeScale_one_le P.val) (errorCoefficientVector η u T hT x z) (1 / 2 - rho)
  apply le_trans (le_of_eq hmass)
  apply Finset.prod_le_prod₀
  · intro P hP
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · intro P hP
    unfold errorCoefficientVector
    rw [cubic_vector_mass _ _ _ (by
      have hh := primeScale_one_le P.val
      exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh))]
    simpa only [Complex.ofReal_re,primeScale,NNReal.coe_natCast] using
      actual_error_coefficient_mass η u P.val _ (hη P.val P.property)
        x z alpha eps rho (hQ P.val P.property) halpha halpha1 heps heps1 hx hz hrho hrho1 hline

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
