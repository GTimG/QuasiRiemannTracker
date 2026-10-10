import WeightedQRH.NumeratorEulerExpansion
import OAI.NumberTheory.DirichletL.PrimeRows.FirstProduct

/-! Absolute Dirichlet expansion of the actual unramified correction product. -/
noncomputable section
open scoped BigOperators NNReal Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def QuadraticCoefficients.vector (c : QuadraticCoefficients) : Fin 3 → ℂ := ![c.a,c.b,c.c]

theorem quadratic_vector_eval (c : QuadraticCoefficients) (T : ℂ) :
    (∑ j : Fin 3, c.vector j * T ^ j.val) = c.eval T := by
  simp [QuadraticCoefficients.vector, QuadraticCoefficients.eval, quadratic, Fin.sum_univ_three]

theorem quadratic_vector_mass (c : QuadraticCoefficients) (Q : ℝ≥0) (w : ℂ)
    (hQ : 0 < (Q : ℝ)) :
    (∑ j : Fin 3, ‖c.vector j * ((Q : ℂ) ^ (-w)) ^ j.val‖) =
      c.mass ((Q : ℝ) ^ (-w.re)) := by
  simp [QuadraticCoefficients.vector, QuadraticCoefficients.mass, quadraticMass,
    Fin.sum_univ_three, norm_mul, norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]

def primeScale (P : PrimeIdeal) : ℝ≥0 := P.val.absNorm

def actualUnramifiedCoefficients (η : Character) (u : FreeRow) (x z : ℂ)
    (P : PrimeIdeal) : Fin 3 → ℂ :=
  if P.val ∣ Ideal.span {u.val} then 0 else
    (unramifiedDefectCoefficients P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z).vector

theorem actual_unramified_local_expansion (η : Character) (u : FreeRow) (x w z : ℂ)
    (P : PrimeIdeal) (hP : 4 ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    unramifiedFactor η u P x w z =
      1 + ∑ j : Fin 3, localMellinTerm primeScale (actualUnramifiedCoefficients η u x z) w P j := by
  by_cases hram : P.val ∣ Ideal.span {u.val}
  · simp only [unramifiedFactor, localMellinTerm, actualUnramifiedCoefficients,
      hram, ite_true, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  · simp only [unramifiedFactor, localMellinTerm, actualUnramifiedCoefficients,
      hram, ite_false]
    have hQ : (4 : ℝ) ≤ P.val.absNorm := by exact_mod_cast hP
    obtain ⟨hR,hV,hD⟩ := unramified_denominators P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z hQ (actualAPhase_norm_le_one η _)
      (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) hx hz
    have he := unramified_defect_expansion P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x w z (by linarith) hR hV hD
    rw [quadratic_vector_eval]
    change idealUnramifiedCorrection η u P x w z = _
    dsimp only [idealUnramifiedCorrection]
    change _ = 1 + (unramifiedDefectCoefficients _ _ _ _ _ _).eval _
    simpa only [primeScale, NNReal.coe_natCast, Complex.ofReal_natCast] using
      (eq_add_of_sub_eq he).trans (add_comm _ _)

theorem actual_unramified_local_mass (eps : ℝ) (η : Character) (u : FreeRow) (x w z : ℂ)
    (P : PrimeIdeal) (hP : 4 ≤ P.val.absNorm) (heps : 0 < eps)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    localMass (localMellinTerm primeScale (actualUnramifiedCoefficients η u x z) w) P ≤
      3 * firstPrimeDefectBound eps P := by
  unfold localMass localMellinTerm actualUnramifiedCoefficients
  split_ifs
  · simp only [Pi.zero_apply, zero_mul, norm_zero, Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (firstPrimeDefectBound_nonneg eps P)
  · have hQ : (4 : ℝ) ≤ P.val.absNorm := by exact_mod_cast hP
    rw [quadratic_vector_mass _ _ _ (by change (0 : ℝ) < P.val.absNorm; linarith)]
    have hh := unramified_defect_coefficient_mass P.val.absNorm w.re eps
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z hQ (actualAPhase_norm_le_one η _)
      (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) heps hx hz hw hxw
    simpa only [primeScale, NNReal.coe_natCast, firstPrimeDefectBound,
      show (720 : ℝ) = 3 * 240 by norm_num, mul_assoc] using hh

theorem actual_unramified_local_mass_summable (eps : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    Summable (localMass (localMellinTerm
      (fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val)
      (fun P => actualUnramifiedCoefficients η u x z P.val) w)) := by
  apply (hS.summable.mul_left 3).of_nonneg_of_le
  · intro P
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · intro P
    exact actual_unramified_local_mass eps η u x w z P.val
      (hS.norm_four P.val P.property) hS.positive hx hz hw hxw

theorem actual_unramified_expansion (eps : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    unramifiedProduct S η u x w z =
      ∑' e : EulerIndex {P : PrimeIdeal // P.val ∉ S} 3,
        eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e *
          (eulerScale (fun P => primeScale P.val) e : ℂ) ^ (-w) := by
  have hs := actual_unramified_local_mass_summable eps S hS η u x w z hx hz hw hxw
  have he := euler_expansion_eq_tprod _ hs
  simp only [eulerTerm_mellin] at he
  rw [← he]
  apply tprod_congr
  intro P
  exact actual_unramified_local_expansion η u x w z P.val
    (hS.norm_four P.val P.property) hx hz

theorem primeScale_one_le (P : PrimeIdeal) : 1 ≤ primeScale P := by
  have hn : 0 < P.val.absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  change (1 : ℝ≥0) ≤ (P.val.absNorm : ℝ≥0)
  exact_mod_cast (Nat.succ_le_of_lt hn)

theorem actual_unramified_coefficient_mass (eps sigma : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hsigma : -(1 / 100 : ℝ) ≤ sigma) (hxw : 1 + eps ≤ x.re + sigma) :
    let Q := fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val
    let c := fun P : {P : PrimeIdeal // P.val ∉ S} => actualUnramifiedCoefficients η u x z P.val
    Summable (fun e : EulerIndex {P : PrimeIdeal // P.val ∉ S} 3 =>
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) ∧
    (∑' e : EulerIndex {P : PrimeIdeal // P.val ∉ S} 3,
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) ≤ Real.exp (1 / 2) := by
  dsimp only
  let Q := fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val
  let c := fun P : {P : PrimeIdeal // P.val ∉ S} => actualUnramifiedCoefficients η u x z P.val
  let f := localMellinTerm Q c (sigma : ℂ)
  have hf := actual_unramified_local_mass_summable eps S hS η u x (sigma : ℂ) z
    hx hz hsigma hxw
  have hQ : ∀ P, 1 ≤ Q P := fun P => primeScale_one_le P.val
  refine ⟨euler_coefficients_summable_weight Q hQ c sigma hf, ?_⟩
  have hb := euler_expansion_mass_le_exp f hf
  dsimp only [f] at hb
  simp only [euler_coefficient_weight_eq Q hQ c sigma] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hm : (∑' P, localMass f P) ≤
      ∑' P : {P : PrimeIdeal // P.val ∉ S}, 3 * firstPrimeDefectBound eps P.val := by
    apply hf.tsum_le_tsum _ (hS.summable.mul_left 3)
    intro P
    exact actual_unramified_local_mass eps η u x (sigma : ℂ) z P.val
      (hS.norm_four P.val P.property) hS.positive hx hz hsigma hxw
  rw [tsum_mul_left] at hm
  linarith [hS.small]

end WeightedQRH.Numerator
