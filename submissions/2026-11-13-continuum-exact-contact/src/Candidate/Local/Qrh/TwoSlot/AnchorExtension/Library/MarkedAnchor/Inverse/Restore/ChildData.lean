/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Poly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.RowClosure
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ChineseRemainder.PrimaryCompletions
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.ActiveConductor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.MeanSquare.OutsideIdeals
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

/-!
# Inverse.Restore.ChildData — the child row datum of the restoration

The child column carries the twist `ψ` on the PRIMARY generators of the pool primes. We build a
Hecke character `η'` of modulus `(2592 q)` with `η'(P) = ψ(primaryPrime P)` on every prime
coprime to `2592 q`:

* `primaryTwist ψ x = ψ(primaryGenerator (x))` (`0` on `λ`-multiples) is a monoid hom, trivial on
  units, and periodic modulo `(2592 q)` (`primaryTwist_factors`, from `periodic_of_primary`: on
  primary `x` it is `ψ x`, and `ψ` factors modulo `(q)(4)(4)`);
* `childCharacter = rowCharacter (2592 q) (primaryTwist ψ)`; `childRowData η` the `RowData`
  `⟨η, 2λ, 1⟩`, `childData = childRowData (childCharacter …)`;
* **`childCharacter_prime`**: `idealCoeff η' P = ψ(primaryPrime P)` for every prime `P` coprime to
  `2592 q`; `childCharacter_zero`: `η'` vanishes on the primes containing `2592 q`;
* **`childData_prime`**: `idealCoeff ((childRowData η).character y) P = idealCoeff η P ·
  idealRowHom y P` for every prime `P` not containing `2` or `λ`; `childData_coeff_ne_zero`.

The full child column on the canonical pool is identified with the inverse polynomial of the
child datum in `ChildCol` (`col_eq_childPolynomial`); the finiteness of the child characters
(they depend on `ψ` only through `residueRow`) is in `Keys`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.ConcreteTraceCRT (eisEmbedding)
open OAI.SevenEighths.HeckeFamily (Character idealCoeff elementCoeff idealCoeff_span)
open OAI.SevenEighths.HeckeRowClosure (rowCharacter elementCoeff_rowCharacter periodic_of_primary
  idealCoeff_eq_row residueRow)
open OAI.SevenEighths.HeckeInverseAmplification (RowData NonzeroElement)
open OAI.CanonicalCoefficientClass (FactorsModulo fixedBaseConductor IsBaseRayTwist)
open OAI.CanonicalRowCompletion (reflectionConductor reflectionExcludedPrimes idealRowHom)
open OAI.SevenEighths.HeckeDyadic (polynomial)

local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-! ## The primary twist -/

/-- `ψ` read on the primary generator of `(x)`; `0` on multiples of `λ`. -/
def primaryTwist (ψ : O →* ℂ) : O →* ℂ where
  toFun x := if λ₀ ∣ x then 0 else ψ (CompletedGauss.primaryGenerator (Ideal.span {x}))
  map_one' := by
    rw [if_neg ConcretePrimeRowBridge.goodLambda_prime.not_dvd_one, Ideal.span_singleton_one,
      ← Ideal.one_eq_top, CompletedGauss.primaryGenerator_one, map_one]
  map_mul' x y := by
    by_cases hx : λ₀ ∣ x
    · rw [if_pos (dvd_mul_of_dvd_left hx y), if_pos hx, zero_mul]
    by_cases hy : λ₀ ∣ y
    · rw [if_pos (dvd_mul_of_dvd_right hy x), if_pos hy, mul_zero]
    rw [if_neg (fun h => (ConcretePrimeRowBridge.goodLambda_prime.dvd_or_dvd h).elim hx hy),
      if_neg hx, if_neg hy, ← Ideal.span_singleton_mul_span_singleton,
      CompletedGauss.primaryGenerator_mul, map_mul]

theorem primaryTwist_apply (ψ : O →* ℂ) (x : O) :
    primaryTwist ψ x =
      if λ₀ ∣ x then 0 else ψ (CompletedGauss.primaryGenerator (Ideal.span {x})) := rfl

theorem primaryTwist_unit (ψ : O →* ℂ) (u : Oˣ) : primaryTwist ψ (u : O) = 1 := by
  rw [primaryTwist_apply, if_neg (fun h => ConcretePrimeRowBridge.goodLambda_prime.not_isUnit
      (isUnit_of_dvd_unit h u.isUnit)),
    Ideal.span_singleton_eq_top.mpr u.isUnit, ← Ideal.one_eq_top,
    CompletedGauss.primaryGenerator_one, map_one]

theorem primaryTwist_unit_mul (ψ : O →* ℂ) (u : Oˣ) (x : O) :
    primaryTwist ψ ((u : O) * x) = primaryTwist ψ x := by
  rw [map_mul, primaryTwist_unit, one_mul]

theorem primaryTwist_primary (ψ : O →* ℂ) (x : O) (hx : λ₀ ^ 2 ∣ x - 1) :
    primaryTwist ψ x = ψ x := by
  have hnd : ¬ λ₀ ∣ x := by
    intro h
    have h1 : λ₀ ∣ x - 1 := (dvd_pow_self λ₀ (by decide : 2 ≠ 0)).trans hx
    exact ConcretePrimeRowBridge.goodLambda_prime.not_dvd_one (by
      have := dvd_sub h h1; simpa using this)
  rw [primaryTwist_apply, if_neg hnd]
  have hg := PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff x |>.mpr hnd
  have hspec := CompletedGauss.primaryGenerator_spec (Ideal.span {x}) hg
  have hassoc : Associated (CompletedGauss.primaryGenerator (Ideal.span {x})) x :=
    Ideal.span_singleton_eq_span_singleton.mp hspec.1
  rw [ActualEisensteinCubic.primary_associated_eq _ _ hassoc hspec.2 hx]

/-! ## The child modulus `(2592 q)` -/

/-- The child modulus `(2592 q) = (9)·((q)(4))·(72)`. -/
def childModulus (q : ℕ) : Ideal O := Ideal.span {reflectionConductor q}

theorem childModulus_ne_bot (q : ℕ) (hq : q ≠ 0) : childModulus q ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr (CanonicalRowCompletion.reflectionConductor_ne_zero q hq)

theorem childModulus_le_base (q : ℕ) :
    childModulus q ≤ fixedBaseConductor q * Ideal.span {(4 : O)} := by
  rw [childModulus, CanonicalRowCompletion.reflectionConductor_ideal]
  refine Ideal.mul_le_right.trans (Ideal.mul_mono_right ?_)
  rw [Ideal.span_singleton_le_span_singleton]
  exact ⟨18, by norm_num⟩

theorem childModulus_le_lambda (q : ℕ) : childModulus q ≤ Ideal.span {λ₀ ^ 2} := by
  rw [childModulus, CanonicalRowCompletion.reflectionConductor_ideal]
  refine Ideal.mul_le_left.trans ?_
  rw [Ideal.span_singleton_le_span_singleton]
  exact ActualEisensteinCubic.lambda_sq_dvd_three.trans ⟨3, by norm_num⟩

/-- The child ray twists factor modulo `(q)(4)(4)`. -/
theorem childRay_factors {q : ℕ} {base Ψ ψ : O →* ℂ}
    (hb : FactorsModulo (fixedBaseConductor q) base) (hΨ : IsBaseRayTwist base Ψ)
    (hψ : Poisson.IsChildRay Ψ ψ) :
    FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ := by
  have hΨf := hΨ.factorsModulo _ hb
  obtain ⟨χ, rfl⟩ := hψ
  intro x y hxy
  simp only [MonoidHom.mul_apply, SecondPassArithmetic.rayMonoid_apply]
  rw [hΨf x y hxy]
  congr 1
  exact RayFourExpansion.rayCharacter_eq_of_mod_four χ x y
    (Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy))

theorem primaryTwist_factors (q : ℕ) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ) :
    FactorsModulo (childModulus q) (primaryTwist ψ) :=
  periodic_of_primary (childModulus q) (childModulus_le_lambda q) (primaryTwist ψ) ψ
    (fun x y h => hψ x y (childModulus_le_base q h)) (primaryTwist_unit_mul ψ)
    (fun x hx => by rw [primaryTwist_apply, if_pos hx]) (primaryTwist_primary ψ)

/-! ## The child character and the child row datum -/

/-- The child Hecke character `η'` (modulus `(2592 q)`): `ψ` on primary generators. -/
def childCharacter (q : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ) : Character :=
  rowCharacter (childModulus q) (childModulus_ne_bot q hq) (primaryTwist ψ)
    (primaryTwist_factors q ψ hψ) (primaryTwist_unit ψ)

/-- A row datum with character `η` and the trivial row multiplier `m = 2λ`, `f = 1`. -/
def childRowData (η : Character) : RowData where
  η := η
  m := 2 * λ₀
  f := 1
  m_ne_zero := mul_ne_zero two_ne_zero ConcretePrimeRowBridge.goodLambda_prime.ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

/-- The child row datum of the restoration. -/
def childData (q : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ) : RowData :=
  childRowData (childCharacter q hq ψ hψ)

theorem coprime_span_of_not_mem (P : Ideal O) [hP : P.IsMaximal] {a : O} (ha : a ∉ P) :
    IsCoprime P (Ideal.span {a}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply hP.out.2
  refine lt_of_le_of_ne le_sup_left (fun h => ha ?_)
  rw [h]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)

/-- A prime coprime to the child modulus contains no divisor of `2592 q`. -/
theorem not_mem_of_coprime_childModulus {q : ℕ} (P : Ideal O) [hP : P.IsMaximal]
    (hcop : IsCoprime P (childModulus q)) {a : O} (ha : a ∣ reflectionConductor q) :
    a ∉ P := by
  intro haP
  have hc : reflectionConductor q ∈ P := Ideal.mem_of_dvd _ ha haP
  have hle : childModulus q ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hc
  rw [Ideal.isCoprime_iff_sup_eq, sup_eq_left.mpr hle] at hcop
  exact hP.ne_top hcop

theorem two_dvd_reflectionConductor (q : ℕ) : (2 : O) ∣ reflectionConductor q :=
  ⟨((1296 * q : ℕ) : O), by unfold reflectionConductor; push_cast; ring⟩

theorem lambda_dvd_reflectionConductor (q : ℕ) : λ₀ ∣ reflectionConductor q := by
  have h3 : λ₀ ∣ (3 : O) :=
    (dvd_pow_self λ₀ (by decide : 2 ≠ 0)).trans ActualEisensteinCubic.lambda_sq_dvd_three
  exact h3.trans ⟨((864 * q : ℕ) : O), by unfold reflectionConductor; push_cast; ring⟩

/-- **The child character on a prime coprime to `2592 q`.** -/
theorem childCharacter_prime (q : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)
    (P : Ideal O) [P.IsMaximal] (hcop : IsCoprime P (childModulus q)) :
    idealCoeff (childCharacter q hq ψ hψ) P = ψ (CompletedGauss.primaryPrime P) := by
  have hlam : λ₀ ∉ P := not_mem_of_coprime_childModulus P hcop (lambda_dvd_reflectionConductor q)
  have hπ : CompletedGauss.primaryPrime P ≠ 0 := CompletedGauss.primaryPrime_ne_zero P hlam
  have hspec := CompletedGauss.primaryPrime_spec P hπ
  have hgen : CompletedGauss.primaryGenerator (Ideal.span {CompletedGauss.primaryPrime P}) =
      CompletedGauss.primaryPrime P := by
    rw [hspec.2.2.1]
    exact (CanonicalQuadraticSieve.primaryPrime_eq_primaryGenerator P).symm
  have hnd : ¬ λ₀ ∣ CompletedGauss.primaryPrime P := by
    apply (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff _).mp
    rw [hgen]; exact hπ
  conv_lhs => rw [← hspec.2.2.1]
  rw [idealCoeff_span _ hπ]
  unfold childCharacter
  rw [elementCoeff_rowCharacter, if_pos, primaryTwist_apply, if_neg hnd, hgen]
  rw [SevenEighths.IdealCharacter.isUnit_mk_iff_isCoprime, hspec.2.2.1]
  exact hcop

/-- The child character vanishes on every ideal sharing a prime with `2592 q`. -/
theorem childCharacter_zero (q : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)
    (P : Ideal O) [hP : P.IsMaximal] (hle : childModulus q ≤ P) :
    idealCoeff (childCharacter q hq ψ hψ) P = 0 := by
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h] at hle
    exact childModulus_ne_bot q hq (le_bot_iff.mp hle)
  obtain ⟨g, hg⟩ := (Submodule.IsPrincipal.principal P : ∃ g, P = Submodule.span O {g})
  have hg0 : g ≠ 0 := by
    rintro rfl; apply hP0; rw [hg]; exact Ideal.span_singleton_eq_bot.mpr rfl
  have hgP : P = Ideal.span {g} := hg
  rw [hgP, idealCoeff_span _ hg0]
  unfold childCharacter
  rw [elementCoeff_rowCharacter, if_neg]
  rw [SevenEighths.IdealCharacter.isUnit_mk_iff_isCoprime, ← hgP, Ideal.isCoprime_iff_sup_eq,
    sup_eq_left.mpr hle]
  exact hP.ne_top

/-! ## The child row character -/

/-- **The child row character on a prime coprime to `2592 q`**: `ψ(π_P) · χ_P(y)`. -/
theorem childData_prime (η : Character) (u : NonzeroElement) (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) (hlam : λ₀ ∉ P) :
    idealCoeff ((childRowData η).character u) P = idealCoeff η P * idealRowHom u.val P := by
  rw [idealCoeff_eq_row η _ (childRowData η).m (childRowData η).f u.val
    ((childRowData η).character_spec u) P]
  change idealCoeff η P * idealRowHom ((2 * λ₀)^6 * 1^4 * u.val) P = _
  rw [one_pow, mul_one, CanonicalRowCompletion.idealRowHom_argument_mul,
    CanonicalRowCompletion.idealRowHom_prime_sixth_mask _ P hlam, if_pos, one_mul]
  apply coprime_span_of_not_mem
  intro hm
  rcases (Ideal.IsMaximal.isPrime inferInstance).mem_or_mem hm with h | h
  · exact h2 h
  · exact hlam h

/-- The child row character vanishes where the child character does. -/
theorem childData_coeff_ne_zero (η : Character) (u : NonzeroElement) (I : Ideal O)
    (h : idealCoeff ((childRowData η).character u) I ≠ 0) : idealCoeff η I ≠ 0 := by
  rw [idealCoeff_eq_row η _ (childRowData η).m (childRowData η).f u.val
    ((childRowData η).character_spec u) I] at h
  exact left_ne_zero_of_mul h

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.childCharacter_prime
#print axioms Qrh.MarkedAnchor.Inverse.Restore.childCharacter_zero
#print axioms Qrh.MarkedAnchor.Inverse.Restore.childData_prime
