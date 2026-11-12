/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.ChildCol
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Twist
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Bump
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Interface.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Conjugation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime

/-!
# Inverse.Restore.Coeff — the restored child slot coefficient is canonical

On a slot prime `P` (coprime to the child ray modulus `R' = rayM · mod δ · mod η'`) the restored
child slot weight

`-(a(P) · ψ(π_P) · logPhase τ (log N P)) · √(D / N P)`,  `a(P) = conj(β(P)/δ(P)) · logPhase (-t) (log (N P/D))`

(`β = rayCoeff … W σ data θ D v`, `δ = deletedBase data`) equals the unimodular constant
`logPhase τ (log D)` times the canonical coefficient

`rayCoeff R' G' le_rfl (childBump W) σ data' θ' D (-v - 2πt + 2πτ) P`

of the child class `canonicalSlotsRay (childBump W) σ R' G' le_rfl` (**`child_coeff_pos`**), with
`G' = childSlotTwist` (pool = preimage of `G.pool`, twist = global units) and ONE child twist
`θ' = oTwist false … = conj θ · δ · η'`, common to all slots. The negative orientation (row symbol
conjugated, coefficients `conj a`) is **`child_coeff_neg`** with `childBumpN W = -W · x^{-1/2}`,
`θ' = θ · conj δ · η'`, height `v + 2πt + 2πτ`.

Pool equality: `mem_canonicalPool_child` (child canonical pool = parent canonical pool ∩ primes
coprime to `R'`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical ContDiff
open OAI OAI.SevenEighths HeckeFamily
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => HeckeFamily.O
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ## Characters at primes -/

theorem inv_coeff_mul (χ : Character) (P : Ideal O) (h : idealCoeff χ P ≠ 0) :
    idealCoeff χ.inverse P * idealCoeff χ P = 1 := by
  rw [HeckeDetectorRelativePrime.idealCoeff_inverse, inv_mul_cancel₀ h]

theorem star_coeff_eq_inv (χ : Character) (P : Ideal O) :
    star (idealCoeff χ P) = (idealCoeff χ P)⁻¹ := by
  rw [← HeckeDetectorRelativePrime.idealCoeff_inverse, idealCoeff_inverse_conj, starRingEnd_apply]

theorem coprime_of_le {P A B : Ideal O} (h : IsCoprime P A) (hAB : A ≤ B) : IsCoprime P B := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  rw [eq_top_iff, ← h]
  exact sup_le_sup_left hAB P

/-- On primes where the row base does not vanish, the canonical coefficient is the ray character
times the annular weight. -/
theorem rayCoeff_of_ne (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (σ : ℝ)
    (data : HeckeInverseAmplification.RowData) (θ : RayQuotient.Characters rayM G.twist)
    (D v : ℝ) (P : Ideal O) (hη : idealCoeff data.η P ≠ 0) :
    rayCoeff rayM G hH W σ data θ D v P =
      idealCoeff (HeckeRayQuotient.character rayM G.twist hH θ) P *
        HeckePrimeAnnular.annularWeight W D σ v P := by
  unfold rayCoeff
  rw [CenteredMomentNaturalFixedRaySource.relativeCharacter_ideal,
    mul_assoc (idealCoeff (HeckeRayQuotient.character rayM G.twist hH θ) P),
    inv_coeff_mul _ _ hη, mul_one]

/-- A nonzero deleted base forces a nonzero row base. -/
theorem eta_ne_zero_of_deleted (data : HeckeInverseAmplification.RowData) (P : Ideal O)
    (h : idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P ≠ 0) :
    idealCoeff data.η P ≠ 0 := by
  have key : ∀ (χ : Character) (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P),
      idealCoeff (χ.excludePrimes S hS) P ≠ 0 → idealCoeff χ P ≠ 0 := by
    intro χ S hS h
    rw [HeckeFamily.idealCoeff_excludePrimes] at h
    split_ifs at h with hc
    · exact h
    · exact absurd rfl h
  have h2 : idealCoeff (InverseInitialDetectorSource.baseCharacter data) P ≠ 0 := key _ _ _ h
  rw [InverseInitialDetectorSource.baseCharacter_coeff] at h2
  intro h0
  apply h2
  change idealCoeff data.η P * _ = 0
  rw [h0, zero_mul]

/-! ## The oriented child twist -/

section Twist
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
local instance (χ : Character) : Finite (O ⧸ χ.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot

/-- The oriented child twist: `conj θ · δ · η'` (`neg = false`) or `θ · conj δ · η'`
(`neg = true`), as a residue character modulo `childRay`. -/
def oTwistChar (neg : Bool) (H : Subgroup (O ⧸ rayM)ˣ) (θ : RayQuotient.Characters rayM H)
    (δ η' : Character) : MulChar (O ⧸ childRay rayM δ η') ℂ :=
  pullChar (childRay_le_ray rayM δ η')
      (if neg then (θ : MulChar (O ⧸ rayM) ℂ) else star (θ : MulChar (O ⧸ rayM) ℂ)) *
    pullChar (childRay_le_delta rayM δ η') (if neg then star δ.residue else δ.residue) *
    pullChar (childRay_le_eta rayM δ η') η'.residue

theorem oTwistChar_mk (neg : Bool) (H : Subgroup (O ⧸ rayM)ˣ) (θ : RayQuotient.Characters rayM H)
    (δ η' : Character) (z : O) (hz : IsUnit (Ideal.Quotient.mk (childRay rayM δ η') z)) :
    oTwistChar rayM neg H θ δ η' (Ideal.Quotient.mk _ z) =
      (if neg then (θ : MulChar (O ⧸ rayM) ℂ) (Ideal.Quotient.mk rayM z)
        else star ((θ : MulChar (O ⧸ rayM) ℂ) (Ideal.Quotient.mk rayM z))) *
      (if neg then star (δ.residue (Ideal.Quotient.mk δ.modulus z))
        else δ.residue (Ideal.Quotient.mk δ.modulus z)) *
      η'.residue (Ideal.Quotient.mk η'.modulus z) := by
  unfold oTwistChar
  rw [MulChar.mul_apply, MulChar.mul_apply, pullChar_mk _ _ _ hz, pullChar_mk _ _ _ hz,
    pullChar_mk _ _ _ hz]
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, MulChar.star_apply]

theorem oTwistChar_mem (neg : Bool) (H : Subgroup (O ⧸ rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (θ : RayQuotient.Characters rayM H)
    (δ η' : Character) :
    oTwistChar rayM neg H θ δ η' ∈
      RayOrthogonality.characters (RayOrthogonality.globalUnits (childRay rayM δ η')) := by
  rw [RayOrthogonality.mem_characters_iff]
  rintro u ⟨ε, rfl⟩
  have hunit : IsUnit (Ideal.Quotient.mk (childRay rayM δ η') (ε : O)) :=
    (Units.map (Ideal.Quotient.mk (childRay rayM δ η')).toMonoidHom ε).isUnit
  change oTwistChar rayM neg H θ δ η' (Ideal.Quotient.mk _ (ε : O)) = 1
  rw [oTwistChar_mk rayM neg H θ δ η' _ hunit, δ.unit_trivial ε, η'.unit_trivial ε]
  have hθ : (θ : MulChar (O ⧸ rayM) ℂ) (Ideal.Quotient.mk rayM (ε : O)) = 1 :=
    (RayOrthogonality.mem_characters_iff H _).mp θ.property _ (hH ⟨ε, rfl⟩)
  rw [hθ]
  cases neg <;> simp

/-- The oriented common child twist `θ'`. -/
def oTwist (neg : Bool) (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (θ : RayQuotient.Characters rayM H) (δ η' : Character) :
    RayQuotient.Characters (childRay rayM δ η')
      (RayOrthogonality.globalUnits (childRay rayM δ η')) :=
  ⟨oTwistChar rayM neg H θ δ η', oTwistChar_mem rayM neg H hH θ δ η'⟩

theorem oTwist_span (neg : Bool) (H : Subgroup (O ⧸ rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (θ : RayQuotient.Characters rayM H)
    (δ η' : Character) (g : O) (hg : g ≠ 0)
    (hunit : IsUnit (Ideal.Quotient.mk (childRay rayM δ η') g)) :
    idealCoeff (HeckeRayQuotient.character (childRay rayM δ η')
        (RayOrthogonality.globalUnits (childRay rayM δ η')) le_rfl
        (oTwist rayM neg H hH θ δ η')) (Ideal.span {g}) =
      (if neg then idealCoeff (HeckeRayQuotient.character rayM H hH θ) (Ideal.span {g})
        else star (idealCoeff (HeckeRayQuotient.character rayM H hH θ) (Ideal.span {g}))) *
      (if neg then star (idealCoeff δ (Ideal.span {g})) else idealCoeff δ (Ideal.span {g})) *
      idealCoeff η' (Ideal.span {g}) := by
  rw [HeckeRayQuotient.idealCoeff_character, HeckeRayQuotient.idealCoeff_character,
    idealCoeff_span δ hg, idealCoeff_span η' hg]
  unfold RayQuotient.idealCharacter
  rw [IdealCharacter.ofResidue_span _ _ _ hg, IdealCharacter.ofResidue_span _ _ _ hg]
  exact oTwistChar_mk rayM neg H θ δ η' g hunit

/-! ## The child slot subgroups and the pool -/

/-- Child slot subgroups: pool = preimage of the parent pool, twist = global units. -/
def childSlotTwist (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)
    (δ η' : Character) : SlotTwist (childRay rayM δ η') where
  pool := G.pool.comap (Units.map (Ideal.Quotient.factor (childRay_le_ray rayM δ η')).toMonoidHom)
  twist := RayOrthogonality.globalUnits (childRay rayM δ η')
  twist_le := by
    rintro u ⟨ε, rfl⟩
    rw [Subgroup.mem_comap]
    apply G.twist_le
    apply hH
    refine ⟨ε, Units.ext ?_⟩
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact (Ideal.Quotient.factor_mk _ _).symm

theorem childSlotTwist_hH (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)
    (δ η' : Character) :
    RayOrthogonality.globalUnits (childRay rayM δ η') ≤ (childSlotTwist rayM G hH δ η').twist :=
  le_rfl

/-- The oriented child twist, typed for the child slot subgroups. -/
def childTheta (neg : Bool) (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)
    (θ : RayQuotient.Characters rayM G.twist) (δ η' : Character) :
    RayQuotient.Characters (childRay rayM δ η') (childSlotTwist rayM G hH δ η').twist :=
  oTwist rayM neg G.twist hH θ δ η'

theorem mem_identityClass_child (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (δ η' : Character) (P : Ideal O)
    (hP : P ≠ ⊥) :
    P ∈ RayQuotient.identityClass (childRay rayM δ η') (childSlotTwist rayM G hH δ η').pool ↔
      P ∈ RayQuotient.identityClass rayM G.pool ∧ IsCoprime P (childRay rayM δ η') := by
  constructor
  · rintro ⟨_, a, ha, u, hua, huH⟩
    refine ⟨⟨hP, a, ha, Units.map (Ideal.Quotient.factor (childRay_le_ray rayM δ η')).toMonoidHom u,
      ?_, huH⟩, ?_⟩
    · rw [Units.coe_map]
      change Ideal.Quotient.factor (childRay_le_ray rayM δ η') (u : O ⧸ childRay rayM δ η') = _
      rw [hua, Ideal.Quotient.factor_mk]
    · rw [← ha, ← IdealCharacter.isUnit_mk_iff_isCoprime, ← hua]
      exact u.isUnit
  · rintro ⟨⟨_, a, ha, u, hua, huH⟩, hc⟩
    have hunit : IsUnit (Ideal.Quotient.mk (childRay rayM δ η') a) := by
      rw [IdealCharacter.isUnit_mk_iff_isCoprime, ha]; exact hc
    obtain ⟨u', hu'⟩ := hunit
    refine ⟨hP, a, ha, u', hu', ?_⟩
    show Units.map (Ideal.Quotient.factor (childRay_le_ray rayM δ η')).toMonoidHom u' ∈ G.pool
    have : Units.map (Ideal.Quotient.factor (childRay_le_ray rayM δ η')).toMonoidHom u' = u := by
      apply Units.ext
      rw [Units.coe_map, hua]
      change Ideal.Quotient.factor (childRay_le_ray rayM δ η') (u' : O ⧸ childRay rayM δ η') = _
      rw [hu', Ideal.Quotient.factor_mk]
    rw [this]; exact huH

/-- **Pool equality**: the child canonical pool is the parent canonical pool restricted to the
primes coprime to the child ray modulus. -/
theorem mem_canonicalPool_child (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (δ η' : Character) (D : ℝ) (P : Ideal O) :
    P ∈ canonicalPool (childRay rayM δ η') (childSlotTwist rayM G hH δ η').pool D ↔
      P ∈ canonicalPool rayM G.pool D ∧ IsCoprime P (childRay rayM δ η') := by
  unfold canonicalPool CenteredMomentPrimeSlot.primePool
  simp only [Finset.mem_filter]
  have hb : ∀ {P : Ideal O}, Prime P → P ≠ ⊥ := fun hp h =>
    hp.ne_zero (h.trans Ideal.zero_eq_bot.symm)
  constructor
  · rintro ⟨⟨hA, hp, hc⟩, hr⟩
    have h := (mem_identityClass_child rayM G hH δ η' P (hb hp)).mp hc
    exact ⟨⟨⟨hA, hp, h.1⟩, hr⟩, h.2⟩
  · rintro ⟨⟨⟨hA, hp, hc⟩, hr⟩, hcop⟩
    exact ⟨⟨hA, hp, (mem_identityClass_child rayM G hH δ η' P (hb hp)).mpr ⟨hc, hcop⟩⟩, hr⟩

end Twist

/-! ## Powers -/

theorem cpow_ofReal_exp (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]

theorem logPhase_log_exp (s x : ℝ) :
    FourierBridge.logPhase s (Real.log x) =
      Complex.exp ((Real.log x : ℂ) * (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) := by
  unfold FourierBridge.logPhase
  congr 1
  push_cast
  ring

theorem sqrt_one_div_exp (x : ℝ) (hx : 0 < x) :
    ((Real.sqrt (1 / x) : ℝ) : ℂ) = Complex.exp ((Real.log x : ℂ) * (-(1/2 : ℂ))) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity), one_div, Real.log_inv,
    Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem star_exp (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  rw [Complex.star_def, ← Complex.exp_conj]

/-- The phase identity of the positive orientation. -/
theorem slot_phase_pos (x : ℝ) (hx : 0 < x) (σ v t τ : ℝ) :
    star ((x : ℂ) ^ (-HeckeDyadic.shift σ v)) * FourierBridge.logPhase (-t) (Real.log x) *
      FourierBridge.logPhase τ (Real.log x) * ((Real.sqrt (1 / x) : ℝ) : ℂ) =
    (x : ℂ) ^ (-(1/2 : ℂ)) *
      (x : ℂ) ^ (-HeckeDyadic.shift σ (-v - 2 * Real.pi * t + 2 * Real.pi * τ)) := by
  rw [cpow_ofReal_exp x hx, cpow_ofReal_exp x hx, cpow_ofReal_exp x hx, star_exp,
    logPhase_log_exp, logPhase_log_exp, sqrt_one_div_exp x hx, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Complex.star_def, map_mul, Complex.conj_ofReal]
  unfold HeckeDyadic.shift
  simp only [map_neg, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The phase identity of the negative orientation. -/
theorem slot_phase_neg (x : ℝ) (hx : 0 < x) (σ v t τ : ℝ) :
    (x : ℂ) ^ (-HeckeDyadic.shift σ v) * FourierBridge.logPhase t (Real.log x) *
      FourierBridge.logPhase τ (Real.log x) * ((Real.sqrt (1 / x) : ℝ) : ℂ) =
    (x : ℂ) ^ (-(1/2 : ℂ)) *
      (x : ℂ) ^ (-HeckeDyadic.shift σ (v + 2 * Real.pi * t + 2 * Real.pi * τ)) := by
  rw [cpow_ofReal_exp x hx, cpow_ofReal_exp x hx, cpow_ofReal_exp x hx,
    logPhase_log_exp, logPhase_log_exp, sqrt_one_div_exp x hx, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold HeckeDyadic.shift
  push_cast
  ring

theorem logPhase_star (s y : ℝ) :
    star (FourierBridge.logPhase s y) = FourierBridge.logPhase (-s) y := by
  unfold FourierBridge.logPhase
  rw [star_exp]
  congr 1
  rw [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The negative child bump `W' x = -W x · x^{-1/2}`. -/
def childBumpN (W : ℝ → ℂ) : ℝ → ℂ := fun x => -(W x) * ((x : ℂ) ^ (-(1/2 : ℂ)))

theorem childBumpN_contDiff (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) : ContDiff ℝ ∞ (childBumpN W) := by
  have hcs : Function.support (fun x => -(W x)) ⊆ Set.Icc a b := by
    intro x hx
    apply hs
    intro h0
    apply hx
    simp [h0]
  exact contDiff_mul_cpow _ hW.neg a b ha hcs _

theorem childBumpN_support (W : ℝ → ℂ) (a b : ℝ) (hs : Function.support W ⊆ Set.Icc a b) :
    Function.support (childBumpN W) ⊆ Set.Icc a b := by
  intro x hx
  apply hs
  intro h0
  apply hx
  simp [childBumpN, h0]

/-! ## The coefficient identities -/

section Coeff
variable (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
  (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (σ : ℝ)
  (data : HeckeInverseAmplification.RowData) (θ : RayQuotient.Characters rayM G.twist)
  (q : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
  (hψ : CanonicalCoefficientClass.FactorsModulo
    (CanonicalCoefficientClass.fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)

/-- The common facts at a slot prime coprime to the child ray modulus. -/
theorem slot_prime_facts (P : Ideal O) [hPm : P.IsMaximal] (hP0 : P ≠ ⊥)
    (hcop : IsCoprime P (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
      (childCharacter q hq ψ hψ))) :
    idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P ≠ 0 ∧
    idealCoeff data.η P ≠ 0 ∧
    idealCoeff (childCharacter q hq ψ hψ) P = ψ (CompletedGauss.primaryPrime P) ∧
    idealCoeff (childCharacter q hq ψ hψ) P ≠ 0 := by
  set δ := DetectorDictionaryInverseRawInitialGates.deletedBase data
  set η' := childCharacter q hq ψ hψ
  have hP0' : P ≠ 0 := fun h => hP0 (h.trans Ideal.zero_eq_bot)
  have hδ : idealCoeff δ P ≠ 0 :=
    HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime δ P hP0'
      (coprime_of_le hcop (childRay_le_delta rayM δ η'))
  have hcη : IsCoprime P η'.modulus := coprime_of_le hcop (childRay_le_eta rayM δ η')
  refine ⟨hδ, eta_ne_zero_of_deleted data P hδ, childCharacter_prime q hq ψ hψ P hcη,
    HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime η' P hP0' hcη⟩

/-- The child twist on a slot prime (via its generator). -/
theorem child_twist_prime (neg : Bool) (P : Ideal O) (hP0 : P ≠ ⊥)
    (hcop : IsCoprime P (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
      (childCharacter q hq ψ hψ))) :
    idealCoeff (HeckeRayQuotient.character
        (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ))
        (childSlotTwist rayM G hH (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ)).twist
        (childSlotTwist_hH rayM G hH _ _)
        (childTheta rayM neg G hH θ (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ))) P =
      (if neg then idealCoeff (HeckeRayQuotient.character rayM G.twist hH θ) P
        else star (idealCoeff (HeckeRayQuotient.character rayM G.twist hH θ) P)) *
      (if neg then star (idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P)
        else idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P) *
      idealCoeff (childCharacter q hq ψ hψ) P := by
  set g := Submodule.IsPrincipal.generator P with hgdef
  have hPg : Ideal.span {g} = P := Ideal.span_singleton_generator P
  have hg0 : g ≠ 0 := by
    intro h; apply hP0; rw [← hPg, h, Ideal.span_singleton_eq_bot]
  have hunit : IsUnit (Ideal.Quotient.mk (childRay rayM
      (DetectorDictionaryInverseRawInitialGates.deletedBase data) (childCharacter q hq ψ hψ)) g) := by
    rw [IdealCharacter.isUnit_mk_iff_isCoprime, hPg]; exact hcop
  have h := oTwist_span rayM neg G.twist hH θ
    (DetectorDictionaryInverseRawInitialGates.deletedBase data) (childCharacter q hq ψ hψ) g hg0 hunit
  rw [hPg] at h
  exact h

/-- **The restored child coefficient, positive orientation.** -/
theorem child_coeff_pos (v t τ D : ℝ) (hD : 0 < D) (P : Ideal O) [P.IsMaximal] (hP0 : P ≠ ⊥)
    (hN : 0 < (P.absNorm : ℝ))
    (hcop : IsCoprime P (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
      (childCharacter q hq ψ hψ))) :
    -(star (rayCoeff rayM G hH W σ data θ D v P /
        idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P) *
        FourierBridge.logPhase (-t) (Real.log ((P.absNorm : ℝ) / D)) *
        ψ (CompletedGauss.primaryPrime P) *
        FourierBridge.logPhase τ (Real.log (P.absNorm : ℝ))) *
      ((Real.sqrt (D / (P.absNorm : ℝ)) : ℝ) : ℂ) =
    FourierBridge.logPhase τ (Real.log D) *
      rayCoeff (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ))
        (childSlotTwist rayM G hH (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ)) (childSlotTwist_hH rayM G hH _ _) (childBump W) σ
        (childData q hq ψ hψ)
        (childTheta rayM false G hH θ (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ)) D (-v - 2 * Real.pi * t + 2 * Real.pi * τ) P := by
  obtain ⟨hδ, hη, hη'ψ, hη'⟩ := slot_prime_facts rayM data q hq ψ hψ P hP0 hcop
  have htw := child_twist_prime rayM G hH data θ q hq ψ hψ false P hP0 hcop
  simp only [Bool.false_eq_true, ↓reduceIte] at htw
  rw [rayCoeff_of_ne _ _ _ _ _ _ _ _ _ _ hη,
    rayCoeff_of_ne _ _ _ _ _ _ _ _ _ _ (show idealCoeff (childData q hq ψ hψ).η P ≠ 0 from hη'),
    htw, hη'ψ]
  unfold HeckePrimeAnnular.annularWeight childBump
  set N := (P.absNorm : ℝ)
  set x := N / D with hx
  have hx0 : 0 < x := div_pos hN hD
  have hlogN : Real.log N = Real.log x + Real.log D := by
    rw [hx, Real.log_div hN.ne' hD.ne']; ring
  have hsq : D / N = 1 / x := by rw [hx]; field_simp
  have hph := slot_phase_pos x hx0 σ v t τ
  set cθ := idealCoeff (HeckeRayQuotient.character rayM G.twist hH θ) P
  set cδ := idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P
  have hδinv : (star cδ)⁻¹ = cδ := by rw [star_coeff_eq_inv, inv_inv]
  rw [hlogN, FourierBridge.logPhase_add, hsq, star_div₀, star_mul', star_mul',
    div_eq_mul_inv _ (star cδ), hδinv]
  linear_combination (-(star cθ) * star (W x) * cδ * ψ (CompletedGauss.primaryPrime P) *
    FourierBridge.logPhase τ (Real.log D)) * hph

/-- **The restored child coefficient, negative orientation** (coefficients `conj a`). -/
theorem child_coeff_neg (v t τ D : ℝ) (hD : 0 < D) (P : Ideal O) [P.IsMaximal] (hP0 : P ≠ ⊥)
    (hN : 0 < (P.absNorm : ℝ))
    (hcop : IsCoprime P (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
      (childCharacter q hq ψ hψ))) :
    -(star (star (rayCoeff rayM G hH W σ data θ D v P /
        idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P) *
        FourierBridge.logPhase (-t) (Real.log ((P.absNorm : ℝ) / D))) *
        ψ (CompletedGauss.primaryPrime P) *
        FourierBridge.logPhase τ (Real.log (P.absNorm : ℝ))) *
      ((Real.sqrt (D / (P.absNorm : ℝ)) : ℝ) : ℂ) =
    FourierBridge.logPhase τ (Real.log D) *
      rayCoeff (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ))
        (childSlotTwist rayM G hH (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ)) (childSlotTwist_hH rayM G hH _ _) (childBumpN W) σ
        (childData q hq ψ hψ)
        (childTheta rayM true G hH θ (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ)) D (v + 2 * Real.pi * t + 2 * Real.pi * τ) P := by
  obtain ⟨hδ, hη, hη'ψ, hη'⟩ := slot_prime_facts rayM data q hq ψ hψ P hP0 hcop
  have htw := child_twist_prime rayM G hH data θ q hq ψ hψ true P hP0 hcop
  simp only [↓reduceIte] at htw
  rw [rayCoeff_of_ne _ _ _ _ _ _ _ _ _ _ hη,
    rayCoeff_of_ne _ _ _ _ _ _ _ _ _ _ (show idealCoeff (childData q hq ψ hψ).η P ≠ 0 from hη'),
    htw, hη'ψ]
  unfold HeckePrimeAnnular.annularWeight childBumpN
  set N := (P.absNorm : ℝ)
  set x := N / D with hx
  have hx0 : 0 < x := div_pos hN hD
  have hlogN : Real.log N = Real.log x + Real.log D := by
    rw [hx, Real.log_div hN.ne' hD.ne']; ring
  have hsq : D / N = 1 / x := by rw [hx]; field_simp
  have hph := slot_phase_neg x hx0 σ v t τ
  set cθ := idealCoeff (HeckeRayQuotient.character rayM G.twist hH θ) P
  set cδ := idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P
  have hδinv : cδ⁻¹ = star cδ := by rw [star_coeff_eq_inv]
  rw [hlogN, FourierBridge.logPhase_add, hsq, star_mul', star_star, logPhase_star, neg_neg,
    div_eq_mul_inv _ cδ, hδinv]
  linear_combination (-cθ * W x * star cδ * ψ (CompletedGauss.primaryPrime P) *
    FourierBridge.logPhase τ (Real.log D)) * hph

end Coeff

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.mem_canonicalPool_child
#print axioms Qrh.MarkedAnchor.Inverse.Restore.child_coeff_pos
#print axioms Qrh.MarkedAnchor.Inverse.Restore.child_coeff_neg
