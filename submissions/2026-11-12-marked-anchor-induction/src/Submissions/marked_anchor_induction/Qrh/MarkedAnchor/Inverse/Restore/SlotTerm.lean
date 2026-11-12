/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Coeff
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Dict

/-!
# Inverse.Restore.SlotTerm — the restored child slot term on a canonical pool prime

For a canonical pool prime `P` (pool index of `primePool (childF q D)`, `p = poolPrimary`) coprime
to the child ray modulus, with the imageAdm coefficient
`a = conj(β(P)/δ(P)) · logPhase (-t) (log (N P / X))`, `β = rayCoeff … X v`:

**`slot_term_pos`**: `idealRowHom y P · normalizedPrimeCoeff L' β' X P =
  conj(logPhase τ (log X)) · (a · (childWeight ψ 1 y P · logPhase τ (log (N P))))`
with the canonical child coefficient `β' = rayCoeff R' G' _ (childBump W) σ data' θ' X (-v-2πt+2πτ)`.
This is exactly the hypothesis `hw` of `Dict.injSlots_eq_tuple` for the weights of
`TupleSum.twSlots_eq_tuple` (with `κ = conj(logPhase τ (log X))`, unimodular).
**`slot_term_neg`**: the same for the conjugated coefficients `conj a` (negative orientation,
`childBumpN`, `θ' = θ·conj δ·η'`, height `v + 2πt + 2πτ`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.ConcreteTraceCRT (eisEmbedding)
open OAI.SevenEighths.HeckeFamily (Character idealCoeff)
open OAI.ConcretePrimeRowBridge (primePool)
open OAI.CanonicalQuadraticSieve (poolPrimary)
open Qrh.MarkedAnchor.Inverse.Poisson
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => ActualEisensteinCubic.O

section
variable (q D : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
  (hψ : CanonicalCoefficientClass.FactorsModulo
    (CanonicalCoefficientClass.fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)
  (hg : ∀ i : primePool (childF q D), lambda ∉ Ideal.span {poolPrimary (childF q D) i})
  [∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal]

theorem primeN_pool (P : primePool (childF q D)) :
    primeN (poolPrimary (childF q D)) P = (P.val.absNorm : ℝ) := by
  rw [primeN_eq_absNorm, CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) P]

/-- The child weight on a canonical pool prime, in ideal terms. -/
theorem childWeight_pool (y : O) (P : primePool (childF q D)) :
    childWeight (poolPrimary (childF q D)) hg ψ 1 y P =
      -(ψ (CompletedGauss.primaryPrime P.val) * CanonicalRowCompletion.idealRowHom y P.val *
        (((Real.sqrt (P.val.absNorm : ℝ))⁻¹ : ℝ) : ℂ)) := by
  have hspan := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) P
  have hpp : CompletedGauss.primaryPrime P.val = poolPrimary (childF q D) P := rfl
  have hrow : finiteSquarefreeRow (fun i => Ideal.span {poolPrimary (childF q D) i}) hg {P} y =
      CanonicalRowCompletion.idealRowHom y P.val := by
    rw [← hspan, CanonicalRowCompletion.idealRowHom_prime _ _ (hg P)]
    unfold finiteSquarefreeRow
    rw [Finset.prod_singleton]
  have hnorm : ‖eisEmbedding (poolPrimary (childF q D) P)‖ = Real.sqrt (P.val.absNorm : ℝ) := by
    have h := primeN_pool q D P
    unfold primeN at h
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  unfold childWeight
  rw [rowCoprimeMask_one, mul_one, hrow, hnorm, hpp]

theorem pool_facts (P : primePool (childF q D)) :
    P.val.IsMaximal ∧ P.val ≠ ⊥ ∧ 0 < (P.val.absNorm : ℝ) := by
  have hmax : P.val.IsMaximal := ConcretePrimeRowBridge.primePool_maximal _
    (fun I hI => (childF_admissible q D I hI).1) P
  have hb : P.val ≠ ⊥ := by
    have hspan := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) P
    rw [← hspan, Ne, Ideal.span_singleton_eq_bot]
    exact CanonicalQuadraticSieve.poolPrimary_ne_zero _ (childF_admissible q D) P
  refine ⟨hmax, hb, ?_⟩
  have : Ideal.absNorm P.val ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact fun h => hb (h.trans Ideal.zero_eq_bot)
  exact_mod_cast Nat.pos_of_ne_zero this

theorem logPhase_unit (s y : ℝ) :
    star (FourierBridge.logPhase s y) * FourierBridge.logPhase s y = 1 := by
  rw [logPhase_star]
  unfold FourierBridge.logPhase
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 2
  push_cast; ring

theorem sqrt_div_cast (X N : ℝ) (hX : 0 < X) (hN : 0 < N) :
    ((Real.sqrt X : ℂ))⁻¹ * ((Real.sqrt (X / N) : ℝ) : ℂ) = (((Real.sqrt N)⁻¹ : ℝ) : ℂ) := by
  rw [Real.sqrt_div hX.le]
  have h1 : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
  have h2 : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hN).ne'
  push_cast
  field_simp

variable (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
  (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (σ : ℝ)
  (data : HeckeInverseAmplification.RowData) (θ : RayQuotient.Characters rayM G.twist)

/-- **The restored child slot term, positive orientation.** -/
theorem slot_term_pos (y : O) (t τ X v : ℝ) (hX : 0 < X) (L' : Finset (Ideal O))
    (P : primePool (childF q D)) (hPL : P.val ∈ L')
    (hcop : IsCoprime P.val (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
      (childCharacter q hq ψ hψ))) :
    CanonicalRowCompletion.idealRowHom y P.val *
      Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff L'
        (rayCoeff (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ))
          (childSlotTwist rayM G hH (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ)) (childSlotTwist_hH rayM G hH _ _) (childBump W) σ
          (childData q hq ψ hψ)
          (childTheta rayM false G hH θ (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ)) X (-v - 2 * Real.pi * t + 2 * Real.pi * τ)) X P.val =
    star (FourierBridge.logPhase τ (Real.log X)) *
      ((star (rayCoeff rayM G hH W σ data θ X v P.val /
          idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P.val) *
          FourierBridge.logPhase (-t) (Real.log ((P.val.absNorm : ℝ) / X))) *
        (childWeight (poolPrimary (childF q D)) hg ψ 1 y P *
          FourierBridge.logPhase τ (Real.log (primeN (poolPrimary (childF q D)) P)))) := by
  obtain ⟨hmax, hb, hN⟩ := pool_facts q D P
  have h := child_coeff_pos rayM G hH W σ data θ q hq ψ hψ v t τ X hX P.val hb hN hcop
  set β' := rayCoeff (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ))
          (childSlotTwist rayM G hH (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ)) (childSlotTwist_hH rayM G hH _ _) (childBump W) σ
          (childData q hq ψ hψ)
          (childTheta rayM false G hH θ (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ)) X (-v - 2 * Real.pi * t + 2 * Real.pi * τ) with hβ'
  set lp := FourierBridge.logPhase τ (Real.log X)
  have hu := logPhase_unit τ (Real.log X)
  unfold Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
  rw [if_pos hPL, childWeight_pool q D ψ hg y P, primeN_pool q D P]
  have hs := sqrt_div_cast X (P.val.absNorm : ℝ) hX hN
  linear_combination -(CanonicalRowCompletion.idealRowHom y P.val * ((Real.sqrt X : ℂ))⁻¹ *
      star lp) * h - (CanonicalRowCompletion.idealRowHom y P.val * β' P.val *
      ((Real.sqrt X : ℂ))⁻¹) * hu -
    (star lp * star (rayCoeff rayM G hH W σ data θ X v P.val /
          idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P.val) *
        FourierBridge.logPhase (-t) (Real.log ((P.val.absNorm : ℝ) / X)) *
        ψ (CompletedGauss.primaryPrime P.val) *
        FourierBridge.logPhase τ (Real.log (P.val.absNorm : ℝ)) *
        CanonicalRowCompletion.idealRowHom y P.val) * hs

/-- **The restored child slot term, negative orientation** (coefficients `conj a`). -/
theorem slot_term_neg (y : O) (t τ X v : ℝ) (hX : 0 < X) (L' : Finset (Ideal O))
    (P : primePool (childF q D)) (hPL : P.val ∈ L')
    (hcop : IsCoprime P.val (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
      (childCharacter q hq ψ hψ))) :
    CanonicalRowCompletion.idealRowHom y P.val *
      Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff L'
        (rayCoeff (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ))
          (childSlotTwist rayM G hH (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ)) (childSlotTwist_hH rayM G hH _ _) (childBumpN W) σ
          (childData q hq ψ hψ)
          (childTheta rayM true G hH θ (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ)) X (v + 2 * Real.pi * t + 2 * Real.pi * τ)) X P.val =
    star (FourierBridge.logPhase τ (Real.log X)) *
      (star (star (rayCoeff rayM G hH W σ data θ X v P.val /
          idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P.val) *
          FourierBridge.logPhase (-t) (Real.log ((P.val.absNorm : ℝ) / X))) *
        (childWeight (poolPrimary (childF q D)) hg ψ 1 y P *
          FourierBridge.logPhase τ (Real.log (primeN (poolPrimary (childF q D)) P)))) := by
  obtain ⟨hmax, hb, hN⟩ := pool_facts q D P
  have h := child_coeff_neg rayM G hH W σ data θ q hq ψ hψ v t τ X hX P.val hb hN hcop
  set β' := rayCoeff (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ))
          (childSlotTwist rayM G hH (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ)) (childSlotTwist_hH rayM G hH _ _) (childBumpN W) σ
          (childData q hq ψ hψ)
          (childTheta rayM true G hH θ (DetectorDictionaryInverseRawInitialGates.deletedBase data)
            (childCharacter q hq ψ hψ)) X (v + 2 * Real.pi * t + 2 * Real.pi * τ) with hβ'
  set lp := FourierBridge.logPhase τ (Real.log X)
  have hu := logPhase_unit τ (Real.log X)
  unfold Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
  rw [if_pos hPL, childWeight_pool q D ψ hg y P, primeN_pool q D P]
  have hs := sqrt_div_cast X (P.val.absNorm : ℝ) hX hN
  linear_combination -(CanonicalRowCompletion.idealRowHom y P.val * ((Real.sqrt X : ℂ))⁻¹ *
      star lp) * h - (CanonicalRowCompletion.idealRowHom y P.val * β' P.val *
      ((Real.sqrt X : ℂ))⁻¹) * hu -
    (star lp * star (star (rayCoeff rayM G hH W σ data θ X v P.val /
          idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P.val) *
        FourierBridge.logPhase (-t) (Real.log ((P.val.absNorm : ℝ) / X))) *
        ψ (CompletedGauss.primaryPrime P.val) *
        FourierBridge.logPhase τ (Real.log (P.val.absNorm : ℝ)) *
        CanonicalRowCompletion.idealRowHom y P.val) * hs

end

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.slot_term_pos
#print axioms Qrh.MarkedAnchor.Inverse.Restore.slot_term_neg
