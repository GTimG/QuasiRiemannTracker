/- Copyright (c) 2026 Sil. Apache-2.0.
The same fixed-exponent event pays original outer and small-sigma
exceptional conductors. No character norm is hidden in a constant.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedChildCaps
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshAssembly
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedPrincipalPoolCaps

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedConductorCaps
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge
open MixedPrincipalPair MixedPrincipalWindow MixedSupplierFourthRow MixedSupplierSource
open MixedOriginalTail MixedInnerExceptionalPair MixedInnerExceptionalLedger MixedPrincipalPoolCaps
open OuterFreshAssembly RepairedCapEvent
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem pool_norm_cap {κ : Type u} [Fintype κ] (r : Source κ (1/4) (9/4))
    (Z : ℝ) (hZ : 1 < Z) (hpool : poolCap r ≤ Z^(8:ℝ)) :
    MixedInnerExceptionalPair.poolNorm r ≤ Z^(16:ℝ) := by
  apply (pool_norm_le_square r (by norm_num)).trans
  apply (pow_le_pow_left₀ (poolCap_nonneg r) hpool 2).trans_eq
  rw [pow_two, ← Real.rpow_add (zero_lt_one.trans hZ)]
  norm_num

theorem linear_sigma_cap {N : ℕ} {ε Z : ℝ} (hevent : Event.{u} N ε Z)
    (τ σ : Character) (f : Id) (hτ : (τ.modulus.absNorm:ℝ) ≤ Z^(6:ℝ))
    (hf : (f.absNorm:ℝ) ≤ Z^(2:ℝ))
    (hσ : σ.modulus.absNorm ≤ τ.modulus.absNorm *
      (ReferenceCubicCharacter.conductorConstant*f.absNorm) * (Ideal.span {(12:O)}).absNorm) :
    (σ.modulus.absNorm:ℝ) ≤ Z^(9:ℝ) := by
  have hz := zero_lt_one.trans hevent.uniform.1
  have hσr : (σ.modulus.absNorm:ℝ) ≤ sigmaFixed*(τ.modulus.absNorm:ℝ)*(f.absNorm:ℝ) := by
    have hh : (σ.modulus.absNorm:ℝ) ≤ (τ.modulus.absNorm:ℝ) *
        ((ReferenceCubicCharacter.conductorConstant:ℝ)*(f.absNorm:ℝ)) * (Ideal.span {(12:O)}).absNorm := by
      exact_mod_cast hσ
    apply hh.trans_eq
    unfold sigmaFixed
    ring
  apply hσr.trans
  calc
    _ ≤ Z*Z^(6:ℝ)*Z^(2:ℝ) := by
      have hc := hevent.sigma
      have hfixed : 0 ≤ sigmaFixed := by unfold sigmaFixed; positivity
      gcongr
    _ = _ := by norm_num [Real.rpow_natCast,pow_succ]; ring

set_option maxHeartbeats 600000 in
theorem outer_family_cap {κ : Type u} [Fintype κ] {N : ℕ} {ε Z : ℝ}
    (hevent : Event.{u} N ε Z) (q : Data κ) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) (1/4) (9/4)) (τ : Character) (radius : ℝ)
    (hτ : (τ.modulus.absNorm:ℝ) ≤ Z^(6:ℝ)) (hR : (r.R.absNorm:ℝ) ≤ Z^(4:ℝ))
    (hf : ((frozenProduct q x).absNorm:ℝ) ≤ Z^(2:ℝ))
    (hd : ((selectedProduct q y).absNorm:ℝ) ≤ Z^(2:ℝ))
    (hpool : poolCap r ≤ Z^(8:ℝ)) (hr0 : 0 ≤ radius) (hrad : radius ≤ Z^(15:ℝ)) :
    outerFamilyConductorBudget q x y r τ radius ≤ Z^(64:ℝ) := by
  have hz := zero_lt_one.trans hevent.uniform.1
  have hpn := pool_norm_cap r Z hevent.uniform.1 hpool
  have hpc0 := poolCap_nonneg r
  have hpn0 : 0 ≤ MixedInnerExceptionalPair.poolNorm r := Finset.sum_nonneg (fun I _ => Nat.cast_nonneg _)
  have hfixed : 0 ≤ outerFixed := by unfold outerFixed; positivity
  calc
    _ = outerFixed*(τ.modulus.absNorm:ℝ)*(r.R.absNorm:ℝ)*
        ((frozenProduct q x).absNorm:ℝ)^2*((selectedProduct q y).absNorm:ℝ)^2*
        poolCap r*MixedInnerExceptionalPair.poolNorm r*radius := by
      unfold outerFamilyConductorBudget OuterFreshPhysical.fixedConductorCost outerFixed
      ring
    _ ≤ Z*Z^(6:ℝ)*Z^(4:ℝ)*(Z^(2:ℝ))^2*(Z^(2:ℝ))^2*Z^(8:ℝ)*Z^(16:ℝ)*Z^(15:ℝ) := by
      have hc := hevent.outer
      gcongr
    _ = Z^(58:ℝ) := by norm_num [Real.rpow_natCast,pow_succ]; ring
    _ ≤ Z^(64:ℝ) := Real.rpow_le_rpow_of_exponent_le hevent.uniform.1.le (by norm_num)

set_option maxHeartbeats 600000 in
theorem plain_family_cap {κ : Type u} [Fintype κ] {N : ℕ} {ε Z : ℝ}
    (hevent : Event.{u} N ε Z) (r : Source κ (1/4) (9/4)) (σ : Character) (radius : ℝ)
    (hσ : (σ.modulus.absNorm:ℝ) ≤ Z^(9:ℝ)) (hR : (r.R.absNorm:ℝ) ≤ Z^(4:ℝ))
    (hpool : poolCap r ≤ Z^(8:ℝ)) (hr0 : 0 ≤ radius) (hrad : radius ≤ Z^(15:ℝ)) :
    familyConductorBudget r σ radius ≤ Z^(64:ℝ) := by
  have hz := zero_lt_one.trans hevent.uniform.1
  have hpn := pool_norm_cap r Z hevent.uniform.1 hpool
  have hpc0 := poolCap_nonneg r
  have hpn0 : 0 ≤ MixedInnerExceptionalPair.poolNorm r := Finset.sum_nonneg (fun I _ => Nat.cast_nonneg _)
  have hfixed : 0 ≤ innerFixed := by unfold innerFixed; positivity
  calc
    _ = innerFixed*(σ.modulus.absNorm:ℝ)*(r.R.absNorm:ℝ)*(poolCap r)^2*
        MixedInnerExceptionalPair.poolNorm r*radius := by
      unfold familyConductorBudget MixedInnerExceptionalPair.fixedConductorCost innerFixed
      ring
    _ ≤ Z*Z^(9:ℝ)*Z^(4:ℝ)*(Z^(8:ℝ))^2*Z^(16:ℝ)*Z^(15:ℝ) := by
      have hc := hevent.inner
      gcongr
    _ = Z^(61:ℝ) := by norm_num [Real.rpow_natCast,pow_succ]; ring
    _ ≤ Z^(64:ℝ) := Real.rpow_le_rpow_of_exponent_le hevent.uniform.1.le (by norm_num)

end
end Candidate.FourthPower.RepairedConductorCaps
