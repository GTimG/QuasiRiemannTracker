/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The same fixed-exponent event pays original outer and small-sigma
exceptional conductors. No character norm is hidden in a constant.

Modified by Sil (2026-10-26): Event G; outer_family_cap (OuterFreshAssembly outer conductor of the replaced lane) dropped; pool_norm_cap, linear_sigma_cap, plain_family_cap kept.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedChildCaps
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedPrincipalPoolCaps

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedConductorCaps
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge
open MixedPrincipalPair MixedPrincipalWindow
open MixedOriginalTail MixedInnerExceptionalPair MixedInnerExceptionalLedger MixedPrincipalPoolCaps
open RepairedCapEvent
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem pool_norm_cap {κ : Type u} [Fintype κ] (r : Source κ (1/4) (9/4))
    (Z : ℝ) (hZ : 1 < Z) (hpool : poolCap r ≤ Z^(8:ℝ)) :
    MixedInnerExceptionalPair.poolNorm r ≤ Z^(16:ℝ) := by
  apply (pool_norm_le_square r (by norm_num)).trans
  apply (pow_le_pow_left₀ (poolCap_nonneg r) hpool 2).trans_eq
  rw [pow_two, ← Real.rpow_add (zero_lt_one.trans hZ)]
  norm_num

theorem linear_sigma_cap {D : StepData} {G : StepGates D} {N : ℕ} {ε Z : ℝ} (hevent : Event.{u} G N ε Z)
    (τ σ : Character) (f : Id) (hτ : (τ.modulus.absNorm:ℝ) ≤ Z^(6:ℝ))
    (hf : (f.absNorm:ℝ) ≤ Z^(2:ℝ))
    (hσ : σ.modulus.absNorm ≤ τ.modulus.absNorm *
      (ReferenceCubicCharacter.conductorConstant*f.absNorm) * (Ideal.span {(12:O)}).absNorm) :
    (σ.modulus.absNorm:ℝ) ≤ Z^(9:ℝ) := by
  have hz := zero_lt_one.trans hevent.one_lt
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
theorem plain_family_cap {κ : Type u} [Fintype κ] {D : StepData} {G : StepGates D} {N : ℕ} {ε Z : ℝ}
    (hevent : Event.{u} G N ε Z) (r : Source κ (1/4) (9/4)) (σ : Character) (radius : ℝ)
    (hσ : (σ.modulus.absNorm:ℝ) ≤ Z^(9:ℝ)) (hR : (r.R.absNorm:ℝ) ≤ Z^(4:ℝ))
    (hpool : poolCap r ≤ Z^(8:ℝ)) (hr0 : 0 ≤ radius) (hrad : radius ≤ Z^(15:ℝ)) :
    familyConductorBudget r σ radius ≤ Z^(64:ℝ) := by
  have hz := zero_lt_one.trans hevent.one_lt
  have hpn := pool_norm_cap r Z hevent.one_lt hpool
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
    _ ≤ Z^(64:ℝ) := Real.rpow_le_rpow_of_exponent_le hevent.one_lt.le (by norm_num)

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedConductorCaps
