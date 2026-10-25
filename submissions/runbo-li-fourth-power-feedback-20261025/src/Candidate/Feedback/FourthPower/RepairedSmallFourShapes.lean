/- Copyright (c) 2026 Sil. Apache-2.0.
Exact raw scalar shapes of all four actual small-source components,
under one homogeneous profile factor. No component estimate is assumed.

-/
import Candidate.Feedback.FourthPower.RepairedSmallCommonProfile

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedSmallFourShapes
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondWindowBudget
open MixedPrincipalPair MixedPrincipalBudget MixedPrincipalCentered
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedOriginalNormCap MixedOriginalTail
open MixedFirstProfileEnvelope
open RepairedSmallRawBudget RepairedSmallCostControl RepairedSmallCommonProfile
open MixedPrincipalWindow
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def nativeShape (s : Source ι a b) (η : Character) (seed : Id) (Z exponent : ℝ) : ℝ :=
  (η.modulus.absNorm:ℝ)*(sourceVolume s/pairNorm s.d)^2*Z^exponent/(seed.absNorm:ℝ)

def exceptionalShape (s : Source ι a b) (seed : Id) (K Z exponent : ℝ) : ℝ :=
  sourceVolume s*commonPhysicalCost s K*Z^exponent/((pairNorm s.d)^2*(seed.absNorm:ℝ))

def zeroShape (s : Source ι a b) (seed : Id) (K Z exponent : ℝ) : ℝ :=
  K*sourceNormCap s.P b s.T s.d*Z^exponent/(seed.absNorm:ℝ)

def tailShape (u : Id) (Z saving : ℝ) : ℝ := Z^(-saving)/(u.absNorm:ℝ)

theorem native_shape_nonneg (s : Source ι a b) (η : Character) (seed : Id)
    (Z exponent : ℝ) (hZ : 0≤Z) : 0≤nativeShape s η seed Z exponent := by
  have hp := Real.rpow_nonneg hZ exponent
  unfold nativeShape
  positivity

theorem exceptional_shape_nonneg (s : Source ι a b) (seed : Id)
    (K Z exponent : ℝ) (hK : 0≤K) (hZ : 0≤Z) :
    0≤exceptionalShape s seed K Z exponent := by
  have hv := (sourceVolume_pos s).le
  have hc := commonPhysicalCost_nonneg s K hK
  have hz := Real.rpow_nonneg hZ exponent
  unfold exceptionalShape
  positivity

theorem zero_shape_nonneg (s : Source ι a b) (seed : Id)
    (K Z exponent : ℝ) (hK : 0≤K) (hZ : 0≤Z) : 0≤zeroShape s seed K Z exponent := by
  have ht := s.total_pos
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hP (i : ι) : 0<s.P i := zero_lt_one.trans_le (s.hP i)
  have hprod : 0 ≤ ∏ i, 2*s.P i :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (hP i).le)
  have hz := Real.rpow_nonneg hZ exponent
  unfold zeroShape sourceNormCap
  positivity

theorem tail_shape_nonneg (u : Id) (Z saving : ℝ) (hZ : 0≤Z) : 0≤tailShape u Z saving := by
  exact div_nonneg (Real.rpow_nonneg hZ _) (Nat.cast_nonneg _)

theorem native_cost_le_common (s : Source ι a b) (N j J : ℕ) (Kslot C : ℝ)
    (T U : Finset (ℕ×ℕ)) (t₀ V v Z exponent : ℝ) (η : Character) (seed : Id)
    (hN : Fintype.card ι≤N) (hK : 1≤Kslot) (hM : ∀i,s.M i≤Kslot)
    (hC : 0≤C) (hT : T⊆U) (hj : j≤J) (hV : 0≤V) (hZ : 0≤Z) :
    simpleCost s C j T t₀ V v Z exponent η seed≤
      (C*((Kslot^N)^2*(2:ℝ)^N))*commonProfile s J U t₀ V v*nativeShape s η seed Z exponent := by
  have hp := profile_powers_le s j (2*j) J T U t₀ V v hT hj
    (Nat.mul_le_mul_left 2 hj) hV
  have hslot := slot_cost_le s N Kslot hN hK hM
  have hold : 0≤(sourceControl T s.W₁*sourceControl T s.W₂)^2*
      (height t₀ V s.t₁ s.t₂)^j*heightEnvelope v^(2*j) := by
    have hh : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    have hv := (heightEnvelope_pos v).le
    positivity
  have hc := mul_le_mul_of_nonneg_left
    (mul_le_mul hslot hp hold (by positivity)) hC
  have he := mul_le_mul_of_nonneg_right hc (native_shape_nonneg s η seed Z exponent hZ)
  convert he using 1 <;> dsimp only [simpleCost, nativeShape] <;> ring

def exceptionalRawCost (s : Source ι a b) (j : ℕ) (T : Finset (ℕ×ℕ)) (Q seed : Id)
    (Ckernel A Csum Z ε δ Bnorm εsum K v : ℝ) : ℝ :=
  (Ckernel*A*heightBase v^(2*j)*(windowMoment j)^2)*
    savedBudget s j T Q Z ε (K/16) 1*Z^(2*Bnorm*δ)*
    (Csum*Z^εsum/(seed.absNorm:ℝ))*sourceVolume s

def fullShape (s : Source ι a b) (η : Character) (u seed : Id)
    (K Z nativeLoss exceptionalLoss zeroLoss saving : ℝ) : ℝ :=
  zeroShape s seed K Z zeroLoss+nativeShape s η seed Z nativeLoss+
    exceptionalShape s seed K Z exceptionalLoss+tailShape u Z saving

theorem exceptional_cost_le_common (s : Source ι a b) (N j J : ℕ) (Kslot : ℝ)
    (T U : Finset (ℕ×ℕ)) (Q seed : Id)
    (Ckernel A Csum Z ε δ Bnorm εsum K t₀ V v : ℝ)
    (hN : Fintype.card ι≤N) (hKslot : 1≤Kslot) (hM : ∀i,s.M i≤Kslot)
    (hT : T⊆U) (hj : 2*j≤J) (hV : 0≤V) (hZ : 0<Z) (hK : 0<K)
    (hCkernel : 0≤Ckernel) (hA : 0≤A) (hCsum : 0≤Csum) :
    exceptionalRawCost s j T Q seed Ckernel A Csum Z ε δ Bnorm εsum K v≤
      (Ckernel*A*Csum*(windowMoment j)^2*fixedQCost Q*
        ((1024:ℝ)^N*(Kslot^N)^3)^2)*commonProfile s J U t₀ V v*
      exceptionalShape s seed K Z (2*ε+2*Bnorm*δ+εsum) := by
  have hp := exceptional_profile_le s N j J Kslot T U t₀ V v Z ε
    hN hKslot hM hT hj hV hZ
  have hsaved := savedBudget_exact s j T Q Z ε (K/16) 1 (by positivity) (by norm_num)
  have hscale : 16*(K/16)*(1:ℝ)^4=K := by ring
  simp only [hscale,div_one] at hsaved
  let R:=Ckernel*A*Csum*(windowMoment j)^2*fixedQCost Q*sourceVolume s*commonPhysicalCost s K/
    ((pairNorm s.d)^2*(seed.absNorm:ℝ))*Z^(2*Bnorm*δ+εsum)
  have hR : 0≤R := by
    have hq := fixedQCost_nonneg Q
    have hv := (sourceVolume_pos s).le
    have hc := commonPhysicalCost_nonneg s K hK.le
    have hz := Real.rpow_nonneg hZ.le (2*Bnorm*δ+εsum)
    dsimp only [R]
    positivity
  have he := mul_le_mul_of_nonneg_left hp hR
  unfold exceptionalRawCost
  rw [←hsaved]
  convert he using 1 <;> dsimp only [R,sourcePrefactor,exceptionalShape] <;>
    simp only [Real.rpow_add hZ] <;> ring

end
end Candidate.Feedback.FourthPower.RepairedSmallFourShapes
