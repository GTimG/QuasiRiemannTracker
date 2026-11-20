/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine ordinary witness times its original marks has a pointwise outer
bound from the SAME earlier PairAt, at long scale one. No fourth substitution. -/
import Candidate.C092.transport.MixedPacketScaleSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedPacketScale
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open ConcretePrimeRowBridge CanonicalRowCompletion ProbeHighRowFamily HeckeRowClosure ProbePhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorDictionary
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization CenteredMomentLattice
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyBands CenteredMomentDetectorEnergyInitialState
open HeckeDetectorRawFiber HeckeDetectorCoefficientTransfer Cycle25WeightedNumeratorPhysical
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WitnessRowSup
open QRH.Cycle092.MixedPacketWitness QRH.Cycle092.MixedScale
local notation "O" => HeckeFamily.O

def unitProfile : 𝓢(ℝ,ℂ) := normPowerProfile unitWindow (1/2) (3/2)
  (by norm_num) unitWindow_support unitWindow_smooth 0

lemma unitProfile_apply : (unitProfile:ℝ→ℂ)=unitWindow := by
  ext x
  rw [unitProfile,normPowerProfile_apply]
  simp

lemma unitProfile_support : Function.support (unitProfile:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4) := by
  rw [unitProfile_apply]
  intro x hx
  exact ⟨(by norm_num : (1/4:ℝ)≤1/2).trans (unitWindow_support hx).1,
    (unitWindow_support hx).2.trans (by norm_num)⟩

lemma original_unit (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S) (u : FreeRow) :
    original (fixedSourcePrincipal S hS) (fixedBadMask*idealGenerator 1) 1 u.val unitProfile 0 1=1 := by
  let η := fixedSourcePrincipal S hS
  have h := plain_polynomial_eq_row η (canonicalCharacter η u) (fixedBadMask*idealGenerator 1)
    1 u.val (canonical_element η u) unitProfile 1 0 0 (by norm_num)
  rw [twistProfile_zero_zero] at h
  change polynomial (canonicalCharacter η u) false unitProfile 1 0 0 =
    original η (fixedBadMask*idealGenerator 1) 1 u.val unitProfile 0 1 at h
  rw [←h,←polynomial_eq_of_idealCoeff _ (canonicalCharacter η u) (canonical_ideal η u)
    false (unitProfile:ℝ→ℂ) 1 0 0,
    ←numerator_polynomial_eq_moment S hS hbad,unitProfile_apply,unitWindow_polynomial]

/-- Actual pointwise multiplier control is DERIVED from the earlier source,
using its componentwise shortening to a fixed unit-ideal long test. -/
theorem witness_outer {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (reverse : Bool) (controls : Finset (ℕ×ℕ)) :
    ∃ Jw : ℕ,∃ Cw : ℝ,0<Cw ∧
    ∀{M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
      (hH : RayOrthogonality.globalUnits M≤H)
      (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P),
      CanonicalQuadraticSieve.fixedBadPrimes ⊆ S →
    ∀{Label : Type} {U a ε cutoff T allowance : ℝ} {i : ℕ}
      (F : Fiber M H Label Slot U a ε cutoff T allowance i) (ηW : Character),
      F.reverse=reverse → F.rowData=momentData ηW →
    ∀D : EarlierPair M H hH S hS F ηW controls,
      1<U → 0≤a → 0≤T → 0≤allowance → 0≤D.C → 0≤D.N → length U (U^F.m)≤D.Y →
    ∀u∈F.rows,‖fiberPlain F u*∏k∈D.selected,D.mark k u‖^2 ≤
      Cw*(D.C*QuadraticInitialBound.diagonalControl radialMajorant*
        (1+D.height)^D.degree*U^(1+D.epsilon))*
        (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1) := by
  obtain ⟨Jw,C,hC,hfiber⟩ := fiber_ordinary_moment (Slot:=Slot) reverse controls
  refine ⟨Jw,12*(sourceControl controls unitProfile)^2*C^2+1,by positivity,?_⟩
  intro M _ H hH S hS hbad Label U a ε cutoff T allowance i F ηW hrev hdata
    D hU ha hT hall hCsrc hN hXY u hu
  let K := D.C*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+D.height)^D.degree*U^(1+D.epsilon)
  have hK : 0≤K := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    have hh := D.height_nonneg
    dsimp [K];positivity
  have hn : length U 1≤D.N := by simpa [length] using hN
  have he := hfiber F (fixedSourcePrincipal S hS) ηW hrev hdata D.selected D.mark
    unitProfile unitProfile_support 0 1 K hU ha hT hall hK
    (D.fixed 1 (by norm_num) hn hXY (zero_lt_one.trans hU))
  simp_rw [original_unit S hS hbad,one_mul] at he
  have hs := Finset.single_le_sum (s:=F.rows)
    (fun v (_:v∈F.rows)=>sq_nonneg ‖fiberPlain F v*∏k∈D.selected,D.mark k v‖) hu
  apply (hs.trans he).trans
  have hH0 : 0≤1+(2*Real.pi*allowance+(3*i : ℕ)*T) := by positivity
  nlinarith only [mul_nonneg hK (pow_nonneg hH0 (2*Jw+1))]

#print axioms original_unit
#print axioms witness_outer
end
end QRH.Cycle092.MixedPacketScale
