/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
An earlier native PairAt with its original finite-row and mark dictionaries.
The record contains no moving-scale or mixed-energy estimate. -/
import Candidate.C092.transport.MixedPacketScaleProfiles
import Candidate.C092.transport.WitnessRowSupNative

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
open HeckeDetectorRawFiber HeckeDetectorCoefficientTransfer Cycle25WeightedNumeratorPhysical
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WitnessRowSup
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyBands CenteredMomentDetectorEnergyInitialState
open QRH.Cycle092.WholeSlot QRH.Cycle092.MixedPacketWitness
local notation "O" => HeckeFamily.O

structure EarlierPair {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    {Label : Type} {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i) (ηW : Character)
    (controls : Finset (ℕ×ℕ)) where
  N : ℝ
  Y : ℝ
  l : ℝ
  bΦ : ℝ
  mesh : ℝ
  epsilon : ℝ
  C : ℝ
  W : ℝ→ℂ
  η₀L : Character
  η₀W : Character
  QL : Ideal O
  QW : Ideal O
  degree : ℕ
  pair : PairAt (Slot:=Slot) M H hH N Y l W bΦ mesh epsilon U
    (fixedSourcePrincipal S hS) ηW η₀L η₀W QL QW degree controls C
  selected : Finset Slot
  mark : Slot→FreeRow→ℂ
  thetaL : Slot→RayQuotient.Characters M H
  thetaW : Slot→RayQuotient.Characters M H
  w : Slot→ℝ
  sigmaL : Slot→ℝ
  sigmaW : Slot→ℝ
  vL : Slot→ℝ
  vW : Slot→ℝ
  height : ℝ
  hw : ∀k,0≤w k
  hwm : ∀k,w k ≤ mesh
  hsigmaL : ∀k,sigmaL k=33/50
  hsigmaW : ∀k,sigmaW k=33/50
  height_nonneg : 0≤height
  hvL : ∀k,|vL k|≤height
  hvW : ∀k,|vW k|≤height
  hsum : (∑k∈selected,w k)≤l
  keepL : ∀u∈F.rows,initialKeep (fixedSourcePrincipal S hS) (internalQ QL η₀L) u.val
  keepW : ∀u∈F.rows,initialKeep ηW (internalQ QW η₀W) u.val
  markL : ∀u∈F.rows,∀k∈selected,‖mark k u‖=
    ‖normalizedSlot (fixedSourcePrincipal S hS) (fixedBadMask*idealGenerator 1) 1 u.val
      (originalPools M H 2 U w k) (originalCoefficients M H hH η₀L thetaL W U w sigmaL vL k) 0 (U^(w k))‖
  markW : ∀u∈F.rows,∀k∈selected,‖mark k u‖=
    ‖normalizedSlot ηW (fixedBadMask*idealGenerator 1) 1 u.val
      (originalPools M H 2 U w k) (originalCoefficients M H hH η₀W thetaW W U w sigmaW vW k) 0 (U^(w k))‖

/-- Literal fixed-profile PairAt specialization, including independent
ordinary keep conditions and both original mark presentations. -/
theorem EarlierPair.fixed {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H} {S : Finset (Ideal O)} {hS : ∀P∈S,Prime P}
    {Label : Type} {U a ε cutoff T allowance : ℝ} {i : ℕ}
    {F : Fiber M H Label Slot U a ε cutoff T allowance i} {ηW : Character}
    {controls : Finset (ℕ×ℕ)} (D : EarlierPair M H hH S hS F ηW controls)
    (XL : ℝ) (hXL : 0<XL) (hXN : length U XL≤D.N) (hXY : length U (U^F.m)≤D.Y)
    (hU : 0<U) :
    ∀p : Profiles (1/4) (9/4),finiteEnergyOn D.selected F.rows
      (fixedSourcePrincipal S hS) ηW (p.profile 0) (p.profile 1) 0 0 XL (U^F.m) D.mark ≤
        (D.C*QuadraticInitialBound.diagonalControl radialMajorant*
          (1+D.height)^D.degree*U^(1+D.epsilon))*(p.control controls)^2 := by
  have h := pairAt_fixed_height M H hH D.pair D.selected D.thetaL D.thetaW
    D.w D.sigmaL D.sigmaW D.vL D.vW 0 D.height XL (U^F.m)
    D.hw D.hwm (fun k=>by rw [D.hsigmaL k]) (fun k=>by rw [D.hsigmaL k])
    (fun k=>by rw [D.hsigmaW k]) (fun k=>by rw [D.hsigmaW k])
    D.height_nonneg D.hvL D.hvW D.hsum hXL (Real.rpow_pos_of_pos hU _)
    hXN hXY F.rows D.mark D.keepL D.keepW (fun u hu=>F.row_norm u hu) D.markL D.markW
  simpa only [abs_zero,add_zero] using h

/-- Earlier native PairAt pays each reflected Fourier column times the
actual same-zero ordinary witness and the original selected whole marks. -/
theorem earlier_pair_fourier {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (reverse : Bool) (controls : Finset (ℕ×ℕ)) :
    ∃ Jf Jw : ℕ,∃ C : ℝ,0<C ∧
    ∀{M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
      (hH : RayOrthogonality.globalUnits M≤H)
      (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P),
      CanonicalQuadraticSieve.fixedBadPrimes ⊆ S →
    ∀{Label : Type} {U a ε cutoff T allowance : ℝ} {i : ℕ}
      (F : Fiber M H Label Slot U a ε cutoff T allowance i) (ηW : Character),
      F.reverse=reverse → F.rowData=momentData ηW →
    ∀D : EarlierPair M H hH S hS F ηW controls,
      1<U → 0≤a → 0≤T → 0≤allowance → 0≤D.C → length U (U^F.m)≤D.Y →
    ∀XL : ℝ,0<XL → length U XL≤D.N → ∀j : Fin 2,∀v : ℝ,
      (∑u∈F.rows,‖polynomial (rowCharacter S hS u) false
        (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j) XL 0 (-2*Real.pi*v)*
          fiberPlain F u*∏k∈D.selected,D.mark k u‖^2) ≤
      C*(D.C*QuadraticInitialBound.diagonalControl radialMajorant*
        (1+D.height)^D.degree*U^(1+D.epsilon))*
        (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1)*(1+‖v‖)^(2*Jf) := by
  obtain ⟨Jw,Cw,hCw,hfiber⟩ := fiber_ordinary_moment (Slot:=Slot) reverse controls
  obtain ⟨Jf,Cf,hCf,hprofile⟩ := long_fourier_control controls
  refine ⟨Jf,Jw,12*Cf*Cw^2,by positivity,?_⟩
  intro M _ H hH S hS hbad Label U a ε cutoff T allowance i F ηW hrev hdata
    D hU ha hT hall hC hXY XL hXL hXN j v
  let K := D.C*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+D.height)^D.degree*U^(1+D.epsilon)
  have hK : 0≤K := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    have hh := D.height_nonneg
    dsimp [K];positivity
  have he := hfiber F (fixedSourcePrincipal S hS) ηW hrev hdata D.selected D.mark
    ((numeratorFourierProfiles j 0 v 0).profile 0) ((numeratorFourierProfiles j 0 v 0).support 0)
    0 XL K hU ha hT hall hK (D.fixed XL hXL hXN hXY (zero_lt_one.trans hU))
  have heq : (∑u∈F.rows,‖polynomial (rowCharacter S hS u) false
      (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j) XL 0 (-2*Real.pi*v)*
      fiberPlain F u*∏k∈D.selected,D.mark k u‖^2) =
      (∑u∈F.rows,‖original (fixedSourcePrincipal S hS) (fixedBadMask*idealGenerator 1)
      1 u.val ((numeratorFourierProfiles j 0 v 0).profile 0) 0 XL*
      fiberPlain F u*∏k∈D.selected,D.mark k u‖^2) :=
    Finset.sum_congr rfl (fun u _=>by rw [long_fourier_original S hS hbad u j v XL hXL])
  rw [heq]
  apply he.trans
  calc
    _ ≤ 12*K*(Cf*(1+‖v‖)^(2*Jf))*Cw^2*
        (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1) := by gcongr;exact hprofile j v
    _ = _ := by dsimp [K];ring

#print axioms EarlierPair.fixed
#print axioms earlier_pair_fourier
end
end QRH.Cycle092.MixedPacketScale
