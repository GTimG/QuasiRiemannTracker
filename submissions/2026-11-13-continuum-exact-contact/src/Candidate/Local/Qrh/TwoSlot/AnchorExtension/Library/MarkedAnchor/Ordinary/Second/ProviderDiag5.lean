/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: absorption constants `kF`, `k0`, `kT` and the generic absorptions.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderDiag4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectorLocalization CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentFirstMixedAllowance
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedFirstCommonSum MixedFirstPaidRetained
open MixedInnerExceptionalBlock MixedFirstExceptionalWindow
open RepairedRawContext RepairedSourceSideSupply
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open scoped ContDiff
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondWindowBudget
open MixedFirstPhysicalApplication MixedFirstPhysicalBudget MixedFirstRetainedFixed
open MixedFirstExceptionalNormalization RepairedFirstRawSides RepairedFirstRawScalar RepairedFirstRawBlock
open Qrh.MarkedAnchor.Ordinary.RootParameters
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstScale EisensteinSchwartzPoisson
open CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open QRH.Record1252270103KernelMass
open MixedPrincipalBudget MixedPrincipalCentered MixedCommonCoefficient
open MixedInnerExceptionalLedger MixedFirstAllocatedRemainders MixedFirstProfileEnvelope
open QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
open QRH.SilDensitySplit.CubeFree.Second.Provider Qrh.MarkedAnchor.Ordinary.Second.Provider
open MixedPrincipalPoolCaps MixedActualRetained
open ActualEisensteinCubic CenteredMomentFirstAmplificationChoice

local instance (priority := 2000) instDecEqSubtypeProvDiag5 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-! ### Generic absorption of the zero-frequency and tail root terms -/

theorem absorb0 (c2 Mall2 R2 Φ16 Hv pM Mc prof2 YE Q Zx : ℝ) (Nm : ℕ)
    (Cc ZeC KN2 BX lZ CM ZeM Ar CY ZeY Zex : ℝ)
    (hc2 : 0 ≤ c2) (hc : c2 ≤ Cc*ZeC) (hM0 : 0 ≤ Mall2) (hM : Mall2 ≤ KN2) (hR2 : 0 ≤ R2)
    (hΦ : 0 ≤ Φ16) (hHv0 : 0 ≤ Hv) (hHv : Hv ≤ 2304*BX*lZ) (hpM : 0 ≤ pM) (hMc0 : 0 ≤ Mc)
    (hMc : Mc ≤ CM*ZeM) (hp0 : 0 ≤ prof2) (hp : prof2 ≤ 4*KN2*Ar) (hY0 : 0 ≤ YE)
    (hY : YE ≤ CY*ZeY) (hQ : 0 ≤ Q) (hZx0 : 0 ≤ Zx) (hZx : Zx ≤ 4*Zex) :
    c2*Mall2*R2*Φ16*Hv*(pM*Mall2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc)*(prof2*YE))*Q*Zx ≤
      (Cc*KN2*R2*Φ16*(2304*BX)*(pM*KN2*(256:ℝ)^Nm*((2:ℝ)^Nm*CM)*(4*KN2*CY))*Q*4)*lZ*
        (ZeC*ZeM*ZeY*Zex)*Ar := by
  have hy1 := hc2.trans hc
  have hK0 := hM0.trans hM
  have hB3 := hHv0.trans hHv
  have h256 : (0:ℝ) ≤ (256:ℝ)^Nm := by positivity
  have h2N : (0:ℝ) ≤ (2:ℝ)^Nm := by positivity
  have hCM0 := hMc0.trans hMc
  have hAr0 := hp0.trans hp
  have hCY0 := hY0.trans hY
  have e1 : c2*Mall2 ≤ (Cc*ZeC)*KN2 := mul_le_mul hc hM hM0 hy1
  have e2 : c2*Mall2*R2*Φ16 ≤ (Cc*ZeC)*KN2*R2*Φ16 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e1 hR2) hΦ
  have n2 : 0 ≤ (Cc*ZeC)*KN2*R2*Φ16 := mul_nonneg (mul_nonneg (mul_nonneg hy1 hK0) hR2) hΦ
  have e3 : c2*Mall2*R2*Φ16*Hv ≤ (Cc*ZeC)*KN2*R2*Φ16*(2304*BX*lZ) := mul_le_mul e2 hHv hHv0 n2
  have n3 : 0 ≤ (Cc*ZeC)*KN2*R2*Φ16*(2304*BX*lZ) := mul_nonneg n2 hB3
  have hP5a : pM*Mall2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc) ≤ pM*KN2*(256:ℝ)^Nm*((2:ℝ)^Nm*(CM*ZeM)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hpM) h256)
      (mul_le_mul_of_nonneg_left hMc h2N) (mul_nonneg h2N hMc0)
      (mul_nonneg (mul_nonneg hpM hK0) h256)
  have hP5b : prof2*YE ≤ (4*KN2*Ar)*(CY*ZeY) := mul_le_mul hp hY hY0 hAr0
  have hP5 : pM*Mall2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc)*(prof2*YE) ≤
      pM*KN2*(256:ℝ)^Nm*((2:ℝ)^Nm*(CM*ZeM))*((4*KN2*Ar)*(CY*ZeY)) :=
    mul_le_mul hP5a hP5b (mul_nonneg hp0 hY0)
      (mul_nonneg (mul_nonneg (mul_nonneg hpM hK0) h256) (mul_nonneg h2N hCM0))
  have n5 : 0 ≤ pM*Mall2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc)*(prof2*YE) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hpM hM0) h256) (mul_nonneg h2N hMc0))
      (mul_nonneg hp0 hY0)
  have n5' : 0 ≤ pM*KN2*(256:ℝ)^Nm*((2:ℝ)^Nm*(CM*ZeM))*((4*KN2*Ar)*(CY*ZeY)) := n5.trans hP5
  have e4 := mul_le_mul e3 hP5 n5 n3
  have e5 := mul_le_mul_of_nonneg_right e4 hQ
  have n6 : 0 ≤ (Cc*ZeC)*KN2*R2*Φ16*(2304*BX*lZ)*
      (pM*KN2*(256:ℝ)^Nm*((2:ℝ)^Nm*(CM*ZeM))*((4*KN2*Ar)*(CY*ZeY)))*Q :=
    mul_nonneg (mul_nonneg n3 n5') hQ
  have e6 := mul_le_mul e5 hZx hZx0 n6
  refine e6.trans (le_of_eq ?_)
  ring

theorem absorbt (c2 Mall2 R2 Cts pM Mc Wm X prof2 : ℝ) (Nm : ℕ)
    (Cc ZeC KN2 CM ZeM Ar XB Wb : ℝ)
    (hc2 : 0 ≤ c2) (hc : c2 ≤ Cc*ZeC) (hM0 : 0 ≤ Mall2) (hM : Mall2 ≤ KN2) (hR2 : 0 ≤ R2)
    (hCts : 0 ≤ Cts) (hpM : 0 ≤ pM) (hMc0 : 0 ≤ Mc) (hMc : Mc ≤ CM*ZeM) (hW0 : 0 ≤ Wm)
    (hW : Wm ≤ Wb) (hX0 : 0 ≤ X) (hX : X ≤ XB) (hp0 : 0 ≤ prof2) (hp : prof2 ≤ 4*KN2*Ar) :
    c2*(Mall2*R2*Cts*(pM*Mall2*(256:ℝ)^Nm*Wm*((2:ℝ)^Nm*Mc)*(128*X*Wm*prof2))) ≤
      (Cc*KN2*R2*(pM*KN2*(256:ℝ)^Nm*((2:ℝ)^Nm*CM)*(128*4*KN2)))*(ZeC*ZeM*XB*Wb*Wb)*Cts*Ar := by
  have hy1 := hc2.trans hc
  have hK0 := hM0.trans hM
  have h256 : (0:ℝ) ≤ (256:ℝ)^Nm := by positivity
  have h2N : (0:ℝ) ≤ (2:ℝ)^Nm := by positivity
  have hCM0 := hMc0.trans hMc
  have hAr0 := hp0.trans hp
  have hWb := hW0.trans hW
  have hXB := hX0.trans hX
  have i1 : Mall2*R2*Cts ≤ KN2*R2*Cts :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hR2) hCts
  have i2 : pM*Mall2*(256:ℝ)^Nm*Wm ≤ pM*KN2*(256:ℝ)^Nm*Wb :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hpM) h256) hW hW0
      (mul_nonneg (mul_nonneg hpM hK0) h256)
  have i3 : pM*Mall2*(256:ℝ)^Nm*Wm*((2:ℝ)^Nm*Mc) ≤ pM*KN2*(256:ℝ)^Nm*Wb*((2:ℝ)^Nm*(CM*ZeM)) :=
    mul_le_mul i2 (mul_le_mul_of_nonneg_left hMc h2N) (mul_nonneg h2N hMc0)
      (mul_nonneg (mul_nonneg (mul_nonneg hpM hK0) h256) hWb)
  have i4 : 128*X*Wm*prof2 ≤ 128*XB*Wb*(4*KN2*Ar) :=
    mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hX (by norm_num)) hW hW0 (by positivity))
      hp hp0 (by positivity)
  have i5 := mul_le_mul i3 i4 (by positivity)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hpM hK0) h256) hWb) (mul_nonneg h2N hCM0))
  have i6 := mul_le_mul i1 i5
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hpM hM0) h256) hW0) (mul_nonneg h2N hMc0) |>
      fun h => mul_nonneg h (by positivity)) (mul_nonneg (mul_nonneg hK0 hR2) hCts)
  have i7 := mul_le_mul hc i6 (by
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hpM hM0) h256) hW0) (mul_nonneg h2N hMc0)
    have h' : 0 ≤ 128*X*Wm*prof2 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hM0 hR2) hCts) (mul_nonneg this h')) hy1
  refine i7.trans (le_of_eq ?_)
  ring

/-- `log X = BX·log Z` for `X = Z^BX`. -/
theorem log_rpow_eq (Z BX : ℝ) (hZ : 1 < Z) : Real.log (Z^BX) = BX*Real.log Z :=
  Real.log_rpow (zero_lt_one.trans hZ) _

/-- `Z^{freqLoss(1,κ)+κ} = 4·Z^{3κ/2}`. -/
theorem rpow_freqLoss0 (Z κ : ℝ) (hZ : 1 < Z) :
    Z^(frequencyLoss Z 1 κ + κ) = 4*Z^(3*κ/2) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  unfold frequencyLoss
  rw [show κ/2 + Real.logb Z (4*1) + κ = Real.logb Z 4 + 3*κ/2 by ring_nf,
    Real.rpow_add hz, Real.rpow_logb hz hZ.ne' (by norm_num)]

/-- Finishing an absorption: `K·log Z·Z^e·(A/C) ≤ θ·A·T` from `K·(log Z+1)·Z^e ≤ θ·C·T`. -/
theorem finish_absorb (K lZ Ze Amp Cs θ T : ℝ) (hK : 0 ≤ K) (_hl : 0 ≤ lZ) (hZe : 0 ≤ Ze)
    (hA : 0 ≤ Amp) (hC : 0 < Cs) (h : K*(lZ+1)*Ze ≤ θ*Cs*T) :
    K*lZ*Ze*(Amp/Cs) ≤ θ*Amp*T := by
  have h1 : K*lZ*Ze ≤ θ*Cs*T :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK) hZe).trans h
  calc K*lZ*Ze*(Amp/Cs) ≤ (θ*Cs*T)*(Amp/Cs) := mul_le_mul_of_nonneg_right h1 (div_nonneg hA hC.le)
    _ = θ*Amp*T := by field_simp

/-! ### The root constants (fixed before `Z`) -/

/-- Constant of the fixed-inducing root term. -/
def kF (Cc CM BX Kslot Ckernel A Csum : ℝ) (Nm JL : ℕ) (Q : Id) : ℝ :=
  Cc*pcMass*(Kslot^Nm)^2*(1024:ℝ)^Nm*CM*
    ((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
    (Ckernel*A*((1+2*Real.pi)^2)^(2*JL)*(windowMoment JL)^2)*Csum*(2304*BX)*
    (fixedQCost Q*(16:ℝ)^(5/6:ℝ)*(1/4:ℝ)^(-4/3:ℝ))*(((1024:ℝ)^Nm*(Kslot^Nm)^3)^2)*
    ((Kslot^Nm)^2*((2:ℝ)^Nm)^(4/3:ℝ))*((9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nm)^3*(4:ℝ)^(5/6:ℝ))

/-- Constant of the zero-frequency root term. -/
def k0 (Cc CM BX Kslot C0 εL : ℝ) (Nm : ℕ) : ℝ :=
  Cc*(Kslot^Nm)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
    (16*‖paperRadialFourier ballProfile 0‖*C0)*(2304*BX)*
    (pcMass*(Kslot^Nm)^2*(256:ℝ)^Nm*((2:ℝ)^Nm*CM)*(4*(Kslot^Nm)^2*(2*(81/16)*(2:ℝ)^Nm)^εL))*
    ((32:ℝ)^Nm+(16:ℝ)^Nm*((9/4:ℝ)^2*(2:ℝ)^Nm))*4

/-- Constant of the tail root term. -/
def kT (Cc CM Kslot Ct : ℝ) (controlT : Finset (ℕ×ℕ)) (Nm : ℕ) : ℝ :=
  (Cc*(Kslot^Nm)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
    (pcMass*(Kslot^Nm)^2*(256:ℝ)^Nm*((2:ℝ)^Nm*CM)*(128*4*(Kslot^Nm)^2)))*((2:ℝ)^Nm*(2:ℝ)^Nm)*
    (Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)


theorem kF_nonneg (Cc CM BX Kslot Ckernel A Csum : ℝ) (Nm JL : ℕ) (Q : Id) (hCc : 0 ≤ Cc)
    (hCM : 0 ≤ CM) (hBX : 0 ≤ BX) (hK : 0 ≤ Kslot) (hCk : 0 ≤ Ckernel) (hA : 0 ≤ A)
    (hCs : 0 ≤ Csum) : 0 ≤ kF Cc CM BX Kslot Ckernel A Csum Nm JL Q := by
  unfold kF
  have := pcMass_nonneg
  have := fixedQCost_nonneg Q
  positivity

theorem k0_nonneg (Cc CM BX Kslot C0 εL : ℝ) (Nm : ℕ) (hCc : 0 ≤ Cc) (hCM : 0 ≤ CM)
    (hBX : 0 ≤ BX) (hC0 : 0 ≤ C0) : 0 ≤ k0 Cc CM BX Kslot C0 εL Nm := by
  unfold k0
  have := pcMass_nonneg
  positivity

theorem kT_nonneg (Cc CM Kslot Ct : ℝ) (controlT : Finset (ℕ×ℕ)) (Nm : ℕ) (hCc : 0 ≤ Cc)
    (hCM : 0 ≤ CM) (hCt : 0 ≤ Ct) : 0 ≤ kT Cc CM Kslot Ct controlT Nm := by
  unfold kT
  have := pcMass_nonneg
  have := apply_nonneg (controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile
  positivity

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
