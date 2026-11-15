/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: one side of the diagonal half against its balanced budget (`diag_side_budget`).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderDiag5

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

local instance (priority := 2000) instDecEqSubtypeProvDiag6 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type u} [Fintype ι] {a b : ℝ}

set_option maxHeartbeats 1600000 in
/-- **One side of the diagonal half against its balanced budget** (all three root margins from
the `RootInput`, the Window data from the first label, the counting bounds of the label stack). -/
theorem diag_side_budget {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
    {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {Wsl : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput G M H hH κ Wsl N Holes ε Z Kslot η η₀) (hε : 0 < ε)
    (Nm : ℕ) (hNm : Fintype.card κ ≤ Nm) (hK1 : 1 ≤ Kslot)
    (C Dl : Id) (hC : Supported C) (hD : Supported Dl)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport Dl)
    (hcpC : commonPart C Dl = C) (hcpD : commonPart Dl C = Dl)
    (hNC : (C.absNorm:ℝ) ≤ Z^(8:ℝ)) (hND : (Dl.absNorm:ℝ) ≤ Z^(8:ℝ))
    (hDC : (Dl.absNorm:ℝ) ≤ (C.absNorm:ℝ)^3)
    (E : Finset (CommonIndex C Dl)) (τ : Character)
    (hmod : τ.modulus = η.modulus*Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*
      Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C Dl => P.val) E*activeConductor C Dl})
    (n : ℤ) (hn : Retained (frequencyRadius (firstNominalScale C Dl (∏ P ∈ E, P.val) d.Kroot
      (sourceVolume d.root)) Z (cutoffLoss G N ε)) n)
    (JB : (B : actualAllocations (tuplePools d.root) C) → Finset (liveIndices B.val))
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u) (BX : ℝ) (hBX : 8 ≤ BX)
    (hUX : ∀ u ∈ Us, (Ideal.absNorm u : ℝ) ≤ Z^BX)
    (CM eM Mc : ℝ) (hCM : 0 ≤ CM) (hMc0 : 0 ≤ Mc) (hMc : Mc ≤ CM*Z^eM)
    (hJ : ∀ B, Fintype.card (JB B) ≤ Nm)
    (hWB : ∀ B, slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B) ≤
      (2:ℝ)^Nm*Z^(uMax G ε (∑ i, d.w i)))
    (JL : ℕ) (cL controlT : Finset (ℕ×ℕ)) (Q : Id)
    (εL Bnorm δ εsum saving C0 Ckernel A Csum Ct : ℝ) (hεL : 0 ≤ εL) (hC0 : 0 ≤ C0)
    (hCk : 0 ≤ Ckernel) (hA : 0 ≤ A) (hCsum : 0 ≤ Csum) (hCt : 0 ≤ Ct)
    (Cc eC : ℝ) (hCc : 0 ≤ Cc)
    (hcard : ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ)^2 ≤ Cc*Z^eC)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Cside : ℝ) (hCs : 0 < Cside) (hJL : 2*JL ≤ J)
    (hcL : cL ⊆ control) (h00 : (0,0) ∈ control)
    (θ0 θf θt : ℝ) (hθ0 : 0 ≤ θ0) (hθt : 0 ≤ θt)
    (hAf : kF Cc CM BX Kslot Ckernel A Csum Nm JL Q*(Real.log Z + 1)*
      Z^(eC+eM+2*Bnorm*δ+εsum+2*εL+5*cutoffLoss G N ε/4) ≤ θf*Cside*Z^(3*ε))
    (hA0 : k0 Cc CM BX Kslot C0 εL Nm*(Real.log Z + 1)*
      Z^(eC+eM+εL+3*cutoffLoss G N ε/2) ≤ θ0*Cside*Z^(3*ε))
    (hAt : kT Cc CM Kslot Ct controlT Nm*(Real.log Z + 1)*Z^(eC+eM+BX+2-saving) ≤
      θt*Cside*Z^(3*ε-20)) :
    ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ) *
      ∑ B : actualAllocations (tuplePools d.root) C, ‖allocWeight d.root C B‖^2 *
        (AtotP (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B) *
          ((2:ℝ)^(Fintype.card (JB B)) * Mc) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
            xiB d.root (by norm_num) d.cover C JB Us (childScale Z (cutoffLoss G N ε) n)
              ((2/9)*Z^d.ell)
              (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))
              (fun B => max 1 (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
                (restOf d.root (by norm_num) d.cover C B (JB B)).T
                (restOf d.root (by norm_num) d.cover C B (JB B)).d))
              JL cL controlT Q Z εL (alphaP G ε) Bnorm δ εsum saving C0 Ckernel A Csum Ct B)) ≤
      (θ0+θf+θt)*balancedBudget d.root τ C Dl (amplitude d.root d.t₀ d.V J control Cside) Z (3*ε) := by
  have hZ1 := d.one_lt_Z
  have hz : 0 < Z := zero_lt_one.trans hZ1
  have hZ5 := d.hZ
  set κc := cutoffLoss G N ε with hκc
  have hκ0 : 0 ≤ κc := by
    rw [hκc]; unfold cutoffLoss; have := (internal_spec G N ε hε).1; positivity
  have hV0 := sourceVolume_pos d.root
  have hVZ := RepairedRootCaps.root_volume_cap M H hH d
  have hVinv := RepairedRootCaps.root_volume_inverse M H hH d
  obtain ⟨h5, h4⟩ := root_width_gates d hε
  set uM := uMax G ε (∑ i, d.w i) with huM
  set Amp := amplitude d.root d.t₀ d.V J control Cside with hAmp
  have hAmp0 : 0 ≤ Amp := amplitude_nonneg d.root d.t₀ d.V d.hV J control Cside hCs.le
  have hAr0 : 0 ≤ Amp/Cside := div_nonneg hAmp0 hCs.le
  have hZBX : Z^(8:ℝ) ≤ Z^BX := Real.rpow_le_rpow_of_exponent_le hZ1.le hBX
  have hZ8 : Z ≤ Z^(8:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num : (1:ℝ) ≤ 8)
  have hX3 : 3 ≤ Z^BX := by linarith
  have hX1 : 1 ≤ Z^BX := by linarith
  have hPX : poolCap d.root ≤ Z^BX := d.hpool.trans hZBX
  have hlogZ := Real.log_nonneg hZ1.le
  have hHv0 : 0 ≤ 2304*Real.log (Z^BX) := by have := Real.log_nonneg hX1; positivity
  have hHv : 2304*Real.log (Z^BX) = 2304*BX*Real.log Z := by rw [log_rpow_eq Z BX hZ1]; ring
  -- the live and residual caps
  have h2N : (2:ℝ)^(Fintype.card κ) ≤ (2:ℝ)^Nm := pow_le_pow_right₀ (by norm_num) hNm
  set Yr := (9/4:ℝ)^2*(2:ℝ)^Nm*sourceVolume d.root with hYrdef
  have hYr : ∀ B, sourceNormCap (allocatedLiveSource d.root (by norm_num) d.cover C B).P (9/4)
      (allocatedLiveSource d.root (by norm_num) d.cover C B).T
      (allocatedLiveSource d.root (by norm_num) d.cover C B).d ≤ Yr := by
    intro B
    refine (live_normCap_le d.root (by norm_num) d.cover C B).trans ?_
    rw [hYrdef]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2N (by norm_num)) hV0.le
  set q := (81/16:ℝ)*(2:ℝ)^Nm*Z with hq
  have hq1 : 1 ≤ q := by
    rw [hq]; have : (1:ℝ) ≤ (2:ℝ)^Nm := one_le_pow₀ (by norm_num); nlinarith
  have hYrq : Yr ≤ q := by
    rw [hYrdef, hq]
    have : (0:ℝ) ≤ (2:ℝ)^Nm := by positivity
    have e : (9/4:ℝ)^2 = 81/16 := by norm_num
    rw [e]; exact mul_le_mul_of_nonneg_left hVZ (by positivity)
  set Yup := 2*(81/16:ℝ)*(2:ℝ)^Nm*Z with hYup
  have hYq : Yup = 2*q := by rw [hYup, hq]; ring
  have hYup0 : 0 ≤ Yup := by rw [hYq]; linarith
  have hY : ∀ B, 1 ≤ max 1 (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
        (restOf d.root (by norm_num) d.cover C B (JB B)).T (restOf d.root (by norm_num) d.cover C B (JB B)).d) ∧
      max 1 (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
        (restOf d.root (by norm_num) d.cover C B (JB B)).T (restOf d.root (by norm_num) d.cover C B (JB B)).d) ≤ Yup ∧
      max 1 (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
        (restOf d.root (by norm_num) d.cover C B (JB B)).T (restOf d.root (by norm_num) d.cover C B (JB B)).d) ≤
        1 + sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
          (restOf d.root (by norm_num) d.cover C B (JB B)).T (restOf d.root (by norm_num) d.cover C B (JB B)).d := by
    intro B
    have h0 := normCap_nonneg (restOf d.root (by norm_num) d.cover C B (JB B))
    have h1 := (rest_normCap_le d.root (by norm_num) d.cover C B (JB B)).trans ((hYr B).trans hYrq)
    refine ⟨le_max_left _ _, max_le (by rw [hYq]; linarith) (by rw [hYq]; linarith), ?_⟩
    exact max_le (by linarith) (by linarith)
  -- the Window data
  set Tsec := firstNominalScale C Dl (∏ P ∈ E, P.val) d.Kroot (sourceVolume d.root) with hTsec
  have hsec : Tsec ≤ 1*firstNominalScale C Dl
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C Dl => P.val) E}) d.Kroot
      (sourceVolume d.root) := by rw [fns_gen_eq, one_mul]
  -- sizes
  have hMall := pow_le_pow_left₀ (zero_le_one.trans (prodM_ge d.root))
    (prodM_le d.root Kslot Nm hNm d.hM hK1) 2
  have hprof : (profileCap d.root)^2 ≤ 4*(Kslot^Nm)^2*(Amp/Cside) :=
    (profileCap_sq_le d.root control h00 Kslot Nm hNm d.hM hK1).trans
      (mul_le_mul_of_nonneg_left (controls_sq_le_amplitude d.root d.t₀ d.V d.hV J control Cside hCs)
        (by positivity))
  have hpc := pcMass_nonneg
  have hR2 : (0:ℝ) ≤ (Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ) := by positivity
  have hcard0 : (0:ℝ) ≤ ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ)^2 :=
    sq_nonneg _
  have hMp0 : (0:ℝ) ≤ (∏ i, d.root.M i)^2 := sq_nonneg _
  have hprof0 : (0:ℝ) ≤ (profileCap d.root)^2 := sq_nonneg _
  have hCM0 : 0 ≤ CM*Z^eM := hMc0.trans hMc
  have hFour : (0:ℝ) ≤ ‖paperRadialFourier ballProfile 0‖ := norm_nonneg _
  -- hroot0
  have hcs := childScale_le_core C Dl hC hD hcpC hcpD E τ η hmod d.Kroot (sourceVolume d.root) Z κc κc
    hZ1 d.hKlow hV0 n hn
  have hroot0 := hroot0_of_core d.root τ C Dl Amp Z (3*ε)
    ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ)
    (∏ i, d.root.M i) ((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))
    ‖paperRadialFourier ballProfile 0‖ C0 (2304*Real.log (Z^BX)) pcMass Mc (profileCap d.root) Yup εL
    (childScale Z κc n) ((2:ℝ)^Nm*Z^uM) Yr ((9/4:ℝ)^2*(2:ℝ)^Nm) uM
    (frequencyLoss Z 1 κc + κc) θ0 Nm hZ1 hAmp0 hθ0 hcs rfl (by rw [hYrdef]; positivity) le_rfl (by positivity) h5 h4
    (by positivity)
    (by
      have hab := absorb0
        (((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ)^2)
        ((∏ i, d.root.M i)^2) ((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))
        (16*‖paperRadialFourier ballProfile 0‖*C0) (2304*Real.log (Z^BX)) pcMass Mc
        ((profileCap d.root)^2) (Yup^εL) ((32:ℝ)^Nm+(16:ℝ)^Nm*((9/4:ℝ)^2*(2:ℝ)^Nm))
        (Z^(frequencyLoss Z 1 κc + κc)) Nm Cc (Z^eC) ((Kslot^Nm)^2) BX (Real.log Z) CM (Z^eM)
        (Amp/Cside) ((2*(81/16:ℝ)*(2:ℝ)^Nm)^εL) (Z^εL) (Z^(3*κc/2))
        hcard0 hcard hMp0 hMall hR2 (by positivity) hHv0 hHv.le hpc hMc0 hMc hprof0 hprof
        (Real.rpow_nonneg (by rw [hYup]; positivity) _)
        (by rw [hYup, Real.mul_rpow (by positivity) hz.le])
        (by positivity) (Real.rpow_nonneg hz.le _) (rpow_freqLoss0 Z κc hZ1).le
      refine hab.trans ?_
      have hzz : Z^eC*Z^eM*Z^εL*Z^(3*κc/2) = Z^(eC+eM+εL+3*κc/2) := by
        simp only [Real.rpow_add hz]
      rw [hzz]
      have hk0 : 0 ≤ k0 Cc CM BX Kslot C0 εL Nm := k0_nonneg Cc CM BX Kslot C0 εL Nm hCc hCM
        (by linarith) hC0
      have := finish_absorb (k0 Cc CM BX Kslot C0 εL Nm) (Real.log Z) (Z^(eC+eM+εL+3*κc/2)) Amp Cside
        θ0 (Z^(3*ε)) hk0 hlogZ (Real.rpow_nonneg hz.le _) hAmp0 hCs hA0
      unfold k0 at this
      exact this)
  -- hrootf
  have hKc : 0 ≤ Ckernel*A*((1+2*Real.pi)^2)^(2*JL)*(windowMoment JL)^2 := by positivity
  have hfq := fixedQCost_nonneg Q
  have hsl := slotCost_nonneg d.root
  have hBX0 : 0 ≤ BX := by linarith
  have hlX : 0 ≤ Real.log (Z^BX) := Real.log_nonneg hX1
  have hrootf := hrootf_of_margin d hε
    ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ) pcMass
    (∏ i, d.root.M i) Mc ((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))
    (Ckernel*A*((1+2*Real.pi)^2)^(2*JL)*(windowMoment JL)^2) (2*Bnorm*δ) Csum εsum
    (2304*Real.log (Z^BX))
    (fixedQCost Q*(sourceProfile d.root JL cL Z εL)^2*(16:ℝ)^(5/6:ℝ)*(1/4:ℝ)^(-4/3:ℝ))
    (slotCost d.root) (θf*Amp*Z^(3*ε)) Nm
    (by
      have := sq_nonneg (sourceProfile d.root JL cL Z εL)
      positivity)
    (habsf_of_sizes d.root d.hunit d.t₀ d.V d.hV J JL hJL cL control hcL Z εL Cside θf ε hZ1 hCs
      ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ) Cc eC pcMass Mc CM eM
      ((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))
      (Ckernel*A*((1+2*Real.pi)^2)^(2*JL)*(windowMoment JL)^2) (2*Bnorm*δ) Csum εsum (Z^BX) BX κc
      Kslot Nm Q hCc hCM hBX0 hcard hpc hMc0 hMc hR2 hKc hCsum hX1 le_rfl hNm d.hM hK1 (by norm_num)
      (by unfold kF at hAf; exact hAf))
  -- hroott
  have hsup := apply_nonneg (controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile
  have hWm : (2:ℝ)^Nm*Z^uM ≤ (2:ℝ)^Nm*Z := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith : uM ≤ 1)
  have hbud := budget_lower d.root τ C Dl hC.1 hD.1 Amp Z (3*ε) hZ1 hAmp0 hVinv hNC hND
  have hroott : ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ)^2 *
      ((∏ i, d.root.M i)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        (Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving))*
        (pcMass * (∏ i, d.root.M i)^2 * (256:ℝ)^Nm * ((2:ℝ)^Nm*Z^uM) * ((2:ℝ)^Nm * Mc) *
          (128 * Z^BX * ((2:ℝ)^Nm*Z^uM) * (profileCap d.root)^2))) ≤
        θt*balancedBudget d.root τ C Dl Amp Z (3*ε) := by
    have hab := absorbt
      (((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ)^2)
      ((∏ i, d.root.M i)^2) ((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))
      (Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)) pcMass Mc
      ((2:ℝ)^Nm*Z^uM) (Z^BX) ((profileCap d.root)^2) Nm Cc (Z^eC) ((Kslot^Nm)^2) CM (Z^eM)
      (Amp/Cside) (Z^BX) ((2:ℝ)^Nm*Z)
      hcard0 hcard hMp0 hMall hR2 (by positivity) hpc hMc0 hMc (by positivity) hWm
      (by positivity) le_rfl hprof0 hprof
    refine hab.trans ?_
    have hzz : Z^(eC+eM+BX+2-saving) = Z^eC*Z^eM*Z^BX*Z*Z*Z^(-saving) := by
      rw [show eC+eM+BX+2-saving = eC+eM+BX+1+1+(-saving) by ring]
      simp only [Real.rpow_add hz, Real.rpow_one]
    have hkT := kT_nonneg Cc CM Kslot Ct controlT Nm hCc hCM hCt
    have hstep : kT Cc CM Kslot Ct controlT Nm*Z^(eC+eM+BX+2-saving) ≤ θt*Cside*Z^(3*ε-20) := by
      refine le_trans ?_ hAt
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact le_mul_of_one_le_right hkT (by linarith)
    have e1 : (Cc*(Kslot^Nm)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        (pcMass*(Kslot^Nm)^2*(256:ℝ)^Nm*((2:ℝ)^Nm*CM)*(128*4*(Kslot^Nm)^2)))*
        (Z^eC*Z^eM*Z^BX*((2:ℝ)^Nm*Z)*((2:ℝ)^Nm*Z))*
        (Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving))*(Amp/Cside) =
        (kT Cc CM Kslot Ct controlT Nm*Z^(eC+eM+BX+2-saving))*(Amp/Cside) := by
      unfold kT
      rw [hzz]
      ring
    rw [e1]
    calc (kT Cc CM Kslot Ct controlT Nm*Z^(eC+eM+BX+2-saving))*(Amp/Cside)
        ≤ (θt*Cside*Z^(3*ε-20))*(Amp/Cside) := mul_le_mul_of_nonneg_right hstep hAr0
      _ = θt*(Amp*Z^(3*ε-20)) := by field_simp
      _ ≤ θt*balancedBudget d.root τ C Dl Amp Z (3*ε) := mul_le_mul_of_nonneg_left hbud hθt
  -- assembly
  exact diag_hbud d.root (by norm_num) (by norm_num) d.cover η τ C Dl hC hD hCD E JB Us hUs
    ((2/9)*Z^d.ell) (fun _ => Mc)
    (fun B => max 1 (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
      (restOf d.root (by norm_num) d.cover C B (JB B)).T (restOf d.root (by norm_num) d.cover C B (JB B)).d))
    JL cL controlT Q Z εL (alphaP G ε) Bnorm δ εsum saving C0 Ckernel A Csum Ct
    d.Kroot Tsec 1 κc κc n Nm Mc ((2:ℝ)^Nm*Z^uM) Yr Yup (Z^BX) Amp (3*ε) θ0 θf θt
    hZ1 d.radial_pos le_rfl hκ0 (by positivity) hεL hC0 hCk hA hCsum hCt hmod hsec hn hDC hJ
    (fun _ => ⟨hMc0, le_rfl⟩) hWB hYr hY hX3 hUX hPX hroot0 hrootf hroott

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
