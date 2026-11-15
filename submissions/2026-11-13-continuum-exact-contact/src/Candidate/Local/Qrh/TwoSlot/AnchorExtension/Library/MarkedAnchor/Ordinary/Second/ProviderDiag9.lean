/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: `diag_supply : DiagSupply G` (the diagonal half of every retained first block at `rootChoice`, share `1/2`).
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag`; `alphaP` is the fixed `D.alpha ∈ (0,2/3)`.
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderDiag8

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
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
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
open CenteredMomentFirstPhysicalDyadicAssembly MixedFirstRetainedFixed MixedFirstCommonSum

local instance (priority := 2000) instDecEqSubtypeProvDiag9 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type u} [Fintype ι] {a b : ℝ}

open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentChildRows CenteredMomentFirstColumns
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondLocalization CenteredMomentSupportedTailAggregate
open CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource
open MixedOriginalTail MixedOriginalNormCap MixedOriginalTailPower MixedPoissonLocalization
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedLocalizedDictionary
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete

open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentNaturalFixedRaySource

/-- Absorption with a positive share. -/
theorem absorb_scaled (K e c θ : ℝ) (hθ : 0 < θ) (hec : e < c) :
    ∀ᶠ Z : ℝ in atTop, K*(Real.log Z + 1)*Z^e ≤ θ*Z^c := by
  filter_upwards [eventually_absorb (K/θ) e c hec] with Z hZ
  calc K*(Real.log Z + 1)*Z^e = θ*((K/θ)*(Real.log Z + 1)*Z^e) := by field_simp
    _ ≤ θ*Z^c := mul_le_mul_of_nonneg_left hZ hθ.le

theorem card_sq_le (Cc δc Z : ℝ) (hδc : 0 ≤ δc) (hZ : 1 < Z) {κ : Type} [Fintype κ] (Nm : ℕ)
    (hNm : Fintype.card κ ≤ Nm) {a b : ℝ} (s : Source κ a b) (C : Id) (hC : C ≠ 0)
    (hNC : (C.absNorm:ℝ) ≤ Z^(8:ℝ))
    (hcount : ∀ {ι : Type} [Fintype ι], Fintype.card ι ≤ Nm + 2 → ∀ S : ι → Finset Id, ∀ D : Id,
      D ≠ 0 → ((actualAllocations S D).card:ℝ)^2 ≤ Cc*(D.absNorm:ℝ)^δc) (hCc : 0 ≤ Cc) :
    ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 ≤ Cc*Z^(8*δc) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [Finset.card_univ, Fintype.card_coe]
  have hc : Fintype.card (κ ⊕ Fin 2) ≤ Nm + 2 := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  refine (hcount hc (tuplePools s) C hC).trans (mul_le_mul_of_nonneg_left ?_ hCc)
  rw [Real.rpow_mul hz.le]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNC hδc

set_option maxHeartbeats 3200000 in
/-- **The diagonal supplier** (`DiagSupply`, `Second/ProviderFinal.lean`). -/
theorem diag_supply {D : StepData} (G : StepGates D) : DiagSupply G := by
  intro ε hε meshF hm0 hmF α _ _ M _ H hH W hW hWs bΦ hbΦ η η₀ Q _ hQt hQ72 hQM hQη
  set Nm := Fintype.card α with hNmdef
  set κc := cutoffLoss G Nm ε with hκc
  have hκ0 : 0 ≤ κc := by
    rw [hκc]; unfold cutoffLoss; have := (internal_spec G Nm ε hε).1; positivity
  have hκe : κc ≤ ε/100000 := by
    rw [hκc]; unfold cutoffLoss
    have h1 := (internal_spec G Nm ε hε).2.2.1
    have h2 := (omega_spec G ε hε).2.2.1
    have h3 := (internal_spec G Nm ε hε).1
    linarith
  have hα := alphaP_spec G ε
  set δ := min (ε/160) (1/10) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ ε/160 := min_le_left _ _
  have hδ2 : δ ≤ 1/10 := min_le_right _ _
  set δc := ε/80 with hδc
  obtain ⟨Cc, hCc, hcount⟩ := MixedSourceAssembly.genuine_count_squared.{0} (Nm+2) δc (by positivity)
  obtain ⟨JL, cL, Ckernel, hCk, hQU⟩ := diag_avg_uniformT' Nm (alphaP G ε) 80 (1/4) (9/4) (ε/10) δ 8
    17 1 (ε/10) 40 meshF 31 hα.2.le hα.1 (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hδ0 (by linarith) (by norm_num) (by norm_num) one_pos (by positivity)
    (by norm_num) hm0
  obtain ⟨A, Csum, C0, Ct, controlT, hA, hCsum, hC0, hCt, hev⟩ := hQU (internalQ Q η₀)
    (iq_ne_zero Q η₀) (iq_ne_top Q hQt η₀) (iq_le72 Q hQ72 η₀)
  refine ⟨2*JL, insert (0,0) cL, 1, ?_⟩
  intro J control Cside hJ hctl hCs
  have hCs0 : 0 < Cside := by linarith
  set Kslot := RestoredRootSource.slotBound W hW.continuous hWs with hKs
  have hK1 : 1 ≤ Kslot := (RestoredRootSource.slotBound_spec W hW.continuous hWs).1
  have hJL : 2*JL ≤ J := hJ
  have hcL : cL ⊆ control := (Finset.subset_insert _ _).trans hctl
  have h00 : (0,0) ∈ control := hctl (Finset.mem_insert_self _ _)
  have hF := absorb_scaled (kF Cc 1 8 Kslot Ckernel A Csum Nm JL (internalQ Q η₀))
    (8*δc+ε/4+2*8*δ+ε/10+2*(ε/10)+5*κc/4) (3*ε) ((1/6)*Cside) (by positivity) (by linarith)
  have h0 := absorb_scaled (k0 Cc 1 8 Kslot C0 (ε/10) Nm) (8*δc+ε/4+ε/10+3*κc/2) (3*ε)
    ((1/6)*Cside) (by positivity) (by linarith)
  have hT := absorb_scaled (kT Cc 1 Kslot Ct controlT Nm) (8*δc+ε/4+8+2-31) (3*ε-20)
    ((1/6)*Cside) (by positivity) (by linarith)
  have h7 : ∀ᶠ Z : ℝ in atTop, (81/16:ℝ)*(2:ℝ)^Nm ≤ Z^(7:ℝ) :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 7))) _
  filter_upwards [hev, hF, h0, hT, h7, eventually_ge_atTop ((2:ℝ)^Nm), eventually_ge_atTop cfam]
    with Z hU hFZ h0Z hTZ hZb hZa hZc
  intro k d hKr hmesh p E hE n hdy Mc hMc0 hMc hML hMR
  have hZ1 := d.one_lt_Z
  have hNm : Fintype.card (RootSlot k) ≤ Nm := root_slot_card k
  -- the first label
  have hCD' := commonLabels_supported (activeSource (sourceColumns d.root)
    (sourceCoefficient d.root (by norm_num) 1)) p
  have hparts := first_label_parts d.root (by norm_num) p
  have hsupp := first_label_support d.root (by norm_num) p
  have hcubes := label_cubes d.root (by norm_num) 1 p
  have hnorm := first_label_norm_le d.root (by norm_num) (by norm_num) p
  have hNC : (p.val.1.absNorm:ℝ) ≤ Z^(8:ℝ) := hnorm.1.trans d.hpool
  have hND : (p.val.2.absNorm:ℝ) ≤ Z^(8:ℝ) := hnorm.2.trans d.hpool
  have hn1 : ((n 1 : ℤ)) ∈ retainedIndices (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z κc) :=
    (n 1).property
  have hret := ((mem_retainedIndices _ _).mp hn1).1
  have hKb := childScale_bounds d hε p E (n 1) hn1 hdy
  have hUX : ∀ u ∈ concreteArtificial d.root p.val.1 p.val.2 hCD'.2.1,
      (Ideal.absNorm u : ℝ) ≤ Z^(8:ℝ) :=
    fun u hu => (artificial_norm_le d.root (by norm_num) _ _ hCD'.2.1 u hu).trans d.hpool
  have hUs := concreteArtificial_squarefree d.root p.val.1 p.val.2 hCD'.2.1
  have hcardC := card_sq_le Cc δc Z (by positivity) hZ1 Nm hNm d.root p.val.1 hCD'.1.1 hNC
    hcount hCc.le
  have hcardD := card_sq_le Cc δc Z (by positivity) hZ1 Nm hNm d.root p.val.2 hCD'.2.1 hND
    hcount hCc.le
  have hMc' : Mc ≤ 1*Z^(ε/4) := by rw [one_mul]; exact hMc
  have hFZ' : kF Cc 1 8 Kslot Ckernel A Csum Nm JL (internalQ Q η₀)*(Real.log Z + 1)*
      Z^(8*δc+ε/4+2*8*δ+ε/10+2*(ε/10)+5*κc/4) ≤ (1/6)*Cside*Z^(3*ε) := hFZ
  have hLeft := fun χ ξ : RayCharacter =>
    diag_side_at d hε Nm hNm hK1 meshF hm0 hmesh hmF p.val.1 p.val.2 hCD'.1 hCD'.2 hsupp
      hparts.1 hparts.2 hNC hND hcubes.1 E (fixedPair η p.val.1 p.val.2 hCD'.1 E χ (ξ⁻¹)).left
      (fixedPair η p.val.1 p.val.2 hCD'.1 E χ (ξ⁻¹)).left_modulus (n 1) hret hKb.1 hKb.2
      (concreteArtificial d.root p.val.1 p.val.2 hCD'.2.1) hUs hUX Mc hMc0 hMc'
      (internalQ Q η₀) JL cL controlT (ε/10) δ (ε/10) 31 C0 Ckernel A Csum Ct (by positivity)
      hC0.le hCk hA.le hCsum.le hCt.le hU.2 Cc (8*δc) hCc.le hcardC J control Cside hCs0 hJL hcL h00
      (1/6) (1/6) (1/6) (by norm_num) (by norm_num) hFZ h0Z hTZ hZa hZb hZc
  have hRight := fun χ ξ : RayCharacter =>
    diag_side_at d hε Nm hNm hK1 meshF hm0 hmesh hmF p.val.2 p.val.1 hCD'.2 hCD'.1 hsupp.symm
      hparts.2 hparts.1 hND hNC hcubes.2 (CenteredMomentFirstMixedRightTransport.swapSubset p.val.1 p.val.2 E)
      (fixedPair η p.val.1 p.val.2 hCD'.1 E χ (ξ⁻¹)).right
      (CenteredMomentFirstMixedRightTransport.right_modulus η p.val.1 p.val.2 hCD'.1 E χ (ξ⁻¹)
        (fixedPair η p.val.1 p.val.2 hCD'.1 E χ (ξ⁻¹))) (n 1)
      (by
        rw [CenteredMomentFirstMixedRightTransport.swapSubset_product,
          CenteredMomentFirstMixedRightTransport.nominal_swap]
        exact hret) hKb.1 hKb.2
      (concreteArtificial d.root p.val.1 p.val.2 hCD'.2.1) hUs hUX Mc hMc0 hMc'
      (internalQ Q η₀) JL cL controlT (ε/10) δ (ε/10) 31 C0 Ckernel A Csum Ct (by positivity)
      hC0.le hCk hA.le hCsum.le hCt.le hU.2 Cc (8*δc) hCc.le hcardD J control Cside hCs0 hJL hcL h00
      (1/6) (1/6) (1/6) (by norm_num) (by norm_num) hFZ h0Z hTZ hZa hZb hZc
  choose XL hXL using hLeft
  choose XR hXR using hRight
  have hZ0 : (0:ℝ) ≤ Z := by linarith
  have hAmp0 := amplitude_nonneg d.root d.t₀ d.V d.hV J control Cside hCs0.le
  unfold DiagHalf
  refine ⟨fun χ ξ => max 0 (XL χ ξ), fun χ ξ => max 0 (XR χ ξ), ?_, ?_, ?_, ?_⟩
  · intro χ ξ v
    have hp : (1+‖v‖)^(2*JL) ≤ (1+‖v‖)^(2*J) :=
      pow_le_pow_right₀ (by linarith [norm_nonneg v]) (by omega)
    have hp0 : 0 ≤ (1+‖v‖)^(2*JL) := by positivity
    refine ((hXL χ ξ).1 v).trans ?_
    calc XL χ ξ * (1+‖v‖)^(2*JL) ≤ max 0 (XL χ ξ) * (1+‖v‖)^(2*JL) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hp0
      _ ≤ max 0 (XL χ ξ) * (1+‖v‖)^(2*J) := mul_le_mul_of_nonneg_left hp (le_max_left _ _)
  · intro χ ξ v
    have hp : (1+‖v‖)^(2*JL) ≤ (1+‖v‖)^(2*J) :=
      pow_le_pow_right₀ (by linarith [norm_nonneg v]) (by omega)
    have hp0 : 0 ≤ (1+‖v‖)^(2*JL) := by positivity
    refine ((hXR χ ξ).1 v).trans ?_
    calc XR χ ξ * (1+‖v‖)^(2*JL) ≤ max 0 (XR χ ξ) * (1+‖v‖)^(2*JL) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hp0
      _ ≤ max 0 (XR χ ξ) * (1+‖v‖)^(2*J) := mul_le_mul_of_nonneg_left hp (le_max_left _ _)
  · intro χ ξ
    have hB := balancedBudget_nonneg d.root (fixedPair η p.val.1 p.val.2 hCD'.1 E χ (ξ⁻¹)).left
      p.val.1 p.val.2 _ Z (3*ε) hAmp0 hZ0
    refine max_le (by positivity) ((hXL χ ξ).2.trans (le_of_eq (by ring)))
  · intro χ ξ
    have hB := balancedBudget_nonneg d.root (fixedPair η p.val.1 p.val.2 hCD'.1 E χ (ξ⁻¹)).right
      p.val.2 p.val.1 _ Z (3*ε) hAmp0 hZ0
    refine max_le (by positivity) ((hXR χ ξ).2.trans (le_of_eq (by ring)))

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
