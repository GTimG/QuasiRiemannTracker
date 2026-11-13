/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: root-level sizes and the width gates.

* `first_label_norm_le`: first labels have norm `≤ poolCap`.
* `live_normCap_le`, `rest_normCap_le`: the live and residual norm caps are `≤ b²·2^N·V`.
* `root_width_gates`: `5u_max ≤ 1` and `log V + 4u_max ≤ 1` (face + the second-diagonal clause
  of `ReferenceAt`).
* `fns_gen_eq`, `budget_lower`.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag`; the second-diagonal clause is
`(StepGates.reference_at ..).2.2` of the ordinary-anchor `ReferenceAt`.
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderDiag3
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.Provider
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedRootCaps

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
open ActualEisensteinCubic

local instance (priority := 2000) instDecEqSubtypeProvDiag4 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-! ### Root-level sizes -/

/-- First labels are bounded by the pool cap. -/
theorem first_label_norm_le (r : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (p : Labels r ha 1) :
    (Ideal.absNorm p.val.1 : ℝ) ≤ poolCap r ∧ (Ideal.absNorm p.val.2 : ℝ) ≤ poolCap r := by
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp p.property
  have hI := Finset.mem_filter.mp (Finset.mem_product.mp hq).1
  have hJ := Finset.mem_filter.mp (Finset.mem_product.mp hq).2
  have hIs : q.1 ∈ sourceColumns r := by
    have := hI.1; rw [CenteredMomentActiveSource.mem_activeSource] at this; exact this.1
  have hJs : q.2 ∈ sourceColumns r := by
    have := hJ.1; rw [CenteredMomentActiveSource.mem_activeSource] at this; exact this.1
  have e1 : p.val.1 = commonPart q.1 q.2 := by rw [← he]
  have e2 : p.val.2 = commonPart q.2 q.1 := by rw [← he]
  rw [e1, e2]
  constructor
  · exact (by exact_mod_cast absNorm_commonPart_le _ _ hI.2.1 :
      (Ideal.absNorm (commonPart q.1 q.2) : ℝ) ≤ Ideal.absNorm q.1).trans
      (source_column_pool_norm r hb _ hIs)
  · exact (by exact_mod_cast absNorm_commonPart_le _ _ hJ.2.1 :
      (Ideal.absNorm (commonPart q.2 q.1) : ℝ) ≤ Ideal.absNorm q.2).trans
      (source_column_pool_norm r hb _ hJs)

theorem one_le_pairNorm {κ : Type*} [Fintype κ] (r : Source κ a b) : 1 ≤ pairNorm r.d := by
  have h1 : (1:ℝ) ≤ (r.d.1.absNorm:ℝ) := ideal_norm_one_le r.hd.1
  have h2 : (1:ℝ) ≤ (r.d.2.absNorm:ℝ) := ideal_norm_one_le r.hd.2
  unfold pairNorm
  push_cast
  nlinarith

/-- The live norm cap is at most `b²·2^N·V`. -/
theorem live_normCap_le (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) :
    sourceNormCap (allocatedLiveSource s hb cover G B).P b (allocatedLiveSource s hb cover G B).T
      (allocatedLiveSource s hb cover G B).d ≤ b^2*(2:ℝ)^(Fintype.card ι)*sourceVolume s := by
  rw [sourceNormCap_eq_volume]
  have hpn := one_le_pairNorm (allocatedLiveSource s hb cover G B)
  have hT : (allocatedLiveSource s hb cover G B).T = s.T := rfl
  have hP : ∀ i, (allocatedLiveSource s hb cover G B).P i = s.P i.val := fun _ => rfl
  have hX1 := s.hL.trans_le s.hX₁
  have hX2 := s.hL.trans_le s.hX₂
  have hT0 : 0 ≤ s.T := by rw [← s.hpX]; positivity
  have hprod : (∏ i, (allocatedLiveSource s hb cover G B).P i) ≤ ∏ i, s.P i := by
    simp only [hP]
    rw [Finset.prod_coe_sort (liveIndices (allocationSource s hb cover G B).B) s.P]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _ => zero_le_one.trans (s.hP i)) (fun i _ _ => s.hP i)
  have hprod0 : 0 ≤ ∏ i, (allocatedLiveSource s hb cover G B).P i :=
    Finset.prod_nonneg (fun i _ => zero_le_one.trans ((allocatedLiveSource s hb cover G B).hP i))
  have hcard : (2:ℝ)^(Fintype.card (liveIndices B.val)) ≤ (2:ℝ)^(Fintype.card ι) :=
    pow_le_pow_right₀ (by norm_num) (by
      rw [Fintype.card_coe]; exact Finset.card_le_univ _)
  have hV : sourceVolume s = s.T*∏ i, s.P i := by
    unfold sourceVolume; rw [s.hpX]
  rw [hV, hT, div_le_iff₀ (zero_lt_one.trans_le hpn)]
  have hb2 : 0 ≤ b^2 := sq_nonneg b
  calc b^2*(2:ℝ)^(Fintype.card (liveIndices B.val))*(s.T*∏ i, (allocatedLiveSource s hb cover G B).P i)
      ≤ b^2*(2:ℝ)^(Fintype.card ι)*(s.T*∏ i, s.P i) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hcard hb2)
          (mul_le_mul_of_nonneg_left hprod hT0) (mul_nonneg hT0 hprod0) (by positivity)
    _ ≤ b^2*(2:ℝ)^(Fintype.card ι)*(s.T*∏ i, s.P i)*pairNorm (allocatedLiveSource s hb cover G B).d := by
        have : 0 ≤ ∏ i, s.P i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.hP i))
        exact le_mul_of_one_le_right (by positivity) hpn

/-- The residual norm cap is below the live one. -/
theorem rest_normCap_le (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    sourceNormCap (restOf s hb cover G B J).P b (restOf s hb cover G B J).T (restOf s hb cover G B J).d ≤
      sourceNormCap (allocatedLiveSource s hb cover G B).P b (allocatedLiveSource s hb cover G B).T
        (allocatedLiveSource s hb cover G B).d := by
  have h := rest_normCap_mul (allocatedLiveSource s hb cover G B) (fun _ => rfl) J
  have h0 := normCap_nonneg (restOf s hb cover G B J)
  have hW : 1 ≤ slotWidth (allocatedLiveSource s hb cover G B) J := by
    unfold slotWidth
    exact Finset.one_le_prod₀ (fun j _ => by
      have := (allocatedLiveSource s hb cover G B).hP j.val; linarith)
  rw [← h]
  exact le_mul_of_one_le_right h0 hW

/-- The two width gates of `hroot0` from the root face and the reference reserve
(`ReferenceAt` clause 3, `s₀ ≤ S`). -/
theorem root_width_gates {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
    {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {Wsl : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput G M H hH κ Wsl N Holes ε Z Kslot η η₀) (hε : 0 < ε) :
    5*uMax G ε (∑ i, d.w i) ≤ 1 ∧
      Real.logb Z (sourceVolume d.root) + 4*uMax G ε (∑ i, d.w i) - 1 ≤ 0 := by
  have hv := RepairedRootCaps.root_volume_log M H hH d
  obtain ⟨hs0, hSc, hface⟩ := d.hface
  have hsel := sel_bounds G hε d.hface
  have href := (G.reference_at hε hs0 hSc).2.2
  have hρ := G.reference_spec.1
  have hr := rootReserve_spec G
  have hm := mesh_spec G ε hε
  have hc := G.face.2.2.2.2.2.1
  unfold uMax
  constructor
  · nlinarith
  · rw [hv]; nlinarith

/-- `firstNominalScale` sees the inactive subset only through its norm. -/
theorem fns_gen_eq (C D : Id) (E : Finset (CommonIndex C D)) (K V : ℝ) :
    firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K V =
      firstNominalScale C D (∏ P ∈ E, P.val) K V := by
  have hgen : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) =
      (Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) : ℝ) := by
    rw [← ActualEisensteinCubic.primeSubsetGenerator_norm_sq, eisEmbedding_norm_sq_eq_absNorm_span]
  unfold firstNominalScale
  rw [hgen]

/-- The balanced budget from below, with label norms `≤ Z^8` and `V⁻¹ ≤ Z²`. -/
theorem budget_lower (s : Source ι a b) (τ : Character) (C D : Id) (hC : C ≠ 0) (hD : D ≠ 0)
    (Abud Z loss : ℝ) (hZ : 1 < Z) (hA : 0 ≤ Abud) (hV : (sourceVolume s)⁻¹ ≤ Z^(2:ℝ))
    (hNC : (C.absNorm:ℝ) ≤ Z^(8:ℝ)) (hND : (D.absNorm:ℝ) ≤ Z^(8:ℝ)) :
    Abud*Z^(loss-20) ≤ balancedBudget s τ C D Abud Z loss := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hv := sourceVolume_pos s
  have hτ : (1:ℝ) ≤ (τ.modulus.absNorm:ℝ) := ideal_norm_one_le τ.modulus_ne_bot
  have hc1 : (1:ℝ) ≤ (C.absNorm:ℝ) := ideal_norm_one_le hC
  have hd1 : (1:ℝ) ≤ (D.absNorm:ℝ) := ideal_norm_one_le hD
  have hall : (1:ℝ) ≤ Z^(allowance C D Z) := Real.one_le_rpow hZ.le (allowance_nonneg C D Z)
  have hV2 : Z^(-4:ℝ) ≤ (sourceVolume s)^2 := by
    have h1 : Z^(-4:ℝ) = ((Z^(2:ℝ))^2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_neg hz.le]; norm_num
    rw [h1, ← inv_pow]
    have h2 : (Z^(2:ℝ))⁻¹ ≤ sourceVolume s := by
      rw [inv_le_comm₀ (Real.rpow_pos_of_pos hz _) hv]; exact hV
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.rpow_nonneg hz.le _)) h2 2
  have hCD : (C.absNorm:ℝ)*(D.absNorm:ℝ) ≤ Z^(16:ℝ) := by
    calc (C.absNorm:ℝ)*(D.absNorm:ℝ) ≤ Z^(8:ℝ)*Z^(8:ℝ) :=
          mul_le_mul hNC hND (by linarith) (Real.rpow_nonneg hz.le _)
      _ = Z^(16:ℝ) := by rw [← Real.rpow_add hz]; norm_num
  have hcore : Z^(-20:ℝ) ≤ (τ.modulus.absNorm:ℝ)*(sourceVolume s)^2/((C.absNorm:ℝ)*(D.absNorm:ℝ))*
      Z^(allowance C D Z) := by
    have hpos : 0 < (C.absNorm:ℝ)*(D.absNorm:ℝ) := by positivity
    have e : Z^(-20:ℝ) = Z^(-4:ℝ)/Z^(16:ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hz.le, ← Real.rpow_add hz]; norm_num
    rw [e]
    calc Z^(-4:ℝ)/Z^(16:ℝ) ≤ (sourceVolume s)^2/((C.absNorm:ℝ)*(D.absNorm:ℝ)) :=
          div_le_div₀ (sq_nonneg _) hV2 hpos hCD
      _ ≤ (τ.modulus.absNorm:ℝ)*(sourceVolume s)^2/((C.absNorm:ℝ)*(D.absNorm:ℝ)) := by
          rw [mul_div_assoc]; exact le_mul_of_one_le_left (by positivity) hτ
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hall
  unfold balancedBudget
  have e2 : Z^(loss-20) = Z^(-20:ℝ)*Z^loss := by rw [← Real.rpow_add hz]; ring_nf
  rw [e2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcore hA) (Real.rpow_nonneg hz.le _)

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
