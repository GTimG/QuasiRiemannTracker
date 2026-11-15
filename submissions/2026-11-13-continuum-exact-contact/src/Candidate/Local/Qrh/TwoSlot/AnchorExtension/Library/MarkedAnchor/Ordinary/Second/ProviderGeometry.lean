/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider geometry (label half): the scalar reductions of the side geometry of a
renormalized residual, and the `GeometryHalf` interface.

* `defect_lower` / `defect_upper`: with `A − c := colLog + u`, `q_C := twistLog`, the frequency
  defect `t := commonH − 1 + 6u` (so that `g.H = commonH rs`) satisfies
  `t ≥ mesh − (2δ₁ + δ₂)` and `t ≤ 1 + 6u + (2·(lv − 1) + 2δ₃ + mesh)`, from
  - the residual volume `lv − c − u − δ₁ ≤ colLog ≤ lv − c − u + δ₃` (`lv = log_Z V_root`,
    `c = log_Z N C`),
  - the Gauss scale `0 ≤ kLog ≤ (e + act + 2lv − k_root − c − d) + 4u + δ₂`, `1 ≤ k_root`
    (`K ≤ 4·firstRadius·Z^κ`, `firstRadius = firstNominalScale·Z^{κ/2}`, `W_B⁴ ≤ 16^N Z^{4u}`),
  - the packed twist `twistLog = e + act + c − d` (`firstPacked_norm`) and `e ≤ c`, `act ≤ d`.
  Here `δ₂ ≥ (3/2)κ` with `κ = cutoffLoss G N ε` FIXED (not `o(1)`).
* `hroot_of_lengths`: with root lengths `≥ 1`, `gP(renorm rest) ≤ log_Z T`, so the side
  geometry with `PC := gP`, `cg := f + (log_Z T − gP)` satisfies `hroot` from the root face.
* `GeometryHalf`: the per-block geometry data consumed by `split_label_bound_final`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly12
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderResidual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree Qrh.MarkedAnchor.Ordinary QRH.SilDensitySplit.CubeFree.Second Qrh.MarkedAnchor.Ordinary.Second
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP MixedPrincipalPair MixedPrincipalWindow

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-! ### The frequency defect -/

/-- **Lower end of the defect** (`t ≥ −tl`, CF `K ≤ K₀ + o(1)`). -/
theorem defect_lower (colLog kLog twistLog mesh u lv c d e act kr δ₁ δ₂ : ℝ)
    (hcol : lv - c - u - δ₁ ≤ colLog)
    (hk : kLog ≤ (e + act + 2*lv - kr - c - d) + 4*u + δ₂) (hkr : 1 ≤ kr)
    (htw : twistLog = e + act + c - d) :
    mesh - (2*δ₁ + δ₂) ≤ (2*colLog - kLog + mesh + twistLog) - 1 + 6*u := by
  rw [htw]; linarith

/-- **Upper end of the defect** (`t ≤ 1 + 6u + tl`). -/
theorem defect_upper (colLog kLog twistLog mesh u lv c d e act δ₃ : ℝ)
    (hcol : colLog ≤ lv - c - u + δ₃) (hk : 0 ≤ kLog) (hu : 0 ≤ u)
    (htw : twistLog = e + act + c - d) (he : e ≤ c) (hact : act ≤ d) :
    (2*colLog - kLog + mesh + twistLog) - 1 + 6*u ≤ 1 + 6*u + (2*(lv - 1) + 2*δ₃ + mesh) := by
  rw [htw]; linarith

/-- The defect window of the side geometry from the two ends. -/
theorem defect_window (H u mesh tl lo hi : ℝ) (hlo : lo ≤ H - 1 + 6*u) (hhi : H - 1 + 6*u ≤ 1 + 6*u + hi)
    (htl1 : -tl ≤ lo) (htl2 : hi ≤ tl) :
    -tl ≤ H - 1 + 6*u ∧ H - 1 + 6*u ≤ 1 + 6*u + tl := ⟨htl1.trans hlo, hhi.trans (by linarith)⟩

/-- `g.H = commonH` for the defect `t := commonH − 1 + 6u`. -/
theorem H_of_defect (H u : ℝ) : 1 + (H - 1 + 6*u) - 6*u = H := by ring

/-! ### The root face at the side -/

theorem length_div_le (Z X N : ℝ) (hZ : 1 < Z) (hN : 1 ≤ N) (hX : 0 < X) :
    length Z (X / N) ≤ length Z X := by
  unfold length
  apply Real.logb_le_logb_of_le hZ (lt_of_lt_of_le one_pos (le_max_left _ _))
  apply max_le_max le_rfl
  exact div_le_self hX.le hN

theorem length_eq_logb (Z X : ℝ) (hX : 1 ≤ X) : length Z X = Real.logb Z X := by
  unfold length; rw [max_eq_right hX]

/-- **The side ordinary width is below the root ordinary width** when the root lengths are
`≥ 1`: `gP ≤ log_Z T` for the renormalized lengths `Xᵢ/N(dᵢ)`, `Yᵢ/N(dᵢ)`. -/
theorem gP_le_root (Z X₁ X₂ Y₁ Y₂ N₁ N₂ T : ℝ) (hZ : 1 < Z) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hX₁ : 1 ≤ X₁) (hX₂ : 1 ≤ X₂) (hY₁ : 1 ≤ Y₁) (hY₂ : 1 ≤ Y₂) (hXT : X₁ * X₂ = T)
    (hYT : Y₁ * Y₂ = T) :
    max (length Z (X₁/N₁) + length Z (X₂/N₂)) (length Z (Y₁/N₁) + length Z (Y₂/N₂)) ≤
      Real.logb Z T := by
  have h1 := length_div_le Z X₁ N₁ hZ hN₁ (by linarith)
  have h2 := length_div_le Z X₂ N₂ hZ hN₂ (by linarith)
  have h3 := length_div_le Z Y₁ N₁ hZ hN₁ (by linarith)
  have h4 := length_div_le Z Y₂ N₂ hZ hN₂ (by linarith)
  rw [length_eq_logb Z X₁ hX₁] at h1
  rw [length_eq_logb Z X₂ hX₂] at h2
  rw [length_eq_logb Z Y₁ hY₁] at h3
  rw [length_eq_logb Z Y₂ hY₂] at h4
  have eX : Real.logb Z T = Real.logb Z X₁ + Real.logb Z X₂ := by
    rw [← hXT, Real.logb_mul (by positivity) (by positivity)]
  have eY : Real.logb Z T = Real.logb Z Y₁ + Real.logb Z Y₂ := by
    rw [← hYT, Real.logb_mul (by positivity) (by positivity)]
  exact max_le (by linarith) (by linarith)

/-- **`hroot` of the side geometry** from the root face, with `PC := gP`,
`cg := f + (log_Z T − gP)`. -/
theorem hroot_of_face (D : StepData) (P S f gP : ℝ) (hface : P + D.L*S ≤ D.B) (hgP : gP ≤ P) :
    gP + ((f + (P - gP)) - f) + D.L*S ≤ D.B ∧ f ≤ f + (P - gP) := by
  constructor <;> linarith

/-! ### The geometry half -/

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- **`GeometryHalf`** (per block side and selected allocation): the data that
`split_label_bound_final` consumes besides the Seam A leaves. The provider supplies one per
`(B, ξ)` and side `P` (`SidePack.left F` / `SidePack.right F`). -/
def GeometryHalf (D : StepData) (G : StepGates D) (η : Character) (ε cb : ℝ) (P : SidePack η)
    (Q : Id) (m : O) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z)
    (Kc R H : ℝ) (M : ℤ) (Mm : ℕ) (clow A c qC : ℝ) : Prop :=
  RootLabelData P Q m s ha rs Kc R H M Mm clow ∧
  (0 ≤ M ∧ (M:ℝ) ≤ cb * Real.logb 2 Z + 2) ∧ (Mm : ℝ) ≤ Z^(ε/2) ∧
  BranchData D G (gFrame L θ mesh η Z) ε mesh rs A c qC (commonH rs) ∧
  (D.Hmin ≤ commonH rs ∧ commonH rs ≤ D.Hmax)

/-! ### δ₁: the residual volume lower bound -/

section volume
open QRH.SilDensitySplit.CubeFree.Second.Provider Qrh.MarkedAnchor.Ordinary.Second.Provider QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentCommonProfile
local instance (priority := 2000) instDecEqSumPG {κ : Type*} : DecidableEq (κ ⊕ Fin 2) :=
  Classical.decEq _

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- A nonzero allocation weight forces every frozen slot prime into its window: `P_i ≤ N(B_i)`. -/
theorem frozen_ge_of_weight (s : Source ι a b) (G : Id) (B : actualAllocations (tuplePools s) G)
    (hw : allocWeight s G B ≠ 0) :
    ∀ i, B.val (Sum.inl i) ≠ 1 → s.P i ≤ (Ideal.absNorm (B.val (Sum.inl i)) : ℝ) := by
  intro i hi
  unfold allocWeight frozenCoefficient at hw
  have h1 := right_ne_zero_of_mul hw
  have h2 := left_ne_zero_of_mul h1
  have h3 := Finset.prod_ne_zero_iff.mp h2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have h4 := right_ne_zero_of_mul h3
  have h5 := (s.hW i h4).1
  have hP : 0 < s.P i := lt_of_lt_of_le one_pos (s.hP i)
  rwa [le_div_iff₀ hP, one_mul] at h5

/-- **δ₁**: on a live allocation the extracted live volume is at least the root volume over the
first common factor (and the root prefix norms). -/
theorem live_volume_ge (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G)
    (hfro : ∀ i, B.val (Sum.inl i) ≠ 1 → s.P i ≤ (Ideal.absNorm (B.val (Sum.inl i)) : ℝ)) :
    sourceVolume s ≤ (nrm s.d.1 * nrm s.d.2) *
      (sourceVolume (renorm (allocatedLiveSource s hb cover G B)) * (Ideal.absNorm G : ℝ)) := by
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  set r := allocatedLiveSource s hb cover G B
  rw [sourceVolume_renorm, alloc_common_norm s G B]
  have hn1 : nrm r.d.1 = nrm s.d.1 * nrm (B.val (Sum.inr 0)) := by
    change nrm (s.d.1 * B.val (Sum.inr 0)) = _; rw [nrm_mul]
  have hn2 : nrm r.d.2 = nrm s.d.2 * nrm (B.val (Sum.inr 1)) := by
    change nrm (s.d.2 * B.val (Sum.inr 1)) = _; rw [nrm_mul]
  have hs1 := nrm_pos s.hd.1
  have hs2 := nrm_pos s.hd.2
  have hb1 := nrm_pos (hB (Sum.inr 0))
  have hb2 := nrm_pos (hB (Sum.inr 1))
  have hplain : plainNorm B.val = nrm (B.val (Sum.inr 0)) * nrm (B.val (Sum.inr 1)) := rfl
  have hvolr : sourceVolume r = s.X₁ * s.X₂ * ∏ i ∈ liveIndices B.val, s.P i := by
    unfold sourceVolume
    change s.X₁ * s.X₂ * (∏ i : liveIndices B.val, s.P i.val) = _
    rw [Finset.prod_coe_sort (liveIndices B.val) s.P]
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => B.val (Sum.inl i) = 1) s.P
  have hlive_eq : liveIndices B.val = Finset.univ.filter (fun i => B.val (Sum.inl i) = 1) := rfl
  have hfroz : (∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1), s.P i) ≤
      ∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B.val (Sum.inl i) = 1)
      (fun i => (Ideal.absNorm (B.val (Sum.inl i)) : ℝ))]
    have h1 : (∏ i ∈ Finset.univ.filter (fun i => B.val (Sum.inl i) = 1),
        (Ideal.absNorm (B.val (Sum.inl i)) : ℝ)) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]; simp
    rw [h1, one_mul]
    apply Finset.prod_le_prod₀ (fun i _ => le_trans zero_le_one (s.hP i))
    intro i hi
    exact hfro i (Finset.mem_filter.mp hi).2
  have hV : sourceVolume s = s.X₁ * s.X₂ * ((∏ i ∈ liveIndices B.val, s.P i) *
      ∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1), s.P i) := by
    unfold sourceVolume; rw [hlive_eq, hsplit]
  rw [hV, hvolr, hn1, hn2, hplain]
  have hX : 0 < s.X₁ * s.X₂ := mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
  have hlive0 : 0 ≤ ∏ i ∈ liveIndices B.val, s.P i :=
    Finset.prod_nonneg fun i _ => le_trans zero_le_one (s.hP i)
  have hden : (nrm s.d.1 * nrm (B.val (Sum.inr 0)) * (nrm s.d.2 * nrm (B.val (Sum.inr 1)))) ≠ 0 := by
    positivity
  have e : nrm s.d.1 * nrm s.d.2 *
      (s.X₁ * s.X₂ * (∏ i ∈ liveIndices B.val, s.P i) /
        (nrm s.d.1 * nrm (B.val (Sum.inr 0)) * (nrm s.d.2 * nrm (B.val (Sum.inr 1)))) *
        (nrm (B.val (Sum.inr 0)) * nrm (B.val (Sum.inr 1)) *
          ∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ))) =
      s.X₁ * s.X₂ * (∏ i ∈ liveIndices B.val, s.P i) * ∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ) := by
    field_simp
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left hfroz (by positivity)

end volume

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
