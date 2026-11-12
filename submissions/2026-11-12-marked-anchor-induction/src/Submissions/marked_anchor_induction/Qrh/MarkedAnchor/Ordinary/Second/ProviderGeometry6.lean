/- Copyright (c) 2026 Sil. Apache-2.0.
Provider geometry, part 6: the inputs of `geometryAt_of` for `rootChoice`.

* `packed_le_sq`, `packedRight_le_sq`: `N(V_C) ≤ N(C)²`, `N(V_D) ≤ N(D)²`.
* `block_K_left`, `block_K_right`: the first-step Gauss scale `K = childScale Z κ n₁` of a retained
  first block (`n₁ ∈ retainedIndices (firstRadius …)`) satisfies
  `K·N(C)²·Z ≤ 4·N(V_C)·V²·Z^{(3/2)κ}` (and the same with `D`, `V_D`).
* `slotWidth_eq`: `W_B = 2^{|J|}·Z^u`.
* `selOf_branch`: the selection `selOf` (frame mesh) gives the branch hypothesis.
* `geometryAt_left`, `geometryAt_right`: **`GeometryAt` for `rootChoice`** on both sides, in the
  exact form of `labelHalf_of_rootInput`'s `hgeoL`/`hgeoR`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry5
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderChoice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentNaturalFixedRaySource CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstScale CenteredMomentFirstPhysicalDyadicAssembly
open QRH.SilDensitySplit.CubeFree Qrh.MarkedAnchor.Ordinary QRH.SilDensitySplit.CubeFree.Second Qrh.MarkedAnchor.Ordinary.Second
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedCompletedRows MixedInnerExceptionalBlock
open MixedFirstRetainedFixed MixedFirstExceptionalWindow
open RepairedRawContext
open Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypePG6 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-! ### The packed twists -/

section packed
variable (C D : Id) (hC : Supported C) (E : Finset (CommonIndex C D))

theorem psg_dvd_left :
    Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} ∣
      CenteredMomentCompleteCommon.commonPart C D := by
  rw [show Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} =
      ∏ P ∈ E, P.val from ConcretePrimeRowBridge.span_idealGenerator _, commonPart_left_product]
  calc (∏ P ∈ E, P.val) ∣ ∏ P : CommonIndex C D, P.val :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    _ ∣ ∏ P : CommonIndex C D, P.val ^ leftExponent C D P :=
        Finset.prod_dvd_prod_of_dvd _ _ (fun P _ => dvd_pow_self _ (leftExponent_pos C D P).ne')

theorem act_dvd_right :
    Ideal.span {activeConductor C D} ∣ CenteredMomentCompleteCommon.commonPart D C := by
  unfold activeConductor
  rw [ActualEisensteinCubic.span_finitePrimeModulus, commonPart_right_product]
  calc (∏ i : ActiveIndex C D, activePrime C D i)
      = ∏ P ∈ CenteredMomentActive.activeSupport (Finset.univ : Finset (CommonIndex C D))
          (leftExponent C D) (rightExponent C D), P.val :=
        Finset.prod_coe_sort _ (fun P : CommonIndex C D => P.val)
    _ ∣ ∏ P : CommonIndex C D, P.val :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    _ ∣ ∏ P : CommonIndex C D, P.val ^ rightExponent C D P :=
        Finset.prod_dvd_prod_of_dvd _ _ (fun P _ => dvd_pow_self _ (rightExponent_pos C D P).ne')

theorem act_dvd_left :
    Ideal.span {activeConductor C D} ∣ CenteredMomentCompleteCommon.commonPart C D := by
  unfold activeConductor
  rw [ActualEisensteinCubic.span_finitePrimeModulus, commonPart_left_product]
  calc (∏ i : ActiveIndex C D, activePrime C D i)
      = ∏ P ∈ CenteredMomentActive.activeSupport (Finset.univ : Finset (CommonIndex C D))
          (leftExponent C D) (rightExponent C D), P.val :=
        Finset.prod_coe_sort _ (fun P : CommonIndex C D => P.val)
    _ ∣ ∏ P : CommonIndex C D, P.val :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    _ ∣ ∏ P : CommonIndex C D, P.val ^ leftExponent C D P :=
        Finset.prod_dvd_prod_of_dvd _ _ (fun P _ => dvd_pow_self _ (leftExponent_pos C D P).ne')

theorem psg_dvd_right :
    Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} ∣
      CenteredMomentCompleteCommon.commonPart D C := by
  rw [show Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} =
      ∏ P ∈ E, P.val from ConcretePrimeRowBridge.span_idealGenerator _, commonPart_right_product]
  calc (∏ P ∈ E, P.val) ∣ ∏ P : CommonIndex C D, P.val :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    _ ∣ ∏ P : CommonIndex C D, P.val ^ rightExponent C D P :=
        Finset.prod_dvd_prod_of_dvd _ _ (fun P _ => dvd_pow_self _ (rightExponent_pos C D P).ne')

variable (hD : Supported D) (hcf : Packet.CubeFreeCommon C D)
  (hcpC : CenteredMomentCompleteCommon.commonPart C D = C)
  (hcpD : CenteredMomentCompleteCommon.commonPart D C = D)
include hD hcf hcpC hcpD

omit hD in
/-- The packing identity in real form: `N(V_C)·N(D) = N(E)·N(act)·N(C)`. -/
theorem packed_eq :
    ((Ideal.span {Packet.firstPacked C D hC E}).absNorm : ℝ) * (Ideal.absNorm D : ℝ) =
      ((Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}).absNorm : ℝ) *
        ((Ideal.span {activeConductor C D}).absNorm : ℝ) * (Ideal.absNorm C : ℝ) := by
  have h := Packet.firstPacked_norm C D hC E hcf
  rw [hcpC, hcpD] at h
  exact_mod_cast h

omit hD in
theorem packedRight_eq :
    ((Ideal.span {Packet.firstPackedRight C D hC E}).absNorm : ℝ) * (Ideal.absNorm C : ℝ) =
      ((Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}).absNorm : ℝ) *
        ((Ideal.span {activeConductor C D}).absNorm : ℝ) * (Ideal.absNorm D : ℝ) := by
  have h := Packet.firstPackedRight_norm C D hC E hcf
  rw [hcpC, hcpD] at h
  exact_mod_cast h

theorem packed_le_sq :
    ((Ideal.span {Packet.firstPacked C D hC E}).absNorm : ℝ) ≤ (Ideal.absNorm C : ℝ)^2 := by
  have h := packed_eq C D hC E hcf hcpC hcpD
  have hE := absNorm_le_of_dvd (psg_dvd_left C D E) (by rw [hcpC]; exact hC.1)
  have hA := absNorm_le_of_dvd (act_dvd_right C D) (by rw [hcpD]; exact hD.1)
  rw [hcpC] at hE; rw [hcpD] at hA
  have hD0 : (0:ℝ) < Ideal.absNorm D := by have := one_le_absNorm hD.1; linarith
  have hC0 : (0:ℝ) ≤ Ideal.absNorm C := Nat.cast_nonneg _
  have : ((Ideal.span {Packet.firstPacked C D hC E}).absNorm : ℝ) * (Ideal.absNorm D : ℝ) ≤
      (Ideal.absNorm C : ℝ)^2 * (Ideal.absNorm D : ℝ) := by
    rw [h, sq]
    calc ((Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}).absNorm : ℝ) *
          ((Ideal.span {activeConductor C D}).absNorm : ℝ) * (Ideal.absNorm C : ℝ)
        ≤ (Ideal.absNorm C : ℝ) * (Ideal.absNorm D : ℝ) * (Ideal.absNorm C : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hE hA (Nat.cast_nonneg _) hC0) hC0
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hD0

theorem packedRight_le_sq :
    ((Ideal.span {Packet.firstPackedRight C D hC E}).absNorm : ℝ) ≤ (Ideal.absNorm D : ℝ)^2 := by
  have h := packedRight_eq C D hC E hcf hcpC hcpD
  have hE := absNorm_le_of_dvd (psg_dvd_right C D E) (by rw [hcpD]; exact hD.1)
  have hA := absNorm_le_of_dvd (act_dvd_left C D) (by rw [hcpC]; exact hC.1)
  rw [hcpD] at hE; rw [hcpC] at hA
  have hC0 : (0:ℝ) < Ideal.absNorm C := by have := one_le_absNorm hC.1; linarith
  have hD0 : (0:ℝ) ≤ Ideal.absNorm D := Nat.cast_nonneg _
  have : ((Ideal.span {Packet.firstPackedRight C D hC E}).absNorm : ℝ) * (Ideal.absNorm C : ℝ) ≤
      (Ideal.absNorm D : ℝ)^2 * (Ideal.absNorm C : ℝ) := by
    rw [h, sq]
    calc ((Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}).absNorm : ℝ) *
          ((Ideal.span {activeConductor C D}).absNorm : ℝ) * (Ideal.absNorm D : ℝ)
        ≤ (Ideal.absNorm D : ℝ) * (Ideal.absNorm C : ℝ) * (Ideal.absNorm D : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hE hA (Nat.cast_nonneg _) hD0) hD0
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hC0

end packed

/-! ### The first-step Gauss scale of a retained block -/

section block
variable {ι : Type*} [Fintype ι] {a b : ℝ}

theorem childScale_eq (Z κl : ℝ) (hZ : 1 < Z) (n : ℤ) :
    childScale Z κl n = dyadicScale n * Z^κl := by
  have hZ0 : 0 < Z := by linarith
  unfold childScale
  rw [Real.rpow_add hZ0, Real.rpow_logb hZ0 hZ.ne' (dyadicScale_pos n)]

theorem K_le_radius (s : Source ι a b) (C D : Id) (E : Finset (CommonIndex C D)) (Kr Z κl : ℝ)
    (hZ : 1 < Z) (n : ℤ) (hn : n ∈ retainedIndices (firstRadius s C D E Kr Z κl)) :
    childScale Z κl n ≤
      4 * firstNominalScale C D (∏ P ∈ E, P.val) Kr (sourceVolume s) * Z^((3/2)*κl) := by
  have hZ0 : 0 < Z := by linarith
  have hds := retained_scale_le _ n ((mem_retainedIndices _ n).mp hn).1
  unfold firstRadius frequencyRadius at hds
  rw [childScale_eq Z κl hZ n]
  have e : Z^((3/2)*κl) = Z^(κl/2) * Z^κl := by rw [← Real.rpow_add hZ0]; ring_nf
  rw [e]
  have hZk := Real.rpow_pos_of_pos hZ0 κl
  calc dyadicScale n * Z^κl
      ≤ (4 * (firstNominalScale C D (∏ P ∈ E, P.val) Kr (sourceVolume s) * Z^(κl/2))) * Z^κl :=
        mul_le_mul_of_nonneg_right hds hZk.le
    _ = _ := by ring

variable (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
  (hcf : Packet.CubeFreeCommon C D)
  (hcpC : CenteredMomentCompleteCommon.commonPart C D = C)
  (hcpD : CenteredMomentCompleteCommon.commonPart D C = D)

theorem normE_eq :
    (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) =
      ((Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P : CommonIndex C D => P.val) E}).absNorm : ℝ) := by
  rw [show Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} =
      ∏ P ∈ E, P.val from ConcretePrimeRowBridge.span_idealGenerator _]

include hC hD hcf hcpC hcpD in
/-- **Left side**: `K·N(C)²·Z ≤ 4·N(V_C)·V²·Z^{(3/2)κ}`. -/
theorem block_K_left (s : Source ι a b) (Kr Z κl : ℝ) (hZ : 1 < Z) (hKr : Z ≤ Kr) (n : ℤ)
    (hn : n ∈ retainedIndices (firstRadius s C D E Kr Z κl)) :
    childScale Z κl n * (Ideal.absNorm C : ℝ)^2 * Z ≤
      4 * ((Ideal.span {Packet.firstPacked C D hC E}).absNorm : ℝ) * sourceVolume s ^ 2 *
        Z^((3/2)*κl) := by
  have hZ0 : 0 < Z := by linarith
  have hK := K_le_radius s C D E Kr Z κl hZ n hn
  have hp := packed_eq C D hC E hcf hcpC hcpD
  have hC0 : (0:ℝ) < Ideal.absNorm C := by have := one_le_absNorm hC.1; linarith
  have hD0 : (0:ℝ) < Ideal.absNorm D := by have := one_le_absNorm hD.1; linarith
  have hKr0 : 0 < Kr := by linarith
  have hnom : firstNominalScale C D (∏ P ∈ E, P.val) Kr (sourceVolume s) * Kr *
      (Ideal.absNorm C : ℝ)^2 =
      ((Ideal.span {Packet.firstPacked C D hC E}).absNorm : ℝ) * sourceVolume s ^ 2 := by
    unfold firstNominalScale
    rw [hcpC, hcpD, normE_eq C D E]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    linear_combination (-(sourceVolume s ^ 2 * Kr * (Ideal.absNorm C : ℝ))) * hp
  have hcs0 : 0 ≤ childScale Z κl n := by
    rw [childScale_eq Z κl hZ n]; exact mul_nonneg (dyadicScale_pos n).le (Real.rpow_nonneg hZ0.le _)
  have hZk := Real.rpow_nonneg hZ0.le ((3/2)*κl)
  calc childScale Z κl n * (Ideal.absNorm C : ℝ)^2 * Z
      ≤ childScale Z κl n * (Ideal.absNorm C : ℝ)^2 * Kr :=
        mul_le_mul_of_nonneg_left hKr (by positivity)
    _ ≤ (4 * firstNominalScale C D (∏ P ∈ E, P.val) Kr (sourceVolume s) * Z^((3/2)*κl)) *
          (Ideal.absNorm C : ℝ)^2 * Kr :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) hKr0.le
    _ = 4 * (firstNominalScale C D (∏ P ∈ E, P.val) Kr (sourceVolume s) * Kr *
          (Ideal.absNorm C : ℝ)^2) * Z^((3/2)*κl) := by ring
    _ = _ := by rw [hnom]; ring

include hC hD hcf hcpC hcpD in
/-- **Right side**: `K·N(D)²·Z ≤ 4·N(V_D)·V²·Z^{(3/2)κ}`. -/
theorem block_K_right (s : Source ι a b) (Kr Z κl : ℝ) (hZ : 1 < Z) (hKr : Z ≤ Kr) (n : ℤ)
    (hn : n ∈ retainedIndices (firstRadius s C D E Kr Z κl)) :
    childScale Z κl n * (Ideal.absNorm D : ℝ)^2 * Z ≤
      4 * ((Ideal.span {Packet.firstPackedRight C D hC E}).absNorm : ℝ) * sourceVolume s ^ 2 *
        Z^((3/2)*κl) := by
  have hZ0 : 0 < Z := by linarith
  have hK := K_le_radius s C D E Kr Z κl hZ n hn
  have hp := packedRight_eq C D hC E hcf hcpC hcpD
  have hC0 : (0:ℝ) < Ideal.absNorm C := by have := one_le_absNorm hC.1; linarith
  have hD0 : (0:ℝ) < Ideal.absNorm D := by have := one_le_absNorm hD.1; linarith
  have hKr0 : 0 < Kr := by linarith
  have hnom : firstNominalScale C D (∏ P ∈ E, P.val) Kr (sourceVolume s) * Kr *
      (Ideal.absNorm D : ℝ)^2 =
      ((Ideal.span {Packet.firstPackedRight C D hC E}).absNorm : ℝ) * sourceVolume s ^ 2 := by
    unfold firstNominalScale
    rw [hcpC, hcpD, normE_eq C D E]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    linear_combination (-(sourceVolume s ^ 2 * Kr * (Ideal.absNorm D : ℝ))) * hp
  have hcs0 : 0 ≤ childScale Z κl n := by
    rw [childScale_eq Z κl hZ n]; exact mul_nonneg (dyadicScale_pos n).le (Real.rpow_nonneg hZ0.le _)
  have hZk := Real.rpow_nonneg hZ0.le ((3/2)*κl)
  calc childScale Z κl n * (Ideal.absNorm D : ℝ)^2 * Z
      ≤ childScale Z κl n * (Ideal.absNorm D : ℝ)^2 * Kr :=
        mul_le_mul_of_nonneg_left hKr (by positivity)
    _ ≤ (4 * firstNominalScale C D (∏ P ∈ E, P.val) Kr (sourceVolume s) * Z^((3/2)*κl)) *
          (Ideal.absNorm D : ℝ)^2 * Kr :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) hKr0.le
    _ = 4 * (firstNominalScale C D (∏ P ∈ E, P.val) Kr (sourceVolume s) * Kr *
          (Ideal.absNorm D : ℝ)^2) * Z^((3/2)*κl) := by ring
    _ = _ := by rw [hnom]; ring

end block

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
