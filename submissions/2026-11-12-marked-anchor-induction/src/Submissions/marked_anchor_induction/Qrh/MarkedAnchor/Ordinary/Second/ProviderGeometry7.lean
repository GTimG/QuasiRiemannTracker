/- Copyright (c) 2026 Sil. Apache-2.0.
Provider geometry, part 7: **`GeometryAt` for `rootChoice`** (both sides).

* `slotWidth_eq`: `W_B = 2^{|J|}·Z^u`; `selOf_branch`: the frame-mesh selection `selOf` gives the
  branch hypothesis of `geometryAt_of`.
* `kc_bounds`: for `K = childScale Z κ n₁` of a retained first block (`1/2 ≤ 2^{n₁}`) and
  `K_c = 16·K·W_B⁴`: `1 ≤ K_c` and `K_c·N(C)²·Z ≤ 64·16^{#κ}·V²·N(V₀)·Z^{4u}·Z^{(3/2)κ}`
  from `K·N(C)²·Z ≤ 4·N(V₀)·V²·Z^{(3/2)κ}` (`block_K_left` / `block_K_right`).
* `geometryAt_left`, `geometryAt_right`: the `hgeoL` / `hgeoR` hypotheses of
  `labelHalf_of_rootInput` at `K = childScale Z (cutoffLoss G N ε) n₁`, for every allocation of
  nonzero weight.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry6

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

local instance (priority := 2000) instDecEqSubtypePG7 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

theorem slotWidth_eq (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) J =
      2^(Fintype.card J) * Z^(selW d J) := by
  obtain ⟨-, -, -, -, hP⟩ := d.hcanonical
  unfold slotWidth
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  unfold selW
  rw [← Finset.sum_coe_sort J, Real.rpow_sum_of_pos (zero_lt_one.trans d.one_lt_Z)]
  apply Finset.prod_congr rfl
  intro j _
  change d.root.P j.val.val = _
  rw [hP]

theorem card_sel_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) {C : Id}
    {B : actualAllocations (tuplePools d.root) C} (J : Finset (liveIndices B.val)) :
    Fintype.card J ≤ Fintype.card κ :=
  (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)

/-- **The frame-mesh selection gives the branch hypothesis.** -/
theorem selOf_branch (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (hε : 0 < ε)
    (mesh : ℝ) (hm : 0 ≤ mesh) (hmesh : ∀ i, d.w i ≤ mesh) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) :
    (G.floor ε ≤ liveW d B ∧ D.sel ε (liveW d B) ≤ selW d (selOf d hε mesh hm hmesh C B) ∧
        selW d (selOf d hε mesh hm hmesh C B) ≤ D.sel ε (liveW d B) + mesh) ∨
      (liveW d B ≤ G.floor ε ∧ selW d (selOf d hε mesh hm hmesh C B) = 0) := by
  have hlw : Second.Selection.liveWidth (Finset.univ : Finset (liveIndices B.val))
      (fun i => d.w i.val) = liveW d B := by
    unfold Second.Selection.liveWidth liveW
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv (fun x => by simp)) _ _ (fun x => rfl)
  have hsw : selW d (selOf d hε mesh hm hmesh C B) =
      ∑ j ∈ Second.Selection.chosenSlots (Finset.univ : Finset (liveIndices B.val))
        (fun i => d.w i.val) (D.sel ε) (widthFloor G ε) mesh hm (fun i => d.hw _)
        (fun i => hmesh _) (d.sel_live hε C B Finset.univ), d.w j.val.val := by
    unfold selW selOf
    rw [Finset.sum_map]
    rfl
  by_cases hL : widthFloor G ε < Second.Selection.liveWidth (Finset.univ : Finset (liveIndices B.val))
      (fun i => d.w i.val)
  · left
    obtain ⟨h1, h2, -⟩ := Second.Selection.chosen_large (Finset.univ : Finset (liveIndices B.val))
      (fun i => d.w i.val) (D.sel ε) (widthFloor G ε) mesh hm (fun i => d.hw _) (fun i => hmesh _)
      (d.sel_live hε C B Finset.univ) hL
    rw [hsw, ← hlw]
    exact ⟨hL.le, h1, h2⟩
  · right
    have h0 := Second.Selection.chosen_small (Finset.univ : Finset (liveIndices B.val))
      (fun i => d.w i.val) (D.sel ε) (widthFloor G ε) mesh hm (fun i => d.hw _) (fun i => hmesh _)
      (d.sel_live hε C B Finset.univ) (le_of_not_gt hL)
    rw [hsw, h0, Finset.sum_empty, ← hlw]
    exact ⟨le_of_not_gt hL, rfl⟩

/-- **The second-step Gauss scale `K_c = 16·K·W_B⁴`.** -/
theorem kc_bounds (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (κl : ℝ) (hκ : 0 ≤ κl) (n : ℤ) (hn : 1/2 ≤ dyadicScale n) (NC NV : ℝ) (hNC : 0 ≤ NC)
    (hK : childScale Z κl n * NC^2 * Z ≤ 4 * NV * sourceVolume d.root ^ 2 * Z^((3/2)*κl)) :
    1 ≤ 16 * childScale Z κl n *
        (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) J)^4 ∧
      16 * childScale Z κl n *
          (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) J)^4 * NC^2 * Z ≤
        (64 * 16^(Fintype.card κ)) * sourceVolume d.root ^ 2 * NV * Z^(4 * selW d J) *
          Z^((3/2)*κl) := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  rw [slotWidth_eq d C B J]
  obtain ⟨hu0, -⟩ := selW_le d J
  have hZu : 1 ≤ Z^(selW d J) := Real.one_le_rpow hZ1.le hu0
  have hcs := childScale_eq Z κl hZ1 n
  have hZk : 1 ≤ Z^κl := Real.one_le_rpow hZ1.le hκ
  have hW1 : 1 ≤ (2:ℝ)^(Fintype.card J) * Z^(selW d J) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hZu
  have hW4 : ((2:ℝ)^(Fintype.card J) * Z^(selW d J))^4 ≤ 16^(Fintype.card κ) * Z^(4 * selW d J) := by
    rw [mul_pow, ← pow_mul, show (4:ℝ) * selW d J = selW d J * ((4:ℕ):ℝ) by push_cast; ring,
      Real.rpow_mul_natCast hZ0.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (2:ℝ)^(Fintype.card J * 4) = 16^(Fintype.card J) := by
          rw [mul_comm, pow_mul]; norm_num
      _ ≤ 16^(Fintype.card κ) := pow_le_pow_right₀ (by norm_num) (card_sel_le d J)
  have hK0 : 0 ≤ childScale Z κl n := by rw [hcs]; positivity
  constructor
  · have hK1 : 1/2 ≤ childScale Z κl n := by
      rw [hcs]; nlinarith
    have : 1 ≤ ((2:ℝ)^(Fintype.card J) * Z^(selW d J))^4 := one_le_pow₀ hW1
    nlinarith
  · calc 16 * childScale Z κl n * ((2:ℝ)^(Fintype.card J) * Z^(selW d J))^4 * NC^2 * Z
        = 16 * ((2:ℝ)^(Fintype.card J) * Z^(selW d J))^4 * (childScale Z κl n * NC^2 * Z) := by
          ring
      _ ≤ 16 * (16^(Fintype.card κ) * Z^(4 * selW d J)) *
            (4 * NV * sourceVolume d.root ^ 2 * Z^((3/2)*κl)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hW4 (by norm_num)) hK (by positivity)
            (by positivity)
      _ = _ := by ring

/-- **`hgeoL` of `labelHalf_of_rootInput`: `GeometryAt` on the left side of `rootChoice`.** -/
theorem geometryAt_left (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (hB24 : 24 ≤ Bmask) (mesh : ℝ) (hm : 0 ≤ mesh) (hmesh : ∀ i, d.w i ≤ mesh)
    (hmG : mesh ≤ RootParameters.mesh G ε)
    (C D' : Id) (hC : Supported C) (hD : Supported D') (E : Finset (CommonIndex C D'))
    (hcf : Packet.CubeFreeCommon C D') (hcpC : CenteredMomentCompleteCommon.commonPart C D' = C)
    (hcpD : CenteredMomentCompleteCommon.commonPart D' C = D')
    (h8 : (Ideal.absNorm C : ℝ) ≤ Z^(8:ℝ)) (n : ℤ)
    (hn : n ∈ retainedIndices (firstRadius d.root C D' E d.Kroot Z (cutoffLoss G N ε)))
    (hn1 : 1/2 ≤ dyadicScale n) (ξr cb : ℝ) (hξr : ξr ≤ 2) (hcb : 19 ≤ cb)
    (hZc : 32 * ((9/4:ℝ)^2 * 2^(Fintype.card κ))^2 * Z^(ξr/2) ≤ Z^mesh)
    (hHmin : 2 * cutoffLoss G N ε ≤ 1 - D.Hmin)
    (hZ1 : Real.logb Z (64 * 16^(Fintype.card κ)) ≤ cutoffLoss G N ε / 2)
    (hZ2 : 2 * (Fintype.card κ : ℝ) * Real.logb Z 2 ≤ rootReserve G)
    (hZ3 : Real.logb Z (9/2) ≤ cutoffLoss G N ε)
    (hZ4 : (81/16:ℝ) * 4^(Fintype.card κ) ≤ Z) (ha : (0:ℝ) < 1/4) :
    ∀ B, allocWeight d.root C B ≠ 0 → 1 ≤ capRes d C B (selOf d hε mesh hm hmesh C B) →
      GeometryAt D G ε η (residFin d C B (selOf d hε mesh hm hmesh C B)) ha
      (frameOf d C B (selOf d hε mesh hm hmesh C B) hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask
        hBmask mesh hmesh (Packet.firstPacked C D' hC E) (Packet.firstPacked_ne_zero C D' hC E)
        (Real.logb Z (16 * childScale Z (cutoffLoss G N ε) n *
          (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
          (selOf d hε mesh hm hmesh C B))^4)))
      (16 * childScale Z (cutoffLoss G N ε) n *
        (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
          (selOf d hε mesh hm hmesh C B))^4)
      (frequencyRadius (Tfreq d C B (selOf d hε mesh hm hmesh C B)
        (16 * childScale Z (cutoffLoss G N ε) n *
          (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
          (selOf d hε mesh hm hmesh C B))^4)) Z ξr)
      (capRes d C B (selOf d hε mesh hm hmesh C B))
      (∑ j : selOf d hε mesh hm hmesh C B, d.w j.val.val) cb := by
  intro B hwt hcap
  have hκ := cutoffLoss_small (G := G) (N := N) hε
  have e : (∑ j : selOf d hε mesh hm hmesh C B, d.w j.val.val) =
      selW d (selOf d hε mesh hm hmesh C B) := Finset.sum_coe_sort _ (fun j : liveIndices B.val => d.w j.val)
  rw [e]
  have hKb := block_K_left C D' hC hD E hcf hcpC hcpD d.root d.Kroot Z (cutoffLoss G N ε) d.one_lt_Z
    d.hKlow n hn
  obtain ⟨hKc1, hKup⟩ := kc_bounds d C B (selOf d hε mesh hm hmesh C B) (cutoffLoss G N ε)
    hκ.1.le n hn1 _ _ (Nat.cast_nonneg _) hKb
  have hZ0 : 0 < Z := zero_lt_one.trans d.one_lt_Z
  have hZc' : 32 * ((9/4:ℝ)^2 * 2^(Fintype.card (Rest (selOf d hε mesh hm hmesh C B))))^2 *
      Z^(ξr/2) ≤ Z^mesh := by
    refine le_trans ?_ hZc
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (card_rest_le d _)
  exact geometryAt_of d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask hB24 mesh hmesh hm hmG
    C B (selOf d hε mesh hm hmesh C B) hwt h8 _ _ (packed_le_sq C D' hC E hD hcf hcpC hcpD) _
    (64 * 16^(Fintype.card κ)) ξr cb hKc1 (by positivity) hKup
    (selOf_branch d hε mesh hm hmesh C B) hcap hZc' hξr hcb hHmin hZ1 hZ2 hZ3 hZ4 ha

/-- **`hgeoR` of `labelHalf_of_rootInput`: `GeometryAt` on the right side of `rootChoice`.** -/
theorem geometryAt_right (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (hB24 : 24 ≤ Bmask) (mesh : ℝ) (hm : 0 ≤ mesh) (hmesh : ∀ i, d.w i ≤ mesh)
    (hmG : mesh ≤ RootParameters.mesh G ε)
    (C D' : Id) (hC : Supported C) (hD : Supported D') (E : Finset (CommonIndex C D'))
    (hcf : Packet.CubeFreeCommon C D') (hcpC : CenteredMomentCompleteCommon.commonPart C D' = C)
    (hcpD : CenteredMomentCompleteCommon.commonPart D' C = D')
    (h8 : (Ideal.absNorm D' : ℝ) ≤ Z^(8:ℝ)) (n : ℤ)
    (hn : n ∈ retainedIndices (firstRadius d.root C D' E d.Kroot Z (cutoffLoss G N ε)))
    (hn1 : 1/2 ≤ dyadicScale n) (ξr cb : ℝ) (hξr : ξr ≤ 2) (hcb : 19 ≤ cb)
    (hZc : 32 * ((9/4:ℝ)^2 * 2^(Fintype.card κ))^2 * Z^(ξr/2) ≤ Z^mesh)
    (hHmin : 2 * cutoffLoss G N ε ≤ 1 - D.Hmin)
    (hZ1 : Real.logb Z (64 * 16^(Fintype.card κ)) ≤ cutoffLoss G N ε / 2)
    (hZ2 : 2 * (Fintype.card κ : ℝ) * Real.logb Z 2 ≤ rootReserve G)
    (hZ3 : Real.logb Z (9/2) ≤ cutoffLoss G N ε)
    (hZ4 : (81/16:ℝ) * 4^(Fintype.card κ) ≤ Z) (ha : (0:ℝ) < 1/4) :
    ∀ B, allocWeight d.root D' B ≠ 0 → 1 ≤ capRes d D' B (selOf d hε mesh hm hmesh D' B) →
      GeometryAt D G ε η (residFin d D' B (selOf d hε mesh hm hmesh D' B)) ha
      (frameOf d D' B (selOf d hε mesh hm hmesh D' B) hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask
        hBmask mesh hmesh (Packet.firstPackedRight C D' hC E) (Packet.firstPackedRight_ne_zero C D' hC E)
        (Real.logb Z (16 * childScale Z (cutoffLoss G N ε) n *
          (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
          (selOf d hε mesh hm hmesh D' B))^4)))
      (16 * childScale Z (cutoffLoss G N ε) n *
        (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
          (selOf d hε mesh hm hmesh D' B))^4)
      (frequencyRadius (Tfreq d D' B (selOf d hε mesh hm hmesh D' B)
        (16 * childScale Z (cutoffLoss G N ε) n *
          (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
          (selOf d hε mesh hm hmesh D' B))^4)) Z ξr)
      (capRes d D' B (selOf d hε mesh hm hmesh D' B))
      (∑ j : selOf d hε mesh hm hmesh D' B, d.w j.val.val) cb := by
  intro B hwt hcap
  have hκ := cutoffLoss_small (G := G) (N := N) hε
  have e : (∑ j : selOf d hε mesh hm hmesh D' B, d.w j.val.val) =
      selW d (selOf d hε mesh hm hmesh D' B) := Finset.sum_coe_sort _ (fun j : liveIndices B.val => d.w j.val)
  rw [e]
  have hKb := block_K_right C D' hC hD E hcf hcpC hcpD d.root d.Kroot Z (cutoffLoss G N ε) d.one_lt_Z
    d.hKlow n hn
  obtain ⟨hKc1, hKup⟩ := kc_bounds d D' B (selOf d hε mesh hm hmesh D' B) (cutoffLoss G N ε)
    hκ.1.le n hn1 _ _ (Nat.cast_nonneg _) hKb
  have hZ0 : 0 < Z := zero_lt_one.trans d.one_lt_Z
  have hZc' : 32 * ((9/4:ℝ)^2 * 2^(Fintype.card (Rest (selOf d hε mesh hm hmesh D' B))))^2 *
      Z^(ξr/2) ≤ Z^mesh := by
    refine le_trans ?_ hZc
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (card_rest_le d _)
  exact geometryAt_of d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask hB24 mesh hmesh hm hmG
    D' B (selOf d hε mesh hm hmesh D' B) hwt h8 _ _ (packedRight_le_sq C D' hC E hD hcf hcpC hcpD) _
    (64 * 16^(Fintype.card κ)) ξr cb hKc1 (by positivity) hKup
    (selOf_branch d hε mesh hm hmesh D' B) hcap hZc' hξr hcb hHmin hZ1 hZ2 hZ3 hZ4 ha

/-- The frame Poisson condition of `hdyad_of_freq` at `ξ_r = mesh` holds eventually. -/
theorem eventually_hZc (n : ℕ) (mesh : ℝ) (hm : 0 < mesh) :
    ∀ᶠ Z : ℝ in atTop, 32 * ((9/4:ℝ)^2 * 2^n)^2 * Z^(mesh/2) ≤ Z^mesh := by
  filter_upwards [(tendsto_rpow_atTop (half_pos hm)).eventually_ge_atTop
    (32 * ((9/4:ℝ)^2 * 2^n)^2), eventually_gt_atTop (0:ℝ)] with Z h1 h0
  have e : Z^mesh = Z^(mesh/2) * Z^(mesh/2) := by rw [← Real.rpow_add h0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg h0.le _)

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
