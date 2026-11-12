/- Copyright (c) 2026 Sil. Apache-2.0.
Provider: the label half of a block from the root input.

* `rootAmp`, `gAmp_frame`: the frame amplitude of every residual split is the root amplitude.
* `side_label_bound`: one side, every allocation, every height: the split label part is at most
  `(C_max/c_low·A_root·Z^{2ε})·V(renorm rest_B)²·∏_{J_B}P·N(V₀)·(1+|t|)^{2J}`, from
  the split bound (`SplitBoundAt` for every residual slot count), `GeometryAt` for every
  allocation with `capRes ≥ 1` (the others have no label part), and subpower multiplicities.
* `labelHalf_of_rootInput`: both sides and `labelHalf_of_split` give `LabelHalf` of the block.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderChoice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second QRH.SilDensitySplit.CubeFree.Second.Provider
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentNaturalFixedRaySource CenteredMomentSectorLocalization
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open RepairedRawContext Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open RayFourExpansion CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderLR {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

/-- The root amplitude (the frame amplitude of every residual split). -/
def rootAmp (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (J : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  (sourceControl S d.root.W₁ * sourceControl S d.root.W₂)^2 *
    (1 + |d.t₀| + d.V + |d.root.t₁ / (2 * Real.pi)| + |d.root.t₂ / (2 * Real.pi)|)^J

theorem gAmp_frame (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (V₀ : O) (hV₀ : V₀ ≠ 0) (kLog : ℝ) (Jd : ℕ) (S : Finset (ℕ × ℕ)) :
    gAmp 3 (thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM hQ0 hQt hQ72 Holes N ε hε Bmask hBmask
        (Fintype.card (Rest J))) mesh η Z
      (frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh V₀ hV₀ kLog) Jd S =
      rootAmp d Jd S := rfl

/-- **One side: the split label part of every allocation.** -/
theorem side_label_bound (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh) (C : Id)
    (JB : (B : actualAllocations (tuplePools d.root) C) → Finset (liveIndices B.val))
    (P : SidePack η) (hPC : P.Cs ∣ C) (K : ℝ) (hK : 0 < K)
    (T Wd : actualAllocations (tuplePools d.root) C → ℝ) (hWd : ∀ B, 0 < Wd B) (ξr cb : ℝ)
    (Jf : ℕ → ℕ) (ctl : ℕ → Finset (ℕ × ℕ)) (Cf : ℕ → ℝ) (Jd : ℕ) (ctl' : Finset (ℕ × ℕ))
    (Cmax : ℝ) (hJf : ∀ n, n ≤ Fintype.card κ → Jf n ≤ Jd) (hctl : ∀ n, n ≤ Fintype.card κ → ctl n ⊆ ctl') (hCf : ∀ n, n ≤ Fintype.card κ → 0 ≤ Cf n ∧ Cf n ≤ Cmax)
    (hfin : ∀ n, n ≤ Fintype.card κ → SplitBoundAt D G (thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM hQ0 hQt hQ72 Holes N ε
      hε Bmask hBmask n) mesh η Z ε cb (Jf n) (ctl n) (Cf n))
    (ha : (0:ℝ) < 1/4)
    (hgeo : ∀ B, allocWeight d.root C B ≠ 0 → 1 ≤ capRes d C B (JB B) → GeometryAt D G ε η (residFin d C B (JB B)) ha
      (frameOf d C B (JB B) hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh P.V P.hV
        (Real.logb Z (16 * K * Wd B^4)))
      (16 * K * Wd B^4) (frequencyRadius (T B) Z ξr) (capRes d C B (JB B))
      (∑ j : JB B, d.w j.val.val) cb)
    (Cδ δ : ℝ)
    (hms : ∀ (S : Finset Id) (side : Bool),
      (∀ l : Lab S, l.1.val.1 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1, P)^2 ∧
        l.1.val.2 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2, P)^2) →
      (∀ l : Lab S, (l.1.val.1.absNorm : ℝ) ≤ Z^((2:ℝ)*4) ∧ (l.1.val.2.absNorm : ℝ) ≤ Z^((2:ℝ)*4)) →
      ∀ (G' : Id) (A : O),
        (((Finset.univ : Finset (Lab S)).filter (fun l =>
          (if side then l.1.val.1 else l.1.val.2) = G' ∧ lA S l = A)).card : ℝ) ≤ Cδ * Z^δ)
    (hMm : ((⌈Cδ * Z^δ⌉₊ : ℕ) : ℝ) ≤ Z^(ε/2)) :
    ∀ B ξ (t : ℝ), allocWeight d.root C B ≠ 0 →
      labelAvgT d.root ha (by norm_num) d.cover C JB P.base 1 (internalQ Q η₀)
        CenteredMomentSecondHeightFamily.fixedBadMask t K T Z ξr Wd B ξ ≤
      (Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε)) *
        sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B (JB B)))^2 *
        (∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
        ((Ideal.span {P.V}).absNorm : ℝ) * (1 + ‖t‖)^(2*Jd) := by
  intro B ξ t hwB
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hCmax : 0 ≤ Cmax := (hCf 0 (Nat.zero_le _)).1.trans (hCf 0 (Nat.zero_le _)).2
  have hAmp0 : 0 ≤ rootAmp d Jd ctl' := by
    unfold rootAmp
    have := sourceControl_nonneg ctl' d.root.W₁
    have := sourceControl_nonneg ctl' d.root.W₂
    have hV := d.hV
    positivity
  have hT1 : (1:ℝ) ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hrest : 0 ≤ (Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε)) *
      sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B (JB B)))^2 *
      (∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
      ((Ideal.span {P.V}).absNorm : ℝ) * (1 + ‖t‖)^(2*Jd) := by
    have hp := alloc_P_ge d.root (by norm_num) d.cover C JB B
    have := Real.rpow_nonneg hZ0.le (2*ε)
    have : (0:ℝ) ≤ ((Ideal.span {P.V}).absNorm : ℝ) := Nat.cast_nonneg _
    have : (0:ℝ) ≤ ∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val := by
      linarith
    positivity
  by_cases hcap : 1 ≤ capRes d C B (JB B)
  · -- the multiplicities
    have hcube := fun l => lab_cube_rad (residFin d C B (JB B)) ha l
    have hnorm : ∀ l : Lab (S0 (residFin d C B (JB B)) ha),
        (l.1.val.1.absNorm : ℝ) ≤ Z^((2:ℝ)*4) ∧ (l.1.val.2.absNorm : ℝ) ≤ Z^((2:ℝ)*4) := by
      intro l
      have h := lab_norm_le (residFin d C B (JB B)) ha (Z^(8:ℝ)) (residFin_pool_le d C B (JB B)) l
      rw [show ((2:ℝ)*4) = 8 by norm_num]
      exact h
    have hmC : ∀ (G' : Id) (A : O), ((Finset.univ : Finset (Lab (S0 (residFin d C B (JB B)) ha))).filter
        (fun l => l.1.val.1 = G' ∧ lA (S0 (residFin d C B (JB B)) ha) l = A)).card ≤ ⌈Cδ * Z^δ⌉₊ := by
      intro G' A
      have h := hms _ true hcube hnorm G' A
      simp only [ite_true] at h
      exact_mod_cast h.trans (Nat.le_ceil _)
    have hmD : ∀ (G' : Id) (A : O), ((Finset.univ : Finset (Lab (S0 (residFin d C B (JB B)) ha))).filter
        (fun l => l.1.val.2 = G' ∧ lA (S0 (residFin d C B (JB B)) ha) l = A)).card ≤ ⌈Cδ * Z^δ⌉₊ := by
      intro G' A
      have h := hms _ false hcube hnorm G' A
      simp only [Bool.false_eq_true, ite_false] at h
      exact_mod_cast h.trans (Nat.le_ceil _)
    have hKc : 0 < 16 * K * Wd B^4 := by have := hWd B; positivity
    set n := Fintype.card (Rest (JB B))
    have hnb : n ≤ Fintype.card κ :=
      Fintype.card_le_of_injective (fun i : Rest (JB B) => i.val.val)
        (Subtype.val_injective.comp Subtype.val_injective)
    have h := labelAvgT_le_of_geometry d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh
      C JB B P hPC 1 K T Wd ξr hKc cb (Cf n) (hCf n hnb).1 (Jf n) (ctl n) (hfin n hnb) ha (hgeo B hwB hcap)
      ⌈Cδ * Z^δ⌉₊ hmC hmD hMm ξ t
    refine h.trans ?_
    rw [gAmp_frame]
    have hA1 : rootAmp d (Jf n) (ctl n) ≤ rootAmp d Jd ctl' := by
      rw [← gAmp_frame d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh C B (JB B)
        P.V P.hV (Real.logb Z (16 * K * Wd B^4)) (Jf n) (ctl n),
        ← gAmp_frame d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh C B (JB B)
        P.V P.hV (Real.logb Z (16 * K * Wd B^4)) Jd ctl']
      exact (gAmp_mono 3 _ mesh η Z _).2 _ _ _ _ (hJf n hnb) (hctl n hnb)
    have hA0 : 0 ≤ rootAmp d (Jf n) (ctl n) := by
      rw [← gAmp_frame d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh C B (JB B)
        P.V P.hV (Real.logb Z (16 * K * Wd B^4)) (Jf n) (ctl n)]
      exact (gAmp_mono 3 _ mesh η Z _).1 _ _
    have hTp : (1 + ‖t‖)^(2*Jf n) ≤ (1 + ‖t‖)^(2*Jd) :=
      pow_le_pow_right₀ hT1 (by have := hJf n hnb; omega)
    have hp := alloc_P_ge d.root (by norm_num) d.cover C JB B
    have hZe := Real.rpow_nonneg hZ0.le (2*ε)
    have hNV : (0:ℝ) ≤ ((Ideal.span {P.V}).absNorm : ℝ) := Nat.cast_nonneg _
    have hvR := (sourceVolume_pos (renorm (restOf d.root (by norm_num) d.cover C B (JB B)))).le
    have hpos : 0 ≤ sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B (JB B)))^2 *
        (∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
        ((Ideal.span {P.V}).absNorm : ℝ) := by
      have : (0:ℝ) ≤ ∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val := by
        linarith
      positivity
    have hc1 : Cf n / (1/4:ℝ)^2 * rootAmp d (Jf n) (ctl n) * Z^(2*ε) ≤
        Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε) := by
      apply mul_le_mul_of_nonneg_right _ hZe
      apply mul_le_mul (div_le_div_of_nonneg_right (hCf n hnb).2 (by norm_num)) hA1 hA0
        (by positivity)
    have hc0 : 0 ≤ Cf n / (1/4:ℝ)^2 * rootAmp d (Jf n) (ctl n) * Z^(2*ε) := by
      have := (hCf n hnb).1; positivity
    calc (Cf n / (1/4:ℝ)^2 * rootAmp d (Jf n) (ctl n) * Z^(2*ε)) *
          sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B (JB B)))^2 *
          (∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
          ((Ideal.span {P.V}).absNorm : ℝ) * (1 + ‖t‖)^(2*Jf n)
        = (Cf n / (1/4:ℝ)^2 * rootAmp d (Jf n) (ctl n) * Z^(2*ε)) *
          (sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B (JB B)))^2 *
          (∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
          ((Ideal.span {P.V}).absNorm : ℝ)) * (1 + ‖t‖)^(2*Jf n) := by ring
      _ ≤ (Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε)) *
          (sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B (JB B)))^2 *
          (∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
          ((Ideal.span {P.V}).absNorm : ℝ)) * (1 + ‖t‖)^(2*Jd) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hc1 hpos) hTp (by positivity)
          exact mul_nonneg (hc0.trans hc1) hpos
      _ = _ := by ring
  · push Not at hcap
    rw [labelAvgT_zero_of_cap d.root ha (by norm_num) d.cover C JB P.base 1 (internalQ Q η₀)
      CenteredMomentSecondHeightFamily.fixedBadMask t K T Z ξr Wd B ξ hcap]
    exact hrest

/-- **The label half of a block from the root input.** -/
theorem labelHalf_of_rootInput (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hm : 0 ≤ mesh) (hmesh : ∀ i, d.w i ≤ mesh)
    (C D' : Id) (hC : Supported C) (hD : Supported D') (E : Finset (CommonIndex C D'))
    (K : ℝ) (hK : 0 < K) (ξr Mc : ℝ)
    (hML : MultBound d.root (by norm_num) d.cover C (selOf d hε mesh hm hmesh C) K
      (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
        (selOf d hε mesh hm hmesh C B)) (fun _ => Mc))
    (hMR : MultBound d.root (by norm_num) d.cover D' (selOf d hε mesh hm hmesh D') K
      (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
        (selOf d hε mesh hm hmesh D' B)) (fun _ => Mc))
    (cb : ℝ) (Jf : ℕ → ℕ) (ctl : ℕ → Finset (ℕ × ℕ)) (Cf : ℕ → ℝ) (Jd : ℕ)
    (ctl' : Finset (ℕ × ℕ)) (Cmax : ℝ) (hJf : ∀ n, n ≤ Fintype.card κ → Jf n ≤ Jd) (hctl : ∀ n, n ≤ Fintype.card κ → ctl n ⊆ ctl')
    (hCf : ∀ n, n ≤ Fintype.card κ → 0 ≤ Cf n ∧ Cf n ≤ Cmax)
    (hfin : ∀ n, n ≤ Fintype.card κ → SplitBoundAt D G (thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM hQ0 hQt hQ72 Holes N ε
      hε Bmask hBmask n) mesh η Z ε cb (Jf n) (ctl n) (Cf n))
    (ha : (0:ℝ) < 1/4)
    (hgeoL : ∀ B, allocWeight d.root C B ≠ 0 → 1 ≤ capRes d C B (selOf d hε mesh hm hmesh C B) →
      GeometryAt D G ε η (residFin d C B (selOf d hε mesh hm hmesh C B)) ha
      (frameOf d C B (selOf d hε mesh hm hmesh C B) hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask
        hBmask mesh hmesh (Packet.firstPacked C D' hC E) (Packet.firstPacked_ne_zero C D' hC E)
        (Real.logb Z (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
          (selOf d hε mesh hm hmesh C B))^4)))
      (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
          (selOf d hε mesh hm hmesh C B))^4)
      (frequencyRadius (Tfreq d C B (selOf d hε mesh hm hmesh C B)
        (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
          (selOf d hε mesh hm hmesh C B))^4)) Z ξr)
      (capRes d C B (selOf d hε mesh hm hmesh C B))
      (∑ j : selOf d hε mesh hm hmesh C B, d.w j.val.val) cb)
    (hgeoR : ∀ B, allocWeight d.root D' B ≠ 0 → 1 ≤ capRes d D' B (selOf d hε mesh hm hmesh D' B) →
      GeometryAt D G ε η (residFin d D' B (selOf d hε mesh hm hmesh D' B)) ha
      (frameOf d D' B (selOf d hε mesh hm hmesh D' B) hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask
        hBmask mesh hmesh (Packet.firstPackedRight C D' hC E)
        (Packet.firstPackedRight_ne_zero C D' hC E)
        (Real.logb Z (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
          (selOf d hε mesh hm hmesh D' B))^4)))
      (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
          (selOf d hε mesh hm hmesh D' B))^4)
      (frequencyRadius (Tfreq d D' B (selOf d hε mesh hm hmesh D' B)
        (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
          (selOf d hε mesh hm hmesh D' B))^4)) Z ξr)
      (capRes d D' B (selOf d hε mesh hm hmesh D' B))
      (∑ j : selOf d hε mesh hm hmesh D' B, d.w j.val.val) cb)
    (Cδ δ : ℝ)
    (hms : ∀ (S : Finset Id) (side : Bool),
      (∀ l : Lab S, l.1.val.1 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1, P)^2 ∧
        l.1.val.2 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2, P)^2) →
      (∀ l : Lab S, (l.1.val.1.absNorm : ℝ) ≤ Z^((2:ℝ)*4) ∧ (l.1.val.2.absNorm : ℝ) ≤ Z^((2:ℝ)*4)) →
      ∀ (G' : Id) (A : O),
        (((Finset.univ : Finset (Lab S)).filter (fun l =>
          (if side then l.1.val.1 else l.1.val.2) = G' ∧ lA S l = A)).card : ℝ) ≤ Cδ * Z^δ)
    (hMm : ((⌈Cδ * Z^δ⌉₊ : ℕ) : ℝ) ≤ Z^(ε/2))
    (N' : ℕ) (hJL : ∀ B, Fintype.card (selOf d hε mesh hm hmesh C B) ≤ N')
    (hJR : ∀ B, Fintype.card (selOf d hε mesh hm hmesh D' B) ≤ N')
    (hcf : Packet.CubeFreeCommon C D') (hcpC : CenteredMomentCompleteCommon.commonPart C D' = C)
    (hcpD : CenteredMomentCompleteCommon.commonPart D' C = D')
    (A loss θl : ℝ)
    (hkL : labelConst d.root C N' Mc (Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε)) ≤
      θl * A * Z^loss)
    (hkR : labelConst d.root D' N' Mc (Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε)) ≤
      θl * A * Z^loss)
    (hθ : 0 ≤ θl) (hA : 0 ≤ A) :
    LabelHalf d.root ha (by norm_num) d.cover η C D' hC E K A Z loss Jd
      (rootChoice d hε mesh hm hmesh Q C D' K ξr Mc hML hMR) θl := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hCmax : 0 ≤ Cmax := (hCf 0 (Nat.zero_le _)).1.trans (hCf 0 (Nat.zero_le _)).2
  have hAmp0 : 0 ≤ rootAmp d Jd ctl' := by
    unfold rootAmp
    have := sourceControl_nonneg ctl' d.root.W₁
    have := sourceControl_nonneg ctl' d.root.W₂
    have hV := d.hV
    positivity
  have hKl : 0 ≤ Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε) := by
    have := Real.rpow_nonneg hZ0.le (2*ε); positivity
  apply labelHalf_of_split d.root ha (by norm_num) d.cover η C D' hC hD E K A Z loss Jd
    (rootChoice d hε mesh hm hmesh Q C D' K ξr Mc hML hMR) θl
    (fun B => (Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε)) *
      sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B
        (selOf d hε mesh hm hmesh C B)))^2 *
      (∏ j : selOf d hε mesh hm hmesh C B,
        (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
      ((Ideal.span {Packet.firstPacked C D' hC E}).absNorm : ℝ))
    (fun B => (Cmax / (1/4:ℝ)^2 * rootAmp d Jd ctl' * Z^(2*ε)) *
      sourceVolume (renorm (restOf d.root (by norm_num) d.cover D' B
        (selOf d hε mesh hm hmesh D' B)))^2 *
      (∏ j : selOf d hε mesh hm hmesh D' B,
        (allocatedLiveSource d.root (by norm_num) d.cover D' B).P j.val) *
      ((Ideal.span {Packet.firstPackedRight C D' hC E}).absNorm : ℝ))
  · intro χ ξ B ξ' t hw
    exact side_label_bound d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh C
      (selOf d hε mesh hm hmesh C) (ConcreteLabelAssembly.SidePack.left
        (fixedPair η C D' hC E χ (ξ⁻¹))) dvd_rfl K hK _ _
      (fun B => slotWidth_pos _ _) ξr cb Jf ctl Cf Jd ctl' Cmax hJf hctl hCf hfin ha hgeoL Cδ δ hms
      hMm B ξ' t hw
  · intro χ ξ B ξ' t hw
    exact side_label_bound d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh D'
      (selOf d hε mesh hm hmesh D') (ConcreteLabelAssembly.SidePack.right
        (fixedPair η C D' hC E χ (ξ⁻¹))) dvd_rfl K hK _ _
      (fun B => slotWidth_pos _ _) ξr cb Jf ctl Cf Jd ctl' Cmax hJf hctl hCf hfin ha hgeoR Cδ δ hms
      hMm B ξ' t hw
  · intro B
    have hp := alloc_P_ge d.root (by norm_num) d.cover C (selOf d hε mesh hm hmesh C) B
    have : (0:ℝ) ≤ ((Ideal.span {Packet.firstPacked C D' hC E}).absNorm : ℝ) := Nat.cast_nonneg _
    have : (0:ℝ) ≤ ∏ j : selOf d hε mesh hm hmesh C B,
        (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val := by linarith
    positivity
  · intro B
    have hp := alloc_P_ge d.root (by norm_num) d.cover D' (selOf d hε mesh hm hmesh D') B
    have : (0:ℝ) ≤ ((Ideal.span {Packet.firstPackedRight C D' hC E}).absNorm : ℝ) :=
      Nat.cast_nonneg _
    have : (0:ℝ) ≤ ∏ j : selOf d hε mesh hm hmesh D' B,
        (allocatedLiveSource d.root (by norm_num) d.cover D' B).P j.val := by linarith
    positivity
  · exact hJL
  · exact hJR
  · intro B; exact le_rfl
  · intro B; exact le_rfl
  · exact hKl
  · exact hKl
  · intro B; exact le_rfl
  · intro B; exact le_rfl
  · exact hcf
  · exact hcpC
  · exact hcpD
  · exact hkL
  · exact hkR
  · exact hZ1.le
  · exact hθ
  · exact hA

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
