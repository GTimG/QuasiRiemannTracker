/- Copyright (c) 2026 Sil. Apache-2.0.
Provider geometry, part 5: **`GeometryAt` of a residual split** from scalar inputs.

`geometryAt_of`: for a root input `d`, an allocation `B` of `C` with nonzero weight, a selected
block `J` (selected width `u = Σ_J w`, live width `lw`), the frame source
`rs = frameOf … V₀ (log_Z K_c)` at a frame mesh `mesh ≤ mesh G ε`, and
* the first-step Gauss bound `K_c·N(C)²·Z ≤ C_st·V_root²·N(V₀)·Z^{4u}·Z^{(3/2)κ}`
  (`κ = cutoffLoss`), `1 ≤ K_c`, and the packed twist `N(V₀) ≤ N(C)²`,
* the selection (`floor ≤ lw`, `sel lw ≤ u ≤ sel lw + mesh`, or `lw ≤ floor`, `J = ∅`),
* `capRes ≥ 1` and the frame Poisson condition of `hdyad_of_freq`,
* large-`Z` conditions (`eventually_bigZ`) and `2κ ≤ 1 - Hmin` (small branch),
the split satisfies `GeometryAt` with `tl = 2κ`, the plain-length slop `2 log_Z (9/2) ≤ tl`
absorbed in `hroot`, `R = frequencyRadius (Tfreq … K_c) Z ξ_r`, `H = capRes`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry4

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
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open QRH.SilDensitySplit.CubeFree Qrh.MarkedAnchor.Ordinary QRH.SilDensitySplit.CubeFree.Second Qrh.MarkedAnchor.Ordinary.Second
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedCompletedRows MixedInnerExceptionalBlock
open RepairedRawContext
open Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypePG5 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

theorem cutoffLoss_small (hε : 0 < ε) : 0 < cutoffLoss G N ε ∧ cutoffLoss G N ε ≤ 1/1000 := by
  have hi := internal_spec G N ε hε
  have ho := omega_spec G ε hε
  unfold cutoffLoss
  constructor
  · exact div_pos hi.1 (by norm_num)
  · have := hi.2.2.1; linarith [ho.2.2.2]

theorem alloc_ne_zero (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) : C ≠ 0 := by
  have hprod := (Finset.mem_filter.mp B.property).2
  have hB := (allocation_data (tuplePools d.root) C B.val (Finset.mem_filter.mp B.property).1).1
  rw [← hprod]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hB i)

/-- The plain lengths of the frame source of a residual split (the plain-length slop). -/
theorem frame_gP_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh)
    (C : Id) (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (V₀ : O) (hV₀ : V₀ ≠ 0) (kLog : ℝ) :
    gP (frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh V₀ hV₀ kLog) ≤
      Real.logb Z d.root.T + 2 * Real.logb Z (9/2) := by
  have hZ1 := d.one_lt_Z
  have hL : (2/9:ℝ) ≤ d.root.L := by
    have h1 := Real.one_le_rpow hZ1.le d.hell
    calc (2/9:ℝ) = 2/9 * 1 := by ring
      _ ≤ 2/9 * Z^d.ell := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ d.root.L := d.hminimum
  have h := gP_le_logT Z (restOf d.root (by norm_num) d.cover C B J).X₁
    (restOf d.root (by norm_num) d.cover C B J).X₂ (restOf d.root (by norm_num) d.cover C B J).Y₁
    (restOf d.root (by norm_num) d.cover C B J).Y₂
    (nrm (restOf d.root (by norm_num) d.cover C B J).d.1)
    (nrm (restOf d.root (by norm_num) d.cover C B J).d.2) d.root.T hZ1
    (nrm_one_le (restOf d.root (by norm_num) d.cover C B J).hd.1)
    (nrm_one_le (restOf d.root (by norm_num) d.cover C B J).hd.2)
    (hL.trans (restOf d.root (by norm_num) d.cover C B J).hX₁)
    (hL.trans (restOf d.root (by norm_num) d.cover C B J).hX₂)
    (hL.trans (restOf d.root (by norm_num) d.cover C B J).hY₁)
    (hL.trans (restOf d.root (by norm_num) d.cover C B J).hY₂)
    (restOf d.root (by norm_num) d.cover C B J).hpX (restOf d.root (by norm_num) d.cover C B J).hpY
  exact h

/-- **`GeometryAt` of a residual split.** -/
theorem geometryAt_of (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (hB24 : 24 ≤ Bmask) (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh) (hm0 : 0 ≤ mesh)
    (hmG : mesh ≤ RootParameters.mesh G ε)
    (C : Id) (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (hwt : allocWeight d.root C B ≠ 0) (hC8 : (Ideal.absNorm C : ℝ) ≤ Z^(8:ℝ))
    (V₀ : O) (hV₀ : V₀ ≠ 0) (hV₀C : ((Ideal.span {V₀}).absNorm : ℝ) ≤ (Ideal.absNorm C : ℝ)^2)
    (Kc Cst ξr cb : ℝ) (hKc1 : 1 ≤ Kc) (hCst : 0 < Cst)
    (hKup : Kc * (Ideal.absNorm C : ℝ)^2 * Z ≤ Cst * sourceVolume d.root ^ 2 *
      ((Ideal.span {V₀}).absNorm : ℝ) * Z^(4 * selW d J) * Z^((3/2) * cutoffLoss G N ε))
    (hbranch : (G.floor ε ≤ liveW d B ∧ D.sel ε (liveW d B) ≤ selW d J ∧
        selW d J ≤ D.sel ε (liveW d B) + mesh) ∨ (liveW d B ≤ G.floor ε ∧ selW d J = 0))
    (hcap : 1 ≤ capRes d C B J)
    (hZc : 32 * ((9/4:ℝ)^2 * 2^(Fintype.card (Rest J)))^2 * Z^(ξr/2) ≤ Z^mesh)
    (hξr : ξr ≤ 2) (hcb : 19 ≤ cb) (hHmin : 2 * cutoffLoss G N ε ≤ 1 - D.Hmin)
    (hZ1 : Real.logb Z Cst ≤ cutoffLoss G N ε / 2)
    (hZ2 : 2 * (Fintype.card κ : ℝ) * Real.logb Z 2 ≤ rootReserve G)
    (hZ3 : Real.logb Z (9/2) ≤ cutoffLoss G N ε)
    (hZ4 : (81/16:ℝ) * 4^(Fintype.card κ) ≤ Z) (ha : (0:ℝ) < 1/4) :
    GeometryAt D G ε η (residFin d C B J) ha
      (frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh V₀ hV₀
        (Real.logb Z Kc))
      Kc (frequencyRadius (Tfreq d C B J Kc) Z ξr) (capRes d C B J) (selW d J) cb := by
  have hZ1' := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1'
  have hZ5 : (5:ℝ) ≤ Z := d.hZ
  set rs := frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh V₀ hV₀
    (Real.logb Z Kc) with hrs
  set κl := cutoffLoss G N ε with hκl
  obtain ⟨hκ0, hκ1⟩ := cutoffLoss_small (G := G) (N := N) hε
  have hrr := rootReserve_spec G
  have hms := mesh_spec G ε hε
  have hmL : mesh ≤ G.meshL ε := hmG.trans hms.2.2.2
  have hmr : mesh ≤ rootReserve G / 1024 := hmG.trans hms.2.1
  have htlL : 2 * κl ≤ G.tlL ε := by
    have h1 := cutoffLoss_le_tl G N ε hε
    have h2 := (G.ledger_spec hε).2.2.2.1
    rw [← hκl] at h1; linarith
  have hgf := G.face
  -- the ideal `C`
  have hC0 := alloc_ne_zero d C B
  have hNC1 : (1:ℝ) ≤ Ideal.absNorm C := one_le_absNorm hC0
  have hNC0 : (0:ℝ) < Ideal.absNorm C := by linarith
  have hNV1 : (1:ℝ) ≤ ((Ideal.span {V₀}).absNorm : ℝ) :=
    one_le_absNorm (Ideal.span_singleton_eq_bot.not.mpr hV₀)
  have hNV0 : (0:ℝ) < ((Ideal.span {V₀}).absNorm : ℝ) := by linarith
  have hKc0 : 0 < Kc := by linarith
  -- volumes
  set Vr := sourceVolume d.root with hVr
  set Vl := sourceVolume (renorm (allocatedLiveSource d.root (by norm_num) d.cover C B)) with hVl
  set Vs := sourceVolume (residOf d C B J) with hVs
  have hVr0 : 0 < Vr := sourceVolume_pos _
  have hVl0 : 0 < Vl := sourceVolume_pos _
  have hVs0 : 0 < Vs := sourceVolume_pos _
  set u := selW d J with hu
  set lw := liveW d B with hlw
  set S := ∑ i, d.w i with hS
  have e1 : Vs * Z^u = Vl := rest_vol_mul d C B J
  have e2 : Vr ≤ Vl * Ideal.absNorm C := by
    have h := live_volume_ge d.root (by norm_num) d.cover C B
      (frozen_ge_of_weight d.root C B hwt)
    have hn : nrm d.root.d.1 * nrm d.root.d.2 = 1 := by
      rw [d.hunit]; simp [nrm]
    rw [hn, one_mul] at h
    exact h
  have e3 : Vl * Ideal.absNorm C ≤ 2^(Fintype.card κ) * Vr :=
    live_volume_le d.root (by norm_num) d.cover C B
  have e4 : Vr = d.root.T * Z^S := root_vol d
  have hT0 : 0 < d.root.T := by
    rw [← d.root.hpX]
    exact mul_pos (d.root.hL.trans_le d.root.hX₁) (d.root.hL.trans_le d.root.hX₂)
  -- logarithms
  set lv := Real.logb Z Vr with hlv
  set c := Real.logb Z (Ideal.absNorm C : ℝ) with hc
  set ll := Real.logb Z Vl with hll
  set tw := Real.logb Z ((Ideal.span {V₀}).absNorm : ℝ) with htw
  set k := Real.logb Z Kc with hk
  have hlogZ : Real.logb Z Z = 1 := Real.logb_self_eq_one hZ1'
  have l1 : Real.logb Z Vs + u = ll := by
    rw [hll, ← e1, Real.logb_mul hVs0.ne' (Real.rpow_pos_of_pos hZ0 _).ne',
      Real.logb_rpow hZ0 hZ1'.ne']
  have l2 : lv ≤ ll + c := by
    have h := Real.logb_le_logb_of_le hZ1' hVr0 e2
    rwa [Real.logb_mul hVl0.ne' hNC0.ne'] at h
  have l3 : ll + c ≤ (Fintype.card κ : ℝ) * Real.logb Z 2 + lv := by
    have h := Real.logb_le_logb_of_le hZ1' (mul_pos hVl0 hNC0) e3
    rwa [Real.logb_mul hVl0.ne' hNC0.ne', Real.logb_mul (by positivity) hVr0.ne',
      Real.logb_pow] at h
  have l4 : lv = Real.logb Z d.root.T + S := by
    rw [hlv, e4, Real.logb_mul hT0.ne' (Real.rpow_pos_of_pos hZ0 _).ne',
      Real.logb_rpow hZ0 hZ1'.ne']
  have l5 : Real.logb Z d.root.T + S ≤ 1 - rootReserve G := face_volume G d.hface
  have hface := d.hface
  have hK : k + 2*c + 1 ≤ Real.logb Z Cst + 2*lv + tw + 4*u + (3/2)*κl := by
    have h := Real.logb_le_logb_of_le hZ1' (by positivity) hKup
    have eL : Real.logb Z (Kc * (Ideal.absNorm C : ℝ)^2 * Z) = k + 2*c + 1 := by
      rw [Real.logb_mul (by positivity) hZ0.ne', Real.logb_mul hKc0.ne' (by positivity), sq,
        Real.logb_mul hNC0.ne' hNC0.ne', hlogZ]; ring
    have eR : Real.logb Z (Cst * Vr ^ 2 * ((Ideal.span {V₀}).absNorm : ℝ) * Z^(4 * u) *
        Z^((3/2) * κl)) = Real.logb Z Cst + 2*lv + tw + 4*u + (3/2)*κl := by
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
        Real.logb_mul (by positivity) hNV0.ne', Real.logb_mul hCst.ne' (by positivity), sq,
        Real.logb_mul hVr0.ne' hVr0.ne', Real.logb_rpow hZ0 hZ1'.ne', Real.logb_rpow hZ0 hZ1'.ne']
      ring
    rw [eL, eR] at h; exact h
  have htw2 : tw ≤ 2*c := by
    have h := Real.logb_le_logb_of_le hZ1' hNV0 hV₀C
    rwa [sq, Real.logb_mul hNC0.ne' hNC0.ne', ← two_mul] at h
  have hk0 : 0 ≤ k := Real.logb_nonneg hZ1' hKc1
  have hc0 : 0 ≤ c := Real.logb_nonneg hZ1' hNC1
  have hl20 : 0 ≤ Real.logb Z 2 := Real.logb_nonneg hZ1' (by norm_num)
  -- widths
  obtain ⟨hu0, hul⟩ := selW_le d J
  have hlwS : lw ≤ S := liveW_le d B
  have hSc : D.s₀ ≤ S ∧ S ≤ D.c := ⟨hface.1, hface.2.1⟩
  -- the frame source
  have hvol : rs.vol = Vs := frame_vol_eq d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh
    hmesh C B J V₀ hV₀ _
  have hcH : commonH rs = 2 * Real.logb Z Vs - k + mesh + tw := by
    unfold commonH cutoffLog GSrc.colLog
    rw [hvol]; rfl
  have hlo : -(2*κl) ≤ commonH rs - 1 + 6*u := by rw [hcH]; linarith
  have hhi : commonH rs - 1 ≤ 1 + 2*κl := by rw [hcH]; linarith
  -- the plain lengths
  have hgP : gP rs ≤ Real.logb Z d.root.T + 2*κl := by
    have h := frame_gP_le d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh C B J V₀
      hV₀ (Real.logb Z Kc)
    linarith
  have hsum : ∑ i, rs.w i = lw - u := frame_w_sum d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask
    hBmask mesh hmesh C B J V₀ hV₀ _
  obtain ⟨hbr, hrange⟩ := branch_window D G η hε rs (2*κl) u lw S (Real.logb Z d.root.T) hm0 hmL
    (by linarith) htlL hHmin hSc hface.2.2 hgP hlwS hsum hlo hhi hbranch
  -- the box
  have hX : ∀ I ∈ S0 (residFin d C B J) ha, (Ideal.absNorm I : ℝ) ≤ Z^(8:ℝ) := by
    intro I hI
    unfold S0 at hI
    rw [CenteredMomentActiveSource.mem_activeSource] at hI
    exact residFin_pool_le d C B J I hI.1
  have hVrZ : Vr ≤ Z := by
    have h : lv ≤ 1 := by linarith [hrr.1]
    have h2 := (Real.logb_le_iff_le_rpow hZ1' hVr0).mp h
    rwa [Real.rpow_one] at h2
  have hcard := card_rest_le d J
  have hcapZ : capRes d C B J ≤ Z^2 := by
    rw [cap_eq_vol]
    have hVsl : Vs ≤ Vl := by
      rw [← e1]; exact le_mul_of_one_le_right hVs0.le (Real.one_le_rpow hZ1'.le hu0)
    have hVl2 : Vl ≤ 2^(Fintype.card κ) * Z := by
      have : Vl ≤ Vl * Ideal.absNorm C := le_mul_of_one_le_right hVl0.le hNC1
      have h2 : (2:ℝ)^(Fintype.card κ) * Vr ≤ 2^(Fintype.card κ) * Z :=
        mul_le_mul_of_nonneg_left hVrZ (by positivity)
      linarith
    have h2n : (2:ℝ)^(Fintype.card (Rest J)) ≤ 2^(Fintype.card κ) :=
      pow_le_pow_right₀ (by norm_num) hcard
    have h4 : (2:ℝ)^(Fintype.card κ) * 2^(Fintype.card κ) = 4^(Fintype.card κ) := by
      rw [← mul_pow]; norm_num
    calc (9/4:ℝ)^2 * 2^(Fintype.card (Rest J)) * Vs
        ≤ (9/4:ℝ)^2 * 2^(Fintype.card κ) * (2^(Fintype.card κ) * Z) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2n (by norm_num)) (hVsl.trans hVl2)
            hVs0.le (by positivity)
      _ = (81/16:ℝ) * 4^(Fintype.card κ) * Z := by rw [← h4]; ring
      _ ≤ Z * Z := mul_le_mul_of_nonneg_right hZ4 hZ0.le
      _ = Z^2 := by ring
  have hZ18 : (Z:ℝ)^(18:ℝ) = Z^(18:ℕ) := by
    rw [show (18:ℝ) = ((18:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hZ2le : Z^2 ≤ Z^(18:ℕ) := pow_le_pow_right₀ hZ1'.le (by norm_num)
  have hH18 : capRes d C B J ≤ Z^(18:ℝ) := by rw [hZ18]; exact hcapZ.trans hZ2le
  have hR18 : 4 * frequencyRadius (Tfreq d C B J Kc) Z ξr ≤ Z^(18:ℝ) := by
    unfold frequencyRadius Tfreq
    rw [max_eq_right hcap]
    have h1 : capRes d C B J ^ 2 / Kc ≤ Z^4 := by
      calc capRes d C B J ^ 2 / Kc ≤ capRes d C B J ^ 2 := div_le_self (sq_nonneg _) hKc1
        _ ≤ (Z^2)^2 := pow_le_pow_left₀ (by linarith) hcapZ 2
        _ = Z^4 := by ring
    have h2 : Z^(ξr/2) ≤ Z := by
      calc Z^(ξr/2) ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1'.le (by linarith)
        _ = Z := Real.rpow_one Z
    have h3 : capRes d C B J ^ 2 / Kc * Z^(ξr/2) ≤ Z^4 * Z :=
      mul_le_mul h1 h2 (Real.rpow_nonneg hZ0.le _) (by positivity)
    rw [hZ18]
    calc 4 * (capRes d C B J ^ 2 / Kc * Z^(ξr/2)) ≤ Z * (Z^4 * Z) :=
          mul_le_mul (by linarith) h3 (by positivity) hZ0.le
      _ = Z^6 := by ring
      _ ≤ Z^18 := pow_le_pow_right₀ hZ1'.le (by norm_num)
  have hKc18 : Kc ≤ Z^(18:ℝ) := by
    have hk18 : k ≤ 18 := by
      have : u ≤ 1/6 := by linarith [hgf.2.2.2.2.2.1]
      linarith [hrr.1]
    exact (Real.logb_le_iff_le_rpow hZ1' hKc0).mp hk18
  obtain ⟨Mbox, hM, hbox⟩ := box_exists (S0 (residFin d C B J) ha) Kc
    (frequencyRadius (Tfreq d C B J Kc) Z ξr) (capRes d C B J) Z cb (by linarith) hcb hX hKc1
    hKc18 hR18 hH18
  -- the caps
  have eR : (residFin d C B J).R = C := by
    change d.root.R * C = C; rw [d.hR, one_mul]
  have eH : holes (residFin d C B J).H = ∅ := by
    change holes d.root.H = ∅; rw [d.hH]; rfl
  have hcapL : ∀ (sel : Lab (S0 (residFin d C B J) ha) → Id),
      (∀ l, sel l = l.1.val.1 ∨ sel l = l.1.val.2) →
      ∀ l : Lab (S0 (residFin d C B J) ha), ∀ Lp ∈ labelPool (S0 (residFin d C B J) ha) l,
      (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport
        (((residFin d C B J).R * sel l) * Lp) ∪ holes (residFin d C B J).H, I) : ℝ) ≤ Z^Bmask := by
    intro sel hsel l Lp hLp
    rw [eR, eH]
    obtain ⟨hc1, hc2⟩ := lab_cols_le _ _ hX l
    obtain ⟨hLp0, hLp8⟩ := labelPool_le _ _ hX l Lp hLp
    have hd := lab_data _ l
    rcases hsel l with h | h <;> rw [h]
    · exact cap_le C _ Lp hC0 hd.1.1 hLp0 Z Bmask hZ1'.le hB24 hC8 hc1 hLp8
    · exact cap_le C _ Lp hC0 hd.2.1.1 hLp0 Z Bmask hZ1'.le hB24 hC8 hc2 hLp8
  refine ⟨Mbox, hM, hbox, ?_, hcapL (fun l => l.1.val.1) (fun l => Or.inl rfl),
    hcapL (fun l => l.1.val.2) (fun l => Or.inr rfl), hbr, hrange⟩
  exact hdyad_of_freq d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh C B J V₀ hV₀
    Kc ξr hKc0 hcap hZc

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
