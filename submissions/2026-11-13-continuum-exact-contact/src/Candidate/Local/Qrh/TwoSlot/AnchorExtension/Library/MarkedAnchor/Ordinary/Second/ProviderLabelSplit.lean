/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, label half: the per-split label bound in the `Λ`-form of
`label_budget`, from `split_label_bound_final` (as a hypothesis on the frame data `θ`),
`rootLabelData_of` and `GeometryAt`.

* `zpow_selected`: `Z^u = ∏_{J_B} P_j` (`u = Σ_{J_B} w_j`, canonical `P = Z^w`).
* `exp_le_of_geometry`: `Z^{A-c+q_C+2ε} ≤ vol·N(V₀)·Z^u·Z^{2ε}` from the exponent clause of
  `GeometryAt`.
* `labelAvgT_le_of_geometry`: for an allocation with `capRes ≥ 1`, the split label part is at most
  `(C_θ/c_low·A_θ·Z^{2ε})·V(renorm rest_B)²·∏_{J_B}P·N(V₀)·(1+|t|)^{2J_θ}`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderLabelHalf

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
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open RepairedRawContext
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open RayFourExpansion CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderLS {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

theorem zpow_selected (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    Z^(∑ j : J, d.w j.val.val) = ∏ j : J, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val := by
  obtain ⟨-, -, -, -, hP⟩ := d.hcanonical
  have hZ0 : 0 < Z := zero_lt_one.trans d.one_lt_Z
  rw [Real.rpow_sum_of_pos hZ0]
  apply Finset.prod_congr rfl
  intro j _
  exact (congrFun hP j.val.val).symm

theorem exp_le_of_geometry {θ : GData 3} {mesh : ℝ} (rs : GSrc θ mesh Z) (hZ : 1 < Z)
    (A c qC u : ℝ) (h : A - c + qC ≤ rs.colLog + rs.twistLog + u) :
    Z^(A - c + qC + 2*ε) ≤
      rs.vol * ((Ideal.span {rs.V₀}).absNorm : ℝ) * Z^u * Z^(2*ε) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hv : 0 < rs.vol := rs.vol_pos hZ0
  have hn : 0 < ((Ideal.span {rs.V₀}).absNorm : ℝ) := absNorm_span_pos _ rs.hV₀
  calc Z^(A - c + qC + 2*ε) ≤ Z^(rs.colLog + rs.twistLog + u + 2*ε) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = rs.vol * ((Ideal.span {rs.V₀}).absNorm : ℝ) * Z^u * Z^(2*ε) := by
        rw [Real.rpow_add hZ0, Real.rpow_add hZ0, Real.rpow_add hZ0]
        unfold GSrc.colLog GSrc.twistLog
        rw [Real.rpow_logb hZ0 hZ.ne' hv, Real.rpow_logb hZ0 hZ.ne' hn]

/-- The conclusion of `split_label_bound_final` at one frame data `θ` and scale `Z`. -/
def SplitBoundAt (D : StepData) (G : StepGates D) {L : ℝ} (θ : GData L) (mesh : ℝ) (η : Character)
    (Z ε cb : ℝ) (J : ℕ) (control : Finset (ℕ × ℕ)) (Cθ : ℝ) : Prop :=
  ∀ (P : SidePack η) (ξ : RayCharacter) (Q : Id) (m : O) (χ₀ : RayCharacter)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z) (Kc R H : ℝ) (Mb : ℤ)
    (Mm : ℕ) (clow : ℝ), RootLabelData P Q m s ha rs Kc R H Mb Mm clow →
    (0 ≤ Mb ∧ (Mb:ℝ) ≤ cb * Real.logb 2 Z + 2) → (Mm : ℝ) ≤ Z^(ε/2) → ∀ A c qC : ℝ,
    BranchData D G (gFrame L θ mesh η Z) ε mesh rs A c qC (commonH rs) →
    (D.Hmin ≤ commonH rs ∧ commonH rs ≤ D.Hmax) → ∀ t : ℝ,
      splitLabel (S0 s ha) (sourceCoefficient s ha 1) (childCharacter P.base ξ) χ₀ Q m t Kc R H ≤
        (Cθ * (rs.vol / clow) * gAmp L θ mesh η Z rs J control * Z^(A - c + qC + 2*ε)) *
          (1 + ‖t‖)^(2*J)

/-- **The per-split label bound of an allocation in the `Λ`-form.** -/
theorem labelAvgT_le_of_geometry (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh) (C : Id)
    (JB : (B : actualAllocations (tuplePools d.root) C) → Finset (liveIndices B.val))
    (B : actualAllocations (tuplePools d.root) C) (P : SidePack η) (hPC : P.Cs ∣ C)
    (χ₀ : RayCharacter) (K : ℝ) (T Wd : actualAllocations (tuplePools d.root) C → ℝ) (ξr : ℝ)
    (hKc : 0 < 16 * K * Wd B^4) (cb Cθ : ℝ) (hCθ : 0 ≤ Cθ) (Jθ : ℕ) (control : Finset (ℕ × ℕ))
    (hfin : SplitBoundAt D G (thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM hQ0 hQt hQ72 Holes N ε hε
      Bmask hBmask (Fintype.card (Rest (JB B)))) mesh η Z ε cb Jθ control Cθ)
    (ha : (0:ℝ) < 1/4)
    (hgeo : GeometryAt D G ε η (residFin d C B (JB B)) ha
      (frameOf d C B (JB B) hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh P.V P.hV
        (Real.logb Z (16 * K * Wd B^4)))
      (16 * K * Wd B^4) (frequencyRadius (T B) Z ξr) (capRes d C B (JB B))
      (∑ j : JB B, d.w j.val.val) cb)
    (Mm : ℕ)
    (hmultC : ∀ (G' : Id) (A : O), ((Finset.univ : Finset (Lab (S0 (residFin d C B (JB B)) ha))).filter
      (fun l => l.1.val.1 = G' ∧ lA (S0 (residFin d C B (JB B)) ha) l = A)).card ≤ Mm)
    (hmultD : ∀ (G' : Id) (A : O), ((Finset.univ : Finset (Lab (S0 (residFin d C B (JB B)) ha))).filter
      (fun l => l.1.val.2 = G' ∧ lA (S0 (residFin d C B (JB B)) ha) l = A)).card ≤ Mm)
    (hMm : (Mm : ℝ) ≤ Z^(ε/2)) (ξ : RayCharacter) (t : ℝ) :
    labelAvgT d.root ha (by norm_num) d.cover C JB P.base χ₀ (internalQ Q η₀)
        CenteredMomentSecondHeightFamily.fixedBadMask t K T Z ξr Wd B ξ ≤
      (Cθ / (1/4:ℝ)^2 * gAmp 3 (thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM hQ0 hQt hQ72 Holes N ε hε
          Bmask hBmask (Fintype.card (Rest (JB B)))) mesh η Z
          (frameOf d C B (JB B) hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh P.V P.hV
            (Real.logb Z (16 * K * Wd B^4))) Jθ control * Z^(2*ε)) *
        sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B (JB B)))^2 *
        (∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
        ((Ideal.span {P.V}).absNorm : ℝ) * (1 + ‖t‖)^(2*Jθ) := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  rw [labelAvgT_eq_split]
  obtain ⟨Mbox, hM, hbox, hdyad, hcapC, hcapD, ⟨A, c, qC, hbr, hexp⟩, hHr⟩ := hgeo
  have hR := rootLabelData_of d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh C B
    (JB B) P hPC (16 * K * Wd B^4) (frequencyRadius (T B) Z ξr) (capRes d C B (JB B)) hKc Mbox Mm ha
    hbox hdyad hcapC hcapD hmultC hmultD
  have h := hfin P ξ (internalQ Q η₀) CenteredMomentSecondHeightFamily.fixedBadMask χ₀ _ ha _ _ _ _
    Mbox Mm _ hR hM hMm A c qC hbr hHr t
  refine h.trans ?_
  set rs := frameOf d C B (JB B) hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh P.V P.hV
    (Real.logb Z (16 * K * Wd B^4))
  have hvol : rs.vol = sourceVolume (renorm (restOf d.root (by norm_num) d.cover C B (JB B))) :=
    frame_vol_eq d hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh C B (JB B) P.V P.hV _
  have hex := exp_le_of_geometry (ε := ε) rs hZ1 A c qC _ hexp
  rw [zpow_selected d C B (JB B)] at hex
  have hgA := (gAmp_mono 3 _ mesh η Z rs).1 Jθ control
  have hv0 : 0 < rs.vol := rs.vol_pos hZ0
  have hT : 0 ≤ (1 + ‖t‖)^(2*Jθ) := by positivity
  have hpre : 0 ≤ Cθ * (rs.vol / (1/4:ℝ)^2) * gAmp 3 _ mesh η Z rs Jθ control := by positivity
  calc (Cθ * (rs.vol / (1/4:ℝ)^2) * gAmp 3 _ mesh η Z rs Jθ control * Z^(A - c + qC + 2*ε)) *
        (1 + ‖t‖)^(2*Jθ)
      ≤ (Cθ * (rs.vol / (1/4:ℝ)^2) * gAmp 3 _ mesh η Z rs Jθ control *
          (rs.vol * ((Ideal.span {rs.V₀}).absNorm : ℝ) *
            (∏ j : JB B, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) *
            Z^(2*ε))) * (1 + ‖t‖)^(2*Jθ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex hpre) hT
    _ = _ := by
        rw [← hvol]
        change _ = _ * _ * _ * ((Ideal.span {rs.V₀}).absNorm : ℝ) * _
        ring

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
