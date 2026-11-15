/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The raw-side provider: `ContraryRawSideProvider` from per-block data.

* `BlockData`: every input of `balanced_summed_raw_side_bounds_avg` for one first block
  (selection, widths, multiplicities, second-step parameters, diagonal and label bounds of both
  sides, and their sums against the balanced budgets).
* `blockData_bounds`: `BlockData → BalancedSummedRawSideBounds` (per block).
* `supplyFor_of_blockData`: block data for every first label, inactive subset and retained block
  of a root input give `SupplyFor d J control Cside`.
* `provider_of_blockData`: a uniform block-data supplier (same quantifier order as
  `ProviderAt`) gives `ContraryRawSideProvider G`.
* `label_main_le_budget`: the label budget main term `K·Nτ·V²/(N G·N opp)` (`label_budget`) is
  at most `θ·balancedBudget` once `K ≤ θ·A·Z^loss` (the allowance is nonnegative);
  `hbud_of_parts`: the diagonal and label parts at `θ_d + θ_l ≤ 1` give `hbud`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderLabelBudget
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteAssemblyAvgT
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedSourceSideSupply
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.SideInstance
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Native

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second QRH.SilDensitySplit.CubeFree.Second.Provider
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

local instance (priority := 2000) instDecEqSubtypeProvider {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- **The data of one first block**: all inputs of `balanced_summed_raw_side_bounds_avg`. -/
def BlockData (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (η : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (K A Z loss : ℝ) (Jd : ℕ) : Prop :=
  ∃ (hCD : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport D)
    (JL : (B : actualAllocations (tuplePools s) C) → Finset (liveIndices B.val))
    (JR : (B : actualAllocations (tuplePools s) D) → Finset (liveIndices B.val))
    (WL ML : actualAllocations (tuplePools s) C → ℝ) (WR MR : actualAllocations (tuplePools s) D → ℝ)
    (χ₀ : RayCharacter) (Q : Id) (m : O)
    (TL : actualAllocations (tuplePools s) C → ℝ) (TR : actualAllocations (tuplePools s) D → ℝ)
    (Zs ξr : ℝ)
    (EdL ElL EdR ElR : RayCharacter → RayCharacter → ℝ),
    WidthBound s hb cover C JL WL ∧ MultBound s hb cover C JL K WL ML ∧
    WidthBound s hb cover D JR WR ∧ MultBound s hb cover D JR K WR MR ∧
    (∀ χ ξ v, outerAvg s hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left v ML
      (diagAvgT s ha hb cover C JL (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).left
        χ₀ Q m v K TL Zs ξr WL) ≤ EdL χ ξ * (1+‖v‖)^(2*Jd)) ∧
    (∀ χ ξ v, outerAvg s hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left v ML
      (labelAvgT s ha hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left χ₀ Q m v K TL Zs ξr WL)
        ≤ ElL χ ξ * (1+‖v‖)^(2*Jd)) ∧
    (∀ χ ξ v, outerAvg s hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right v MR
      (diagAvgT s ha hb cover D JR (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).right
        χ₀ Q m v K TR Zs ξr WR) ≤ EdR χ ξ * (1+‖v‖)^(2*Jd)) ∧
    (∀ χ ξ v, outerAvg s hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right v MR
      (labelAvgT s ha hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right χ₀ Q m v K TR Zs ξr WR)
        ≤ ElR χ ξ * (1+‖v‖)^(2*Jd)) ∧
    (∀ χ ξ, EdL χ ξ + ElL χ ξ ≤
      balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss) ∧
    (∀ χ ξ, EdR χ ξ + ElR χ ξ ≤
      balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss)

theorem blockData_bounds (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (η : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (K A Z loss : ℝ) (hK : 0 < K) (Jd : ℕ)
    (h : BlockData s ha hb cover η C D hC hD E K A Z loss Jd) :
    BalancedSummedRawSideBounds s ha η C D hC hD E K K A Z loss Jd := by
  obtain ⟨hCD, JL, JR, WL, ML, WR, MR, χ₀, Q, m, TL, TR, Zs, ξr, EdL, ElL, EdR, ElR,
    hWL, hML, hWR, hMR, hdL, hlL, hdR, hlR, hbL, hbR⟩ := h
  exact balanced_summed_raw_side_bounds_avgT s ha hb cover η C D hC hD hCD E K K A Z loss hK hK Jd
    JL JR WL ML WR MR hWL hML hWR hMR χ₀ Q m TL TR Zs ξr EdL ElL EdR ElR hdL hlL hdR hlR hbL hbR

/-- **`SupplyFor` from block data.** -/
theorem supplyFor_of_blockData {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
    {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Cside : ℝ)
    (h : ∀ p : Labels d.root (by norm_num) 1, ∀ E ∈ inactiveSubsets p.val.1 p.val.2,
      ∀ n : Blocks (effectiveScale p.val.1 p.val.2 E d.Kroot)
          (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z (cutoffLoss G N ε))
          (Z^(8:ℝ)/p.val.1.absNorm) (Z^(8:ℝ)/p.val.2.absNorm),
        1/2 ≤ dyadicScale (n 1) →
        BlockData d.root (by norm_num) (by norm_num) d.cover η p.val.1 p.val.2
          (commonLabels_supported (activeSource (sourceColumns d.root)
            (sourceCoefficient d.root (by norm_num) 1)) p).1
          (commonLabels_supported (activeSource (sourceColumns d.root)
            (sourceCoefficient d.root (by norm_num) 1)) p).2 E
          (childScale Z (cutoffLoss G N ε) (n 1))
          (amplitude d.root d.t₀ d.V J control Cside) Z (3*ε) J) :
    SupplyFor d J control Cside := by
  intro p E hE n hn
  have hZ : 0 < Z := by linarith [d.hZ]
  exact blockData_bounds d.root _ (by norm_num) d.cover η _ _ _ _ E _ _ Z (3*ε)
    (Real.rpow_pos_of_pos hZ _) J (h p E hE n hn)

/-- **The provider from a uniform block-data supplier** (the quantifier order of
`ProviderAt`). -/
theorem provider_of_blockData {D : StepData} (G : StepGates D)
    (hsup : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → ∀ ε : ℝ, 0 < ε → ∃ meshCap : ℝ, 0 < meshCap ∧
      ∀ (α : Type) [Fintype α] [DecidableEq α],
      ∀ (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H),
      ∀ (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2),
      ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Id) [NeZero Q],
        Q≠⊤ → Q ≤ Ideal.span {(72:O)} → Q ≤ M → Q ≤ η₀.modulus →
      ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ Cside : ℝ,
        1 ≤ Cside ∧ (0,0)∈control ∧ ∀ᶠ Z : ℝ in atTop, 5 ≤ Z ∧
        ∀ k : RootShape α,
        ∀ d : RootInput G M H hH (RootSlot k) W (Fintype.card α) (2*Fintype.card α) ε Z
          (RestoredRootSource.slotBound W hW.continuous hWs) η η₀,
          d.Kroot=bΦ*Z → (∀ i, d.w i ≤ meshCap) →
          ∀ p : Labels d.root (by norm_num) 1, ∀ E ∈ inactiveSubsets p.val.1 p.val.2,
          ∀ n : Blocks (effectiveScale p.val.1 p.val.2 E d.Kroot)
              (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z (cutoffLoss G (Fintype.card α) ε))
              (Z^(8:ℝ)/p.val.1.absNorm) (Z^(8:ℝ)/p.val.2.absNorm),
            1/2 ≤ dyadicScale (n 1) →
            BlockData d.root (by norm_num) (by norm_num) d.cover η p.val.1 p.val.2
              (commonLabels_supported (activeSource (sourceColumns d.root)
                (sourceCoefficient d.root (by norm_num) 1)) p).1
              (commonLabels_supported (activeSource (sourceColumns d.root)
                (sourceCoefficient d.root (by norm_num) 1)) p).2 E
              (childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1))
              (amplitude d.root d.t₀ d.V J control Cside) Z (3*ε) J) :
    ContraryRawSideProvider G := by
  intro hβ ε hε
  obtain ⟨meshCap, hmc, h⟩ := hsup hβ ε hε
  refine ⟨meshCap, hmc, ?_⟩
  intro α _ _ M _ H hH W hW hWs bΦ hbΦ η η₀ Q _ hQt hQ72 hQM hQη
  obtain ⟨J, control, Cside, hC, h0, hev⟩ := h α M H hH W hW hWs bΦ hbΦ η η₀ Q hQt hQ72 hQM hQη
  refine ⟨J, control, Cside, hC, h0, ?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1, fun k d hK hw => ?_⟩
  exact supplyFor_of_blockData d J control Cside (hZ.2 k d hK hw)

/-! ### The split into a diagonal half and a label half

`BlockChoice` is the data shared by both halves (selection, widths, multiplicities, second-step
parameters); `DiagHalf` (`ProviderDiag.lean`) and `LabelHalf` are the two halves of
`BlockData` at budget shares `θd`, `θl`; `blockData_of_halves` recombines them. -/

/-- **The shared choices of one block.** -/
structure BlockChoice (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (C D : Id)
    (K : ℝ) where
  JL : (B : actualAllocations (tuplePools s) C) → Finset (liveIndices B.val)
  JR : (B : actualAllocations (tuplePools s) D) → Finset (liveIndices B.val)
  WL : actualAllocations (tuplePools s) C → ℝ
  ML : actualAllocations (tuplePools s) C → ℝ
  WR : actualAllocations (tuplePools s) D → ℝ
  MR : actualAllocations (tuplePools s) D → ℝ
  χ₀ : RayCharacter
  Q : Id
  m : O
  /-- the second-step frequency of each allocation (left / right) -/
  TL : actualAllocations (tuplePools s) C → ℝ
  TR : actualAllocations (tuplePools s) D → ℝ
  Zs : ℝ
  ξr : ℝ
  hWL : WidthBound s hb cover C JL WL
  hML : MultBound s hb cover C JL K WL ML
  hWR : WidthBound s hb cover D JR WR
  hMR : MultBound s hb cover D JR K WR MR

/-- **The diagonal half** (zero frequency, fixed-inducing rows, tails) of both sides, at budget
share `θ`. -/
def DiagHalf (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (η : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (K A Z loss : ℝ) (Jd : ℕ)
    (c : BlockChoice s hb cover C D K) (θ : ℝ) : Prop :=
  ∃ EdL EdR : RayCharacter → RayCharacter → ℝ,
    (∀ χ ξ v, outerAvg s hb cover C c.JL (fixedPair η C D hC E χ (ξ⁻¹)).left v c.ML
      (diagAvgT s ha hb cover C c.JL (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).left
        c.χ₀ c.Q c.m v K c.TL c.Zs c.ξr c.WL) ≤ EdL χ ξ * (1+‖v‖)^(2*Jd)) ∧
    (∀ χ ξ v, outerAvg s hb cover D c.JR (fixedPair η C D hC E χ (ξ⁻¹)).right v c.MR
      (diagAvgT s ha hb cover D c.JR (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).right
        c.χ₀ c.Q c.m v K c.TR c.Zs c.ξr c.WR) ≤ EdR χ ξ * (1+‖v‖)^(2*Jd)) ∧
    (∀ χ ξ, EdL χ ξ ≤ θ * balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss) ∧
    (∀ χ ξ, EdR χ ξ ≤ θ * balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss)

/-- **The label half** (regrouped nonfixed blocks) of both sides, at budget share `θ`. -/
def LabelHalf (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (η : Character) (C D : Id) (hC : Supported C) (E : Finset (CommonIndex C D))
    (K A Z loss : ℝ) (Jd : ℕ) (c : BlockChoice s hb cover C D K) (θ : ℝ) : Prop :=
  ∃ ElL ElR : RayCharacter → RayCharacter → ℝ,
    (∀ χ ξ v, outerAvg s hb cover C c.JL (fixedPair η C D hC E χ (ξ⁻¹)).left v c.ML
      (labelAvgT s ha hb cover C c.JL (fixedPair η C D hC E χ (ξ⁻¹)).left c.χ₀ c.Q c.m v K c.TL
        c.Zs c.ξr c.WL) ≤ ElL χ ξ * (1+‖v‖)^(2*Jd)) ∧
    (∀ χ ξ v, outerAvg s hb cover D c.JR (fixedPair η C D hC E χ (ξ⁻¹)).right v c.MR
      (labelAvgT s ha hb cover D c.JR (fixedPair η C D hC E χ (ξ⁻¹)).right c.χ₀ c.Q c.m v K c.TR
        c.Zs c.ξr c.WR) ≤ ElR χ ξ * (1+‖v‖)^(2*Jd)) ∧
    (∀ χ ξ, ElL χ ξ ≤ θ * balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss) ∧
    (∀ χ ξ, ElR χ ξ ≤ θ * balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss)

theorem balancedBudget_nonneg (s : Source ι a b) (τ : Character) (G opp : Id) (A Z loss : ℝ)
    (hA : 0 ≤ A) (hZ : 0 ≤ Z) : 0 ≤ balancedBudget s τ G opp A Z loss := by
  unfold balancedBudget
  have := (sourceVolume_pos s).le
  have h1 := Real.rpow_nonneg hZ (allowance G opp Z)
  have h2 := Real.rpow_nonneg hZ loss
  positivity

/-- **Recombination**: the two halves at `θd + θl ≤ 1` give `BlockData`. -/
theorem blockData_of_halves (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (η : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport D)
    (E : Finset (CommonIndex C D)) (K A Z loss : ℝ) (Jd : ℕ) (hA : 0 ≤ A) (hZ : 0 ≤ Z)
    (c : BlockChoice s hb cover C D K) (θd θl : ℝ) (hθ : θd + θl ≤ 1)
    (hd : DiagHalf s ha hb cover η C D hC hD E K A Z loss Jd c θd)
    (hl : LabelHalf s ha hb cover η C D hC E K A Z loss Jd c θl) :
    BlockData s ha hb cover η C D hC hD E K A Z loss Jd := by
  obtain ⟨EdL, EdR, hdL, hdR, hbdL, hbdR⟩ := hd
  obtain ⟨ElL, ElR, hlL, hlR, hblL, hblR⟩ := hl
  refine ⟨hCD, c.JL, c.JR, c.WL, c.ML, c.WR, c.MR, c.χ₀, c.Q, c.m, c.TL, c.TR, c.Zs, c.ξr,
    EdL, ElL, EdR, ElR, c.hWL, c.hML, c.hWR, c.hMR, hdL, hlL, hdR, hlR, ?_, ?_⟩
  · intro χ ξ
    have hB := balancedBudget_nonneg s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss hA hZ
    have := hbdL χ ξ; have := hblL χ ξ
    nlinarith
  · intro χ ξ
    have hB := balancedBudget_nonneg s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss hA hZ
    have := hbdR χ ξ; have := hblR χ ξ
    nlinarith

/-! ### Label and diagonal parts against the balanced budget -/

/-- The label main term is a `θ`-share of the balanced budget once its constant is. -/
theorem label_main_le_budget (s : Source ι a b) (τ : Character) (G opp : Id) (hG : G ≠ 0)
    (hopp : opp ≠ 0) (A Z loss Kmain θ : ℝ) (hZ : 1 ≤ Z) (hθ : 0 ≤ θ) (hK : Kmain ≤ θ * A * Z^loss)
    (hA : 0 ≤ A) :
    Kmain * ((Ideal.absNorm τ.modulus : ℝ) * sourceVolume s^2 /
        ((Ideal.absNorm G : ℝ) * (Ideal.absNorm opp : ℝ))) ≤
      θ * balancedBudget s τ G opp A Z loss := by
  unfold balancedBudget
  have hmain : 0 ≤ (Ideal.absNorm τ.modulus : ℝ) * sourceVolume s^2 /
      ((Ideal.absNorm G : ℝ) * (Ideal.absNorm opp : ℝ)) := by positivity
  have hall : 1 ≤ Z^(allowance G opp Z) := Real.one_le_rpow hZ (by
    unfold allowance; positivity)
  have hZl : 0 ≤ Z^loss := Real.rpow_nonneg (zero_le_one.trans hZ) _
  calc Kmain * ((Ideal.absNorm τ.modulus : ℝ) * sourceVolume s^2 /
        ((Ideal.absNorm G : ℝ) * (Ideal.absNorm opp : ℝ)))
      ≤ (θ * A * Z^loss) * ((Ideal.absNorm τ.modulus : ℝ) * sourceVolume s^2 /
        ((Ideal.absNorm G : ℝ) * (Ideal.absNorm opp : ℝ))) := mul_le_mul_of_nonneg_right hK hmain
    _ ≤ (θ * A * Z^loss) * ((Ideal.absNorm τ.modulus : ℝ) * sourceVolume s^2 /
        ((Ideal.absNorm G : ℝ) * (Ideal.absNorm opp : ℝ)) * Z^(allowance G opp Z)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_mul_of_one_le_right hmain hall
    _ = _ := by ring

/-- `hbud` from a diagonal share and a label share. -/
theorem hbud_of_parts (Ed El Bud θd θl : ℝ) (hd : Ed ≤ θd * Bud) (hl : El ≤ θl * Bud)
    (hθ : θd + θl ≤ 1) (hB : 0 ≤ Bud) : Ed + El ≤ Bud := by
  nlinarith

/-! ### First labels and the plain-length leaves -/

/-- First labels: `commonPart C D = C`, `commonPart D C = D`, equal prime supports. -/
theorem first_label_parts (r : Source ι a b) (ha : 0 < a) (p : Labels r ha 1) :
    CenteredMomentCompleteCommon.commonPart p.val.1 p.val.2 = p.val.1 ∧
      CenteredMomentCompleteCommon.commonPart p.val.2 p.val.1 = p.val.2 := by
  have hd := commonLabels_data _ _ p.val.1 p.val.2 p.property
  exact ⟨CenteredMomentSecondCanonical.commonPart_eq_left _ _ hd.1 hd.2.2,
    CenteredMomentSecondCanonical.commonPart_eq_left _ _ hd.2.1 hd.2.2.symm⟩

theorem first_label_support (r : Source ι a b) (ha : 0 < a) (p : Labels r ha 1) :
    QRH.Record1252270103KernelMass.primeSupport p.val.1 =
      QRH.Record1252270103KernelMass.primeSupport p.val.2 :=
  (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2

theorem first_label_cubeFree (r : Source ι a b) (ha : 0 < a) (p : Labels r ha 1) :
    Packet.CubeFreeCommon p.val.1 p.val.2 := by
  intro P
  have hf := label_cube_free r ha 1 p
  have hd := commonLabels_data _ _ p.val.1 p.val.2 p.property
  have h1 := CenteredMomentCanonicalFirst.leftExponent_pos p.val.1 p.val.2 P
  have h2 := CenteredMomentCanonicalFirst.rightExponent_pos p.val.1 p.val.2 P
  have hl := (KernelIdeal.powerFree_iff_valuations hd.1).mp hf.1 P.val
  have hr := (KernelIdeal.powerFree_iff_valuations hd.2.1).mp hf.2 P.val
  simp only [QRH.Record1252270103KernelMass.valuation,
    factorization_eq_count] at hl hr
  unfold CenteredMomentCanonicalFirst.leftExponent CenteredMomentCanonicalFirst.rightExponent
    CenteredExceptionalCount.valuation at *
  omega

/-- The two Seam A leaves at the frame plain-length cap `L + 1 = 4` (root lengths `≤ Z³`). -/
theorem frame_leaves {D : StepData} (G : StepGates D) (Lplain : ℝ) (hL : 4 ≤ Lplain)
    (hleaf : PricedPackedSource D.price D.Hmin (D.Hmax + 1) Lplain)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    PricedPackedSource D.price D.Hmin (D.Hmax + 1) (3 + 1) ∧
      PricedPackedSource (nativePrice (3/4) (by norm_num)) D.Hmin (D.Hmax + 1) (3 + 1) := by
  obtain ⟨h0, h1⟩ := envelope_range G
  refine ⟨PricedPackedSource.mono (fun _ _ _ _ => le_rfl) le_rfl le_rfl (by norm_num; linarith)
    hleaf, native_priced_source hβ _ _ _ h0 h1⟩

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
