/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, final assembly: `contrary_raw_side_provider` from the two suppliers.

* `DiagSupply G`: the diagonal half of every retained first block at the concrete
  `rootChoice`, budget share `1/2`, for every height exponent / seminorm set / side constant above
  the supplier's, at every multiplicity `0 ≤ Mc ≤ Z^{ε/4}`.
* `GeoSupply G`: the geometry `GeometryAt` of every residual split with `capRes ≥ 1`
  of every retained first block, both sides, with a box constant `cb` and radical exponent `Bmask`
  fixed before `Z`.
* `contrary_raw_side_provider`: `4 ≤ Lplain`, the step leaf, `DiagSupply G` and `GeoSupply G` give
  `ContraryRawSideProvider G`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderScales

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second QRH.SilDensitySplit.CubeFree.Second.Provider
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectorLocalization CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentFirstMixedAllowance
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentNaturalFixedRaySource
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFiniteProfileExceptional
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedFirstCommonSum MixedFirstPaidRetained
open MixedInnerExceptionalBlock MixedFirstExceptionalWindow MixedFirstRetainedFixed
open RepairedRawContext RepairedSourceSideSupply Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderFin {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-! ### Internal-character data of the provider's `Q` -/

theorem iq_ne_zero (Q : Id) [NeZero Q] (η₀ : Character) : internalQ Q η₀ ≠ 0 :=
  internalQ_ne_zero Q (NeZero.ne Q) η₀

theorem iq_ne_top (Q : Id) (hQt : Q ≠ ⊤) (η₀ : Character) : internalQ Q η₀ ≠ ⊤ :=
  internalQ_ne_top Q hQt η₀

theorem iq_le72 (Q : Id) (hQ72 : Q ≤ Ideal.span {(72:O)}) (η₀ : Character) :
    internalQ Q η₀ ≤ Ideal.span {(72:O)} := le_trans inf_le_left hQ72

/-! ### The two suppliers -/

/-- **The diagonal supplier.** -/
def DiagSupply {D : StepData} (G : StepGates D) : Prop :=
  ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ meshF : ℝ, ∀ hm0 : 0 < meshF, meshF ≤ mesh G ε →
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H),
  ∀ (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2),
  ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Id) [NeZero Q],
    Q ≠ ⊤ → Q ≤ Ideal.span {(72:O)} → Q ≤ M → Q ≤ η₀.modulus →
  ∃ J₀ : ℕ, ∃ ctl₀ : Finset (ℕ × ℕ), ∃ C₀ : ℝ,
    ∀ (J : ℕ) (control : Finset (ℕ × ℕ)) (Cside : ℝ), J₀ ≤ J → ctl₀ ⊆ control → C₀ ≤ Cside →
    ∀ᶠ Z : ℝ in atTop, ∀ k : RootShape α,
    ∀ d : RootInput G M H hH (RootSlot k) W (Fintype.card α) (2 * Fintype.card α) ε Z
      (RestoredRootSource.slotBound W hW.continuous hWs) η η₀,
    d.Kroot = bΦ * Z → ∀ hmesh : (∀ i, d.w i ≤ meshF),
    ∀ p : Labels d.root (by norm_num) 1, ∀ E ∈ inactiveSubsets p.val.1 p.val.2,
    ∀ n : Blocks (effectiveScale p.val.1 p.val.2 E d.Kroot)
        (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z (cutoffLoss G (Fintype.card α) ε))
        (Z^(8:ℝ)/p.val.1.absNorm) (Z^(8:ℝ)/p.val.2.absNorm),
      1/2 ≤ dyadicScale (n 1) →
    ∀ Mc : ℝ, 0 ≤ Mc → Mc ≤ Z^(ε/4) →
    ∀ (hML : MultBound d.root (by norm_num) d.cover p.val.1 (selOf d hε meshF hm0.le hmesh p.val.1)
        (childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1))
        (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.1 B)
          (selOf d hε meshF hm0.le hmesh p.val.1 B)) (fun _ => Mc))
      (hMR : MultBound d.root (by norm_num) d.cover p.val.2 (selOf d hε meshF hm0.le hmesh p.val.2)
        (childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1))
        (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.2 B)
          (selOf d hε meshF hm0.le hmesh p.val.2 B)) (fun _ => Mc)),
    DiagHalf d.root (by norm_num) (by norm_num) d.cover η p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns d.root)
        (sourceCoefficient d.root (by norm_num) 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns d.root)
        (sourceCoefficient d.root (by norm_num) 1)) p).2 E
      (childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1))
      (amplitude d.root d.t₀ d.V J control Cside) Z (3*ε) J
      (rootChoice d hε meshF hm0.le hmesh Q p.val.1 p.val.2
        (childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1)) meshF Mc hML hMR) (1/2)

/-- **The geometric supplier.** -/
def GeoSupply {D : StepData} (G : StepGates D) : Prop :=
  ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ meshF : ℝ, ∀ hm0 : 0 < meshF, meshF ≤ mesh G ε →
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H),
  ∀ (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2),
  ∀ bΦ : ℝ, ∀ hbΦ : 2 ≤ bΦ, ∀ (η η₀ : Character) (Q : Id) [NeZero Q],
    ∀ hQt : Q ≠ ⊤, ∀ hQ72 : Q ≤ Ideal.span {(72:O)}, ∀ hQM : Q ≤ M, Q ≤ η₀.modulus →
  ∃ cb Bmask : ℝ, ∃ hcb : 0 ≤ cb, ∃ hBmask : 0 ≤ Bmask,
    ∀ᶠ Z : ℝ in atTop, ∀ k : RootShape α,
    ∀ d : RootInput G M H hH (RootSlot k) W (Fintype.card α) (2 * Fintype.card α) ε Z
      (RestoredRootSource.slotBound W hW.continuous hWs) η η₀,
    d.Kroot = bΦ * Z → ∀ hmesh : (∀ i, d.w i ≤ meshF),
    ∀ p : Labels d.root (by norm_num) 1, ∀ E ∈ inactiveSubsets p.val.1 p.val.2,
    ∀ n : Blocks (effectiveScale p.val.1 p.val.2 E d.Kroot)
        (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z (cutoffLoss G (Fintype.card α) ε))
        (Z^(8:ℝ)/p.val.1.absNorm) (Z^(8:ℝ)/p.val.2.absNorm),
      1/2 ≤ dyadicScale (n 1) →
    (∀ B, allocWeight d.root p.val.1 B ≠ 0 → 1 ≤ capRes d p.val.1 B (selOf d hε meshF hm0.le hmesh p.val.1 B) →
      GeometryAt D G ε η (residFin d p.val.1 B (selOf d hε meshF hm0.le hmesh p.val.1 B))
        (by show (0:ℝ) < 1/4; norm_num)
        (frameOf d p.val.1 B (selOf d hε meshF hm0.le hmesh p.val.1 B) hW hWs bΦ hbΦ Q hQM
          (iq_ne_zero Q η₀) (iq_ne_top Q hQt η₀) (iq_le72 Q hQ72 η₀) hε Bmask hBmask meshF hmesh
          (Packet.firstPacked p.val.1 p.val.2 (commonLabels_supported (activeSource
            (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1)) p).1 E)
          (Packet.firstPacked_ne_zero p.val.1 p.val.2 (commonLabels_supported (activeSource
            (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1)) p).1 E)
          (Real.logb Z (16 * childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1) *
            (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.1 B)
              (selOf d hε meshF hm0.le hmesh p.val.1 B))^4)))
        (16 * childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1) *
          (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.1 B)
            (selOf d hε meshF hm0.le hmesh p.val.1 B))^4)
        (frequencyRadius (Tfreq d p.val.1 B (selOf d hε meshF hm0.le hmesh p.val.1 B)
          (16 * childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1) *
            (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.1 B)
              (selOf d hε meshF hm0.le hmesh p.val.1 B))^4)) Z meshF)
        (capRes d p.val.1 B (selOf d hε meshF hm0.le hmesh p.val.1 B))
        (∑ j : selOf d hε meshF hm0.le hmesh p.val.1 B, d.w j.val.val) cb) ∧
    (∀ B, allocWeight d.root p.val.2 B ≠ 0 → 1 ≤ capRes d p.val.2 B (selOf d hε meshF hm0.le hmesh p.val.2 B) →
      GeometryAt D G ε η (residFin d p.val.2 B (selOf d hε meshF hm0.le hmesh p.val.2 B))
        (by show (0:ℝ) < 1/4; norm_num)
        (frameOf d p.val.2 B (selOf d hε meshF hm0.le hmesh p.val.2 B) hW hWs bΦ hbΦ Q hQM
          (iq_ne_zero Q η₀) (iq_ne_top Q hQt η₀) (iq_le72 Q hQ72 η₀) hε Bmask hBmask meshF hmesh
          (Packet.firstPackedRight p.val.1 p.val.2 (commonLabels_supported (activeSource
            (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1)) p).1 E)
          (Packet.firstPackedRight_ne_zero p.val.1 p.val.2 (commonLabels_supported (activeSource
            (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1)) p).1 E)
          (Real.logb Z (16 * childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1) *
            (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.2 B)
              (selOf d hε meshF hm0.le hmesh p.val.2 B))^4)))
        (16 * childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1) *
          (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.2 B)
            (selOf d hε meshF hm0.le hmesh p.val.2 B))^4)
        (frequencyRadius (Tfreq d p.val.2 B (selOf d hε meshF hm0.le hmesh p.val.2 B)
          (16 * childScale Z (cutoffLoss G (Fintype.card α) ε) (n 1) *
            (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.2 B)
              (selOf d hε meshF hm0.le hmesh p.val.2 B))^4)) Z meshF)
        (capRes d p.val.2 B (selOf d hε meshF hm0.le hmesh p.val.2 B))
        (∑ j : selOf d hε meshF hm0.le hmesh p.val.2 B, d.w j.val.val) cb)

/-! ### Helpers -/

theorem multBound_of_divisor {ι : Type*} [Fintype ι] {a b : ℝ} (N : ℕ) (Cexp δ Cδ Z : ℝ)
    (hZ : 1 ≤ Z) (hδ : 0 < δ)
    (hC : ∀ r : Id, r ≠ ⊥ → (Ideal.absNorm r : ℝ) ≤ Z ^ Cexp →
      ((IdealMobiusDivisorSum.idealDivisors r).card : ℝ) ^ N ≤ Cδ * Z ^ δ)
    (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (K : ℝ) (W : actualAllocations (tuplePools s) G → ℝ)
    (hJ : ∀ B, Fintype.card (J B) ≤ N) (hrad : ∀ B, 16 * K * W B^4 ≤ Z ^ Cexp) :
    MultBound s hb cover G J K W (fun _ => max Cδ 1 * Z ^ δ) := by
  intro B
  refine ⟨by have := Real.rpow_nonneg (zero_le_one.trans hZ) δ; positivity, ?_⟩
  intro z hz hzn
  exact selected_mult_le (allocatedLiveSource s hb cover G B) (J B) N (hJ B) Cexp δ Cδ Z hZ hδ.le
    hC z hz (hzn.trans (hrad B))

theorem labelConst_le {κ : Type*} [Fintype κ] {a b : ℝ} (s : Source κ a b) (G : Id) (N : ℕ)
    (Mc Kl nB Mall : ℝ)
    (hB : ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) ≤ nB)
    (hMall : (∏ i, s.M i) ≤ Mall) (hκN : Fintype.card κ ≤ N) (hMc0 : 0 ≤ Mc) (hKl0 : 0 ≤ Kl) :
    labelConst s G N Mc Kl ≤
      nB^2 * (Mall^2 * (pcMass * Mall^2 * (256:ℝ)^N) * ((2:ℝ)^N * Mc) *
        ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ)) * Kl * (4:ℝ)^N) := by
  unfold labelConst
  have hm0 : 0 ≤ (∏ i, s.M i) := Finset.prod_nonneg fun i _ => zero_le_one.trans (s.hM i)
  have hpc := pcMass_nonneg
  have h4 : (4:ℝ)^(Fintype.card κ) ≤ 4^N := pow_le_pow_right₀ (by norm_num) hκN
  have hB0 : (0:ℝ) ≤ ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) :=
    Nat.cast_nonneg _
  have hM2 : (∏ i, s.M i)^2 ≤ Mall^2 := pow_le_pow_left₀ hm0 hMall 2
  apply mul_le_mul (pow_le_pow_left₀ hB0 hB 2) _ (by positivity) (by positivity)
  apply mul_le_mul _ h4 (by positivity) (by positivity)
  apply mul_le_mul_of_nonneg_right _ hKl0
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul hM2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hpc)
    (by positivity)) (by positivity) (by positivity)

section rootfacts
variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

theorem rootAmp_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (J : ℕ)
    (S : Finset (ℕ × ℕ)) :
    rootAmp d J S ≤ (sourceControl S d.root.W₁ * sourceControl S d.root.W₂)^2 *
      (MixedFirstProfileEnvelope.height d.t₀ d.V d.root.t₁ d.root.t₂)^J := by
  unfold rootAmp MixedFirstProfileEnvelope.height
  have hV := d.hV
  have hpi := Real.pi_pos
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  have h1 : |d.root.t₁ / (2 * Real.pi)| ≤ ‖d.root.t₁‖ := by
    rw [abs_div, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    exact div_le_self (abs_nonneg _) (by nlinarith [Real.pi_gt_three])
  have h2 : |d.root.t₂ / (2 * Real.pi)| ≤ ‖d.root.t₂‖ := by
    rw [abs_div, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    exact div_le_self (abs_nonneg _) (by nlinarith [Real.pi_gt_three])
  linarith

theorem root_Mall_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (hκN : Fintype.card κ ≤ N) :
    (∏ i, d.root.M i) ≤ (max 1 Kslot)^N := by
  calc (∏ i, d.root.M i) ≤ ∏ _i : κ, max 1 Kslot :=
        Finset.prod_le_prod₀ (fun i _ => zero_le_one.trans (d.root.hM i))
          (fun i _ => (d.hM i).trans (le_max_right _ _))
    _ = (max 1 Kslot)^(Fintype.card κ) := by rw [Finset.prod_const, Finset.card_univ]
    _ ≤ (max 1 Kslot)^N := pow_le_pow_right₀ (le_max_left _ _) hκN

theorem root_alloc_le_of (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (hC0 : C ≠ 0) (hN : (Ideal.absNorm C : ℝ) ≤ Z^(8:ℝ)) (hκN : Fintype.card κ ≤ N) (Ca δ : ℝ)
    (hdiv : ∀ Z' : ℝ, 1 ≤ Z' → ∀ r : Id, r ≠ ⊥ → (Ideal.absNorm r : ℝ) ≤ Z' ^ (8:ℝ) →
      ((IdealMobiusDivisorSum.idealDivisors r).card : ℝ) ^ (N+2) ≤ Ca * Z' ^ δ) :
    ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ) ≤ Ca * Z^δ := by
  have hZ1 := d.one_lt_Z
  have hτ1 : (1:ℝ) ≤ (IdealMobiusDivisorSum.idealDivisors C).card := by
    have : 0 < (IdealMobiusDivisorSum.idealDivisors C).card :=
      Finset.card_pos.mpr ⟨_, (IdealMobiusDivisorSum.mem_idealDivisors hC0).mpr dvd_rfl⟩
    exact_mod_cast this
  have hcard := alloc_card_le (tuplePools d.root) C hC0
  rw [Finset.card_univ, Fintype.card_coe]
  calc ((actualAllocations (tuplePools d.root) C).card : ℝ)
      ≤ ((IdealMobiusDivisorSum.idealDivisors C).card : ℝ) ^ Fintype.card (κ ⊕ Fin 2) := by
        exact_mod_cast hcard
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors C).card : ℝ) ^ (N+2) := by
        apply pow_le_pow_right₀ hτ1
        rw [Fintype.card_sum, Fintype.card_fin]; omega
    _ ≤ Ca * Z^δ := hdiv Z hZ1.le C hC0 hN

/-- The label side constant of the provider. -/
def labelSide (Kslot Ca Cm Cmax : ℝ) (N : ℕ) : ℝ :=
  2 * (Ca^2 * (((max 1 Kslot)^N)^2 * (pcMass * ((max 1 Kslot)^N)^2 * (256:ℝ)^N) *
    ((2:ℝ)^N * max Cm 1) * ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ)) *
    (Cmax / (1/4:ℝ)^2) * (4:ℝ)^N))

/-- **The label constant inequality** `labelConst ≤ ½·A·Z^{3ε}`. -/
theorem labelConst_final (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (hε : 0 < ε) (C : Id)
    (hC0 : C ≠ 0) (hN8 : (Ideal.absNorm C : ℝ) ≤ Z^(8:ℝ)) (hκN : Fintype.card κ ≤ N)
    (Ca Cm Cmax : ℝ) (hCa : 0 ≤ Ca) (hCmax : 0 ≤ Cmax)
    (hdiv : ∀ Z' : ℝ, 1 ≤ Z' → ∀ r : Id, r ≠ ⊥ → (Ideal.absNorm r : ℝ) ≤ Z' ^ (8:ℝ) →
      ((IdealMobiusDivisorSum.idealDivisors r).card : ℝ) ^ (N+2) ≤ Ca * Z' ^ (ε/8))
    (J : ℕ) (control : Finset (ℕ × ℕ)) (Cside : ℝ) (hside : labelSide Kslot Ca Cm Cmax N ≤ Cside) :
    labelConst d.root C N (max Cm 1 * Z^(ε/8)) (Cmax / (1/4:ℝ)^2 * rootAmp d J control * Z^(2*ε)) ≤
      (1/2) * amplitude d.root d.t₀ d.V J control Cside * Z^(3*ε) := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  set u := Z^(ε/8) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hZ1.le (by positivity)
  have hu0 : 0 ≤ u := zero_le_one.trans hu1
  have hrA0 : 0 ≤ rootAmp d J control := by
    unfold rootAmp
    have := sourceControl_nonneg control d.root.W₁
    have := sourceControl_nonneg control d.root.W₂
    have hV := d.hV
    positivity
  have hZ2 : 0 ≤ Z^(2*ε) := Real.rpow_nonneg hZ0.le _
  have hMc0 : 0 ≤ max Cm 1 * u := by have := le_max_right Cm 1; positivity
  have hKl0 : 0 ≤ Cmax / (1/4:ℝ)^2 * rootAmp d J control * Z^(2*ε) := by positivity
  have h1 := labelConst_le d.root C N (max Cm 1 * u) (Cmax / (1/4:ℝ)^2 * rootAmp d J control * Z^(2*ε))
    (Ca * u) ((max 1 Kslot)^N) (root_alloc_le_of d C hC0 hN8 hκN Ca (ε/8) hdiv)
    (root_Mall_le d hκN) hκN hMc0 hKl0
  refine h1.trans ?_
  have hAmp := rootAmp_le d J control
  have hS0 : 0 ≤ labelSide Kslot Ca Cm Cmax N := by
    unfold labelSide; have := pcMass_nonneg; have := le_max_right Cm 1; positivity
  have h8 : Z^(3*ε) = u^8 * Z^(2*ε) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]; norm_num; ring_nf
  have hu38 : u^3 ≤ u^8 := pow_le_pow_right₀ hu1 (by norm_num)
  have e1 : (Ca * u)^2 * (((max 1 Kslot)^N)^2 * (pcMass * ((max 1 Kslot)^N)^2 * (256:ℝ)^N) *
      ((2:ℝ)^N * (max Cm 1 * u)) * ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ)) *
      (Cmax / (1/4:ℝ)^2 * rootAmp d J control * Z^(2*ε)) * (4:ℝ)^N) =
      (labelSide Kslot Ca Cm Cmax N / 2) * rootAmp d J control * (u^3 * Z^(2*ε)) := by
    unfold labelSide; ring
  rw [e1, h8]
  unfold amplitude
  have hsc : 0 ≤ (sourceControl control d.root.W₁ * sourceControl control d.root.W₂)^2 *
      (MixedFirstProfileEnvelope.height d.t₀ d.V d.root.t₁ d.root.t₂)^J := hrA0.trans hAmp
  calc labelSide Kslot Ca Cm Cmax N / 2 * rootAmp d J control * (u^3 * Z^(2*ε))
      ≤ Cside / 2 * ((sourceControl control d.root.W₁ * sourceControl control d.root.W₂)^2 *
          (MixedFirstProfileEnvelope.height d.t₀ d.V d.root.t₁ d.root.t₂)^J) * (u^8 * Z^(2*ε)) := by
        apply mul_le_mul (mul_le_mul (by linarith) hAmp hrA0 (by linarith)) _ (by positivity)
          (by have := hS0.trans hside; positivity)
        exact mul_le_mul_of_nonneg_right hu38 hZ2
    _ = _ := by ring

end rootfacts

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
