/- Copyright (c) 2026 Sil. Apache-2.0.
Actual generic-root large nonexceptional retained supplier. The normalized
Uses the common Hsource=Z^8 required by the grouped exceptional supplier.
Sharp active norm/common bounds remain Z^2 inside. The normalized
block input is supplied INSIDE by RepairedLargeBlock, then sharp raw support
and actual harmonic mass are applied. No energy premise.
-/
import Candidate.Feedback.FourthPower.RepairedLargeBlock
import Candidate.Feedback.FourthPower.RepairedFirstPoint

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedActualLargeRetained
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge RayFourExpansion
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentSourceMass CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockHarmonicMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiveNormalization
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedInnerExceptionalBlock MixedFirstExceptionalNormalization MixedOriginalNormCap
open OuterFreshSource OuterFreshSelectedWindow OuterFreshSelected OuterFreshConsumer OuterFreshNonexceptionalBlock
open OuterFreshAllocationMass OuterFreshSelectedKernel
open OuterFreshCutoffAllowance
open RepairedRootParameters RepairedRawContext RepairedFirstPoint RepairedCapEvent RepairedRootCaps
open RepairedDescendantCaps RepairedChildCaps RepairedRawReference RepairedRawRetained RepairedGroupedConsumer
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}

local instance (priority := 2000) {ι : Type u} [Fintype ι]
    {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀}
    (p : Point d) : DecidableEq p.Index := Classical.decEq _

def RetainedBound {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
    {η η₀ : Character} {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀}
    (p : Point d) (hε : 0 < ε) (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) (Q : Id) : Prop :=
  ∀ (u : Id) (L : Finset p.Index), p.large L → ∀ x : Frozen (p.data hε u L),
    MixedSupplierFourthRow.frozenWeight (p.data hε u L) x ≠ 0 →
  ∀ seed : Id, Squarefree seed → u = frozenProduct (p.data hε u L) x * seed →
  ∀ (ξ χ₀ : RayCharacter) (tp : ℝ),
    ‖selectedSum (p.data hε u L) x p.tau
      (fun y => fixedPart false (p.data hε u L) x y (p.residual hε u L x) seed p.tau ξ χ₀ Q tp ballProfile
        p.scale (p.cutoff hε u L x) Z (cutoffLoss N ε) (Z^(8:ℝ)))‖ ≤
    C * MixedSelectedVolume.scale (p.data hε u L) *
      (firstReference (p.data hε u L) p.tau p.label.val.1 (sourceVolume d.root) *
        rawProfileRoot (p.residual hε u L x) *
        profileCore (p.residual hε u L x) Kslot N degree control d.t₀ tp d.V) *
      Z^(windowLoss ε) / (seed.absNorm:ℝ)

private theorem extra_paid (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    4*cutoffLoss N ε + artificialLoss N ε + 4*commonPower N ε + massLoss N ε ≤ stepN N ε := by
  have h := internal_losses_paid N ε hε
  have hp := (mesh_spec ε hε).1.le
  have hprod := mul_nonneg (Nat.cast_nonneg N) hp
  have hB : 2 ≤ seedCap N ε := by unfold seedCap; linarith
  have hδ := h.2.2.2.1
  have hs := step_pos N ε hε
  have he := h.2.2.2.2.trans (min_le_left _ _)
  nlinarith

theorem uniform_actual_large_retained
    (Index : Type v) [Fintype Index] (RootSlot : Index → Type u) [∀ k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀ k,Fintype.card (RootSlot k) ≤ N) (ε : ℝ) (hε : 0 < ε)
    (Wslot : ℝ → ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot ⊆ Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1 ≤ Kslot) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQM : Q ≤ M)
    (η η₀ : Character) (hQη₀ : Q ≤ η₀.modulus) :
    ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, ∀ k : Index,
      ∀ d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
      ∀ p : Point d, RetainedBound p hε degree control C Q := by
  obtain ⟨degree,control,hlarge⟩ := RepairedLargeBlock.uniform_generic_first_large_block M H hH
    Index RootSlot N Holes hcard ε hε Wslot hW hWs Kslot hKslot hβ Q hQt hQ72 hQM
  obtain ⟨Cb,hCb,hlarge⟩ := hlarge η₀ hQη₀
  have hloss := internal_losses_paid N ε hε
  obtain ⟨Cm,hCm,hmass⟩ := uniform_raw_retained_from_blocks (8:ℝ) 15 1 (massLoss N ε)
    (by norm_num) (by norm_num) (by norm_num) hloss.2.2.1
  refine ⟨degree,control,Cb*Cm,mul_pos hCb hCm,?_⟩
  filter_upwards [hlarge,hmass,eventually_event N ε hε] with Z hb hm hevent
  intro k d p u L hL x hx seed hseed hu ξ χ₀ tp
  let q := p.data hε u L
  let r := p.residual hε u L x
  let r₀ := p.unavoided hε u L x
  have hqP : ∀ i,0 < q.P i := fun i => zero_lt_one.trans_le (p.source.hP i)
  have hroot := hb.2 k d.chars d.w d.freq d.t₀ d.V d.R₀ d.hw d.hwm d.hV d.hfreq d.hholes
    d.root d.hcanonical d.hM d.hR d.hH d.hF d.hX₁ d.hX₂ d.hY₁ d.hY₂ d.hnorm d.cover
    η d.Kroot d.radial_pos d.hKcap d.hη d.root_capacity p.label p.inactive p.allocation p.frozen_nonzero
  have hblock := hroot p.tau p.modulus p.index p.retained u L hL x hx seed hseed hu
  have hsupp := commonLabels_supported _ _ _ p.label.property
  have hCD : CompletedGauss.primeSupport p.label.val.1 = CompletedGauss.primeSupport p.label.val.2 :=
    (commonLabels_data _ _ _ _ p.label.property).2.2
  have hsup := residual_support_caps M H hH d (hcard k) hevent p.label.val.1 p.allocation u L (p.selection hε L) x
  have hnorm : sourceNormCap r.P (9/4) r.T r.d ≤ Z^(2:ℝ) := hsup.2.2.2.1
  have hnorm8 : sourceNormCap r.P (9/4) r.T r.d ≤ Z^(8:ℝ) := hnorm.trans
    (Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by norm_num))
  have henv : secondSourceEnvelope r ≤ Z^(2:ℝ) := hsup.2.2.2.2.2
  have hk : 0 < p.scale := Real.rpow_pos_of_pos (zero_lt_one.trans d.one_lt_Z) _
  have hinv := child_inverse_cap M H hH d hε (hcard k) hevent.dimension p.label p.inactive p.index
  have hcuts := second_cutoff_caps r Z p.scale (cutoffLoss N ε) d.one_lt_Z hk
    (RepairedChildCaps.cutoff_le_one N ε hε) henv hinv
  have hrad : p.radius hε u L x ≤ Z^(15:ℝ) := hcuts.2.2.2
  let Base := firstReference q p.tau p.label.val.1 (sourceVolume d.root) * rawProfileRoot r *
    profileCore r Kslot N degree control d.t₀ tp d.V
  let exponent := 4*cutoffLoss N ε + windowLoss ε + artificialLoss N ε + 4*commonPower N ε
  let A := Cb*Base*Z^exponent
  have hBase : 0 ≤ Base := mul_nonneg
    (mul_nonneg (firstReference_nonneg q hqP p.tau p.label.val.1 (sourceVolume d.root)) (rawProfileRoot_nonneg r))
    (profileCore_nonneg r Kslot N degree control d.t₀ tp d.V (zero_le_one.trans hKslot) d.hV)
  have hA : 0 ≤ A :=
    mul_nonneg (mul_nonneg hCb.le hBase)
      (Real.rpow_nonneg (zero_lt_one.trans d.one_lt_Z).le _)
  have hpoint (p₂ : FixedLabel (fixedPool q x r seed)) (U : Finset (CommonIndex p₂.val.1 p₂.val.2))
      (n₂ : SourceBlocks p₂.val.1 p₂.val.2 U p.scale (p.radius hε u L x) (Z^(8:ℝ))) :
      Z^(stepN N ε) * ‖(heightCoeff p.tau tp p₂.val.1 * star (heightCoeff p.tau tp p₂.val.2)) *
        physicalAverage q x r seed p.tau ξ χ₀ Q p₂.val.1 p₂.val.2
          (commonLabels_supported _ _ _ p₂.property).1 (commonLabels_supported _ _ _ p₂.property).2 U
          tp (p.radius hε u L x) ballProfile p.scale (fun i => (n₂ i:ℤ))‖ ≤ A*pairWeight p₂.val.1 p₂.val.2 := by
    have hc := actual_fixed_common_norm_caps p.source (by norm_num) p.cover u L (p.selection hε L) x seed p₂
    have hfirstNorm := (allocated_size_caps d.root (by norm_num) d.cover p.label.val.1 p.allocation).2.2.2.trans
      (root_norm_cap_two M H hH d (hcard k) hevent.dimension)
    have hn := hblock p₂ ξ χ₀ U (fun i => (n₂ i:ℤ)) tp
    have hnormal : ‖normalization (r₀.X₁*r₀.X₂) r₀.P‖^2 = ‖normalization (r.X₁*r.X₂) r.P‖^2 := rfl
    have hrootFactor : rootFactor r₀ = rootFactor r := rfl
    have hangle (Rdecl : ℝ) : angleEnvelope r₀ 1 Kslot N degree control d.t₀ tp d.V Z Rdecl (windowLoss ε) =
        angleEnvelope r 1 Kslot N degree control d.t₀ tp d.V Z Rdecl (windowLoss ε) := rfl
    simp only [hnormal,hrootFactor,hangle] at hn
    have he := raw_block_of_normalized q x hqP r (by norm_num)
      (residual_matches p.source (by norm_num) p.cover u L (p.selection hε L) x) seed η p.tau ξ χ₀ Q
      p.label.val.1 p.label.val.2 hsupp.1 hsupp.2 hCD p.inactive d.Kroot (sourceVolume d.root) Z (cutoffLoss N ε)
      d.radial_pos (sourceVolume_pos d.root) d.one_lt_Z p.modulus p.index p₂.val.1 p₂.val.2
      (commonLabels_supported _ _ _ p₂.property).1 (commonLabels_supported _ _ _ p₂.property).2 U
      (fun i => (n₂ i:ℤ)) tp (p.radius hε u L x) (stepN N ε) Cb 2 (commonPower N ε)
      (windowLoss ε) (artificialLoss N ε) Kslot d.t₀ d.V hCb.le hloss.2.2.2.1.le
      (zero_le_one.trans hKslot) d.hV (hc.1.trans hfirstNorm) (hc.2.trans hfirstNorm) N degree control hn
    have hexp : 4*cutoffLoss N ε + windowLoss ε + artificialLoss N ε + 2*(2:ℝ)*commonPower N ε = exponent := by
      dsimp only [exponent]
      ring
    rw [hexp] at he
    convert he using 1 <;> first | rfl | (dsimp only [A,Base]; ring)
  have he := hm.2 p.Index q x hqP (1/4) (9/4) r (by norm_num)
    (residual_matches p.source (by norm_num) p.cover u L (p.selection hε L) x) seed hseed hnorm8 p.tau ξ χ₀ Q
    tp p.scale (p.cutoff hε u L x) (cutoffLoss N ε) (Z^(8:ℝ)) (stepN N ε) A hk
    (by simpa only [one_mul, Point.radius] using hrad) le_rfl hA hpoint
  let Bound := (Cb*Cm)*MixedSelectedVolume.scale q*Base/(seed.absNorm:ℝ)
  have hBound : 0 ≤ Bound := by
    have hs := (MixedSelectedVolume.scale_pos q hqP).le
    dsimp only [Bound]
    positivity
  have hcombined : Z^(stepN N ε) * ‖selectedSum q x p.tau
      (fun y => fixedPart false q x y r seed p.tau ξ χ₀ Q tp ballProfile p.scale (p.cutoff hε u L x)
        Z (cutoffLoss N ε) (Z^(8:ℝ)))‖ ≤
      Bound * Z^(windowLoss ε + (4*cutoffLoss N ε + artificialLoss N ε + 4*commonPower N ε + massLoss N ε)) := by
    have hp : Z^exponent*Z^(massLoss N ε) =
        Z^(windowLoss ε + (4*cutoffLoss N ε + artificialLoss N ε + 4*commonPower N ε + massLoss N ε)) := by
      rw [← Real.rpow_add (zero_lt_one.trans d.one_lt_Z)]
      congr 1
      dsimp only [exponent]
      ring
    apply he.trans_eq
    dsimp only [A,Bound]
    rw [← hp]
    ring
  have hfinal := cancel_gain Z (stepN N ε) (windowLoss ε)
    (4*cutoffLoss N ε + artificialLoss N ε + 4*commonPower N ε + massLoss N ε)
    _ Bound d.one_lt_Z hBound (extra_paid N ε hε) hcombined
  convert hfinal using 1 <;> first | rfl | (dsimp only [Bound,Base]; ring)

end
end Candidate.Feedback.FourthPower.RepairedActualLargeRetained
