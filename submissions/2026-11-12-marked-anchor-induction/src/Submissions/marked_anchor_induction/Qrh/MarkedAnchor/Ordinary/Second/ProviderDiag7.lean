/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: the structural caps of `rootChoice` (twist norm, family conductor, selection width, child scale).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag6
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderChoice
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderScales
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedChildCaps
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedConductorCaps

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
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
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
open ActualEisensteinCubic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalDyadicAssembly MixedFirstRetainedFixed MixedFirstCommonSum

local instance (priority := 2000) instDecEqSubtypeProvDiag7 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-! ### Twist norm and the family conductor cap -/

theorem tau_norm_le (G opp : Id) (hG : G ≠ 0) (E : Finset (CommonIndex G opp)) (τ η : Character)
    (hmod : τ.modulus = η.modulus*Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*
      Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex G opp => P.val) E*activeConductor G opp}) :
    (τ.modulus.absNorm:ℝ) ≤ (η.modulus.absNorm:ℝ)*
      (Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*((G.absNorm:ℝ)*(G.absNorm:ℝ)) := by
  have hgen : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) =
      (Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex G opp => P.val) E}) : ℝ) := by
    rw [← ActualEisensteinCubic.primeSubsetGenerator_norm_sq, eisEmbedding_norm_sq_eq_absNorm_span]
  have h1 := primeSet_norm_le G opp hG E
  have h2 := active_norm_le G opp hG
  rw [hgen] at h1
  rw [hmod, ← Ideal.span_singleton_mul_span_singleton]
  simp only [map_mul, Nat.cast_mul]
  have h0 : (0:ℝ) ≤ (η.modulus.absNorm:ℝ)*
      (Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm := by positivity
  have := mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc _ = ((η.modulus.absNorm:ℝ)*
      (Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm)*
      ((Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex G opp => P.val) E}) : ℝ)*
        (Ideal.absNorm (Ideal.span {activeConductor G opp}) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this h0

/-- The fixed part of the conductor cost. -/
def cfix : ℝ := (CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*
  (Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem cfix_nonneg : 0 ≤ cfix := by unfold cfix; positivity

theorem fcc_eq (σ : Character) :
    MixedInnerExceptionalPair.fixedConductorCost σ = (σ.modulus.absNorm:ℝ)*cfix := by
  unfold MixedInnerExceptionalPair.fixedConductorCost cfix; ring

/-- The family conductor budget of a source with pool cap `≤ Z^8`. -/
theorem family_cap {ι' : Type*} [Fintype ι'] (r : Source ι' (1/4) (9/4)) (σ : Character)
    (radius Z X1 X2 X4 : ℝ) (hZ : 1 < Z) (hσ : (σ.modulus.absNorm:ℝ) ≤ X1)
    (hR : (r.R.absNorm:ℝ) ≤ X2) (hpool : poolCap r ≤ Z^(8:ℝ)) (hr0 : 0 ≤ radius)
    (hrad : radius ≤ X4) :
    familyConductorBudget r σ radius ≤ 4*(X1*cfix)*X2*(Z^(8:ℝ))^2*Z^(16:ℝ)*X4 := by
  have hpn := RepairedConductorCaps.pool_norm_cap r Z hZ hpool
  have hpc0 := poolCap_nonneg r
  have hpn0 : 0 ≤ MixedInnerExceptionalPair.poolNorm r :=
    Finset.sum_nonneg (fun I _ => Nat.cast_nonneg _)
  have hX1 : 0 ≤ X1 := (Nat.cast_nonneg _).trans hσ
  have hR0 : (0:ℝ) ≤ (r.R.absNorm:ℝ) := Nat.cast_nonneg _
  have hc := cfix_nonneg
  have hX2 : 0 ≤ X2 := hR0.trans hR
  have hz0 : 0 ≤ Z := by linarith
  unfold familyConductorBudget
  rw [fcc_eq]
  gcongr

/-! ### The selection of `rootChoice` -/

section sel
variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {Wsl : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

theorem selOf_card_le (d : RootInput G M H hH κ Wsl N Holes ε Z Kslot η η₀) (hε : 0 < ε)
    (ms : ℝ) (hm : 0 ≤ ms) (hmesh : ∀ i, d.w i ≤ ms) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (Nm : ℕ) (hNm : Fintype.card κ ≤ Nm) :
    Fintype.card (selOf d hε ms hm hmesh C B) ≤ Nm := by
  rw [Fintype.card_coe]
  refine (Finset.card_le_univ _).trans ?_
  rw [Fintype.card_coe]
  exact (Finset.card_le_univ _).trans hNm

theorem selOf_width (d : RootInput G M H hH κ Wsl N Holes ε Z Kslot η η₀) (hε : 0 < ε)
    (ms : ℝ) (hm : 0 ≤ ms) (hmesh : ∀ i, d.w i ≤ ms) (hms : ms ≤ mesh G ε) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (Nm : ℕ) (hNm : Fintype.card κ ≤ Nm) :
    slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (selOf d hε ms hm hmesh C B) ≤
      (2:ℝ)^Nm*Z^(uMax G ε (∑ i, d.w i)) := by
  have hZ1 := d.one_lt_Z
  have hz : 0 < Z := zero_lt_one.trans hZ1
  obtain ⟨-, -, -, -, hP⟩ := d.hcanonical
  set J := selOf d hε ms hm hmesh C B with hJ
  have hsw : slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) J =
      (2:ℝ)^(Fintype.card J)*Z^(∑ j : J, d.w j.val.val) := by
    unfold slotWidth
    calc (∏ j : J, 2*(allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val)
        = ∏ j : J, (2*Z^(d.w j.val.val)) :=
          Finset.prod_congr rfl (fun j _ => by rw [show (allocatedLiveSource d.root (by norm_num)
            d.cover C B).P j.val = d.root.P j.val.val from rfl, congrFun hP j.val.val])
      _ = (2:ℝ)^(Fintype.card J)*∏ j : J, Z^(d.w j.val.val) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ = _ := by rw [Real.rpow_sum_of_pos hz]
  rw [hsw]
  -- the selected width
  have hsum : (∑ j : J, d.w j.val.val) ≤ uMax G ε (∑ i, d.w i) := by
    have e1 : (∑ j : J, d.w j.val.val) = ∑ j ∈ J, d.w j.val :=
      Finset.sum_coe_sort J (fun j : liveIndices B.val => d.w j.val)
    rw [e1, hJ]
    unfold selOf
    rw [Finset.sum_map]
    simp only [Function.Embedding.coe_subtype]
    have hlw := d.liveWidth_le C B Finset.univ
    have hlw0 := d.liveWidth_nonneg C B Finset.univ
    have hS := d.width_bounds
    have hselS := sel_bounds G hε d.hface
    have hmG := (mesh_spec G ε hε).1
    by_cases hL : widthFloor G ε < Second.Selection.liveWidth (Finset.univ : Finset (liveIndices B.val))
        (fun i => d.w i.val)
    · have h := Second.Selection.chosen_large (Finset.univ : Finset (liveIndices B.val))
        (fun i => d.w i.val) (D.sel ε) (widthFloor G ε) ms hm (fun i => d.hw _) (fun i => hmesh _)
        (d.sel_live hε C B Finset.univ) hL
      exact selection_le_uMax G hε hlw0 hlw hS.2 h.2.1 hms
    · rw [Second.Selection.chosen_small (Finset.univ : Finset (liveIndices B.val))
        (fun i => d.w i.val) (D.sel ε) (widthFloor G ε) ms hm (fun i => d.hw _) (fun i => hmesh _)
        (d.sel_live hε C B Finset.univ) (le_of_not_gt hL)]
      simp only [Finset.sum_empty]
      unfold uMax; linarith [hselS.1]
  have hc := selOf_card_le d hε ms hm hmesh C B Nm hNm
  apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hc)
    (Real.rpow_le_rpow_of_exponent_le hZ1.le hsum) (Real.rpow_nonneg hz.le _) (by positivity)

/-- The child scale of a retained block: `1/2 ≤ K ≤ Z^{33}` (`firstRadius_le`). -/
theorem childScale_bounds (d : RootInput G M H hH κ Wsl N Holes ε Z Kslot η η₀) (hε : 0 < ε)
    (p : Labels d.root (by norm_num) 1) (E : Finset (CommonIndex p.val.1 p.val.2)) (n : ℤ)
    (hn : n ∈ retainedIndices (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z (cutoffLoss G N ε)))
    (hdy : 1/2 ≤ dyadicScale n) :
    1/2 ≤ childScale Z (cutoffLoss G N ε) n ∧ childScale Z (cutoffLoss G N ε) n ≤ Z^(33:ℝ) := by
  have hZ1 := d.one_lt_Z
  have hz : 0 < Z := zero_lt_one.trans hZ1
  have hZ5 := d.hZ
  have hκ1 := RepairedChildCaps.cutoff_le_one G N ε hε
  have hκ0 : 0 ≤ cutoffLoss G N ε := by
    unfold cutoffLoss; have := (internal_spec G N ε hε).1; positivity
  rw [childScale_eq Z _ hZ1 n]
  have hR := firstRadius_le d (by norm_num) p E (cutoffLoss G N ε) (by linarith)
  have hd := dyad_le_of_retained _ n hn
  have hZk1 : 1 ≤ Z^(cutoffLoss G N ε) := Real.one_le_rpow hZ1.le hκ0
  have hZk : Z^(cutoffLoss G N ε) ≤ Z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1.le hκ1
  constructor
  · nlinarith
  · have e : Z^(33:ℝ) = Z^(31:ℝ)*Z*Z := by
      rw [show (33:ℝ) = 31+1+1 by norm_num, Real.rpow_add hz, Real.rpow_add hz, Real.rpow_one]
    rw [e]
    have h31 := Real.rpow_nonneg hz.le (31:ℝ)
    have h1 : dyadicScale n ≤ 4*Z^(31:ℝ) := hd.trans (by linarith)
    calc dyadicScale n * Z^(cutoffLoss G N ε) ≤ (4*Z^(31:ℝ))*Z :=
          mul_le_mul h1 hZk (by linarith) (by positivity)
      _ = (Z^(31:ℝ)*Z)*4 := by ring
      _ ≤ (Z^(31:ℝ)*Z)*Z := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
end sel

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
