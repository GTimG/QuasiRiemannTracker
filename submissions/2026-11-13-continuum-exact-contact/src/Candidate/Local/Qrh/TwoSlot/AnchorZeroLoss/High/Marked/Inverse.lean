/- Modified by Joseph Bebel (2026-11-12): actual source adapters for the
smaller-tolerance HIGH contract; original notices follow. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Pattern of Hailey Collet's `annular_rowwise_inverse_marked_energy` (row-wise heights through common
profiles, `naturalSlot_rowwise_energy`, Apache-2.0), with the anchor contract in place of the
native inverse energy. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.Slot
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.FiberBridge

/-!
# High.Marked.Inverse

`core_inverse_of_rect`: an inverse anchor contract `InverseRectSource canonicalFamily ρ mesh εm`
gives the marked inverse moment on core fibers, for every free width `x` with
`ρ.Admissible x (∑ wr) 1`, uniformly (constants before the scale):
* row-wise heights `t u` by HC's common-profile interpolation (`naturalSlot_rowwise_energy`, nodes
  `commonProfile W j`, `j ≤ card Slot`);
* at a node height each core slot is `c_j · directSlot` of the ray-twisted canonical class
  (`node_slot_eq`), so the slot vector lies in the fixed-ray class `canonicalSlotsRay W'_j (33/50) rayM' G' le_rfl`
  (ray data of the twist, fixed before the scale);
* the polynomial of `coreFamily` is the one of `momentData (cleanWholeBase label)`;
* `FiberBridge.detector_inverse_of_rect` for each node and label.
No slot separation is needed: the anchor contract admits overlapping canonical pools.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount Cycle61Moment
open Qrh.MarkedAnchor.Interface Qrh.TwoSlot.AnchorZeroLoss.High
local notation "O" => HeckeFamily.O
local instance markedInverseQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- `‖c · z‖² = c² ‖z‖²` for products of slots with a common real factor. -/
theorem prod_const_mul_sq {ι : Type*} (S : Finset ι) (c : ℝ) (A : ℂ) (f : ι → ℂ) :
    ‖A * ∏ s ∈ S, ((c : ℂ) * f s)‖^2 = (c^2)^S.card * ‖A * ∏ s ∈ S, f s‖^2 := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, mul_left_comm, norm_mul, mul_pow, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, ← pow_mul, ← pow_mul, pow_mul', sq_abs, mul_comm 2]
  ring

/-- **Marked inverse moment on core fibers from one inverse anchor contract.** -/
theorem core_inverse_of_rect {ρ : Contract.AnchorRect} {meshI εm : ℝ}
    (hs : Contract.InverseRectSource Contract.canonicalFamily ρ meshI εm)
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ : Character) (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (wrmin : ℝ) (hwrmin : 0 < wrmin) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (label : WholeSourceIndex rayM H) (rows : Finset FreeRow),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      ∀ (selected : Finset Slot) (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ)
        (t : FreeRow → ℝ) (height : ℝ),
      (∀ s ∈ selected, wrmin ≤ wr s) → (∀ s ∈ selected, wr s ≤ meshI) →
      (∀ s ∈ selected, σ s = 33/50) → 0 ≤ height → (∀ u ∈ rows, |t u| ≤ height) →
      (∀ s ∈ selected, |v s| ≤ height) →
      ∀ x : ℝ, ρ.Admissible x (∑ s ∈ selected, wr s) 1 →
      ∀ (tstar : ℝ) (n : ℕ), n ≤ 2 → ∀ σ' ∈ Set.Icc (0:ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
      ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) true
          ((logProfile^[n]) (inverseTest U tstar x)) (U^x) σ' freq *
        (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤
        C*(1+height)^J*U^(1+εm) := by
  set N := Fintype.card Slot
  -- normalised node profiles
  have hnode (j : Fin (N+1)) := normalized_profile (Cycle61MarkedHeight.commonProfile W j.val)
    ((Cycle61MarkedHeight.commonProfile_support W j.val).trans hWs)
    (Cycle61MarkedHeight.commonProfile_smooth W 1 2 one_pos hWs hW j.val)
  choose cj hcj W' hW'sm hW'su hW'b hW'eq using hnode
  have hcls (j : Fin (N+1)) : Contract.canonicalFamily (Contract.canonicalSlotsRay (W' j) (33/50)
      (twistMod rayM η η₀) (twistSlot rayM H hH η η₀) le_rfl) :=
    ⟨W' j, hW'sm j, hW'su j, twistMod rayM η η₀, inferInstance, twistSlot rayM H hH η η₀,
      le_rfl, rfl⟩
  let data : WholeSourceIndex rayM H → RowData := fun l =>
    ProbeHighRowFamily.momentData (Record12518109Natural.cleanWholeBase rayM H hH η η₀ l)
  -- the degree depends on the row data; finitely many (node, label) pairs occur
  choose deg Cq Zq hCq hZq hb using fun q : Fin (N+1) × WholeSourceIndex rayM H =>
    FiberBridge.detector_inverse_of_rect hs (Contract.canonicalSlotsRay (W' q.1) (33/50)
      (twistMod rayM η η₀) (twistSlot rayM H hH η η₀) le_rfl) (hcls q.1) N (data q.2)
  -- constants
  let cmax : ℝ := ∑ j, cj j
  have hcj_le (j : Fin (N+1)) : cj j ≤ cmax :=
    Finset.single_le_sum (fun k _ => (zero_le_one.trans (hcj k))) (Finset.mem_univ j)
  have hcmax : 1 ≤ cmax := (hcj 0).trans (hcj_le 0)
  let Csum : ℝ := ∑ q, Cq q
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg (fun q _ => (hCq q).le)
  have hCq_le (q : Fin (N+1) × WholeSourceIndex rayM H) : Cq q ≤ 1 + Csum := by
    have := Finset.single_le_sum (fun q _ => (hCq q).le) (Finset.mem_univ q)
    linarith
  let Dg : ℕ := ∑ q, deg q
  have hdeg_le (q : Fin (N+1) × WholeSourceIndex rayM H) : deg q ≤ Dg :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  set cost := Cycle61MarkedHeight.commonProfileCost N with hcost
  have hcost1 : 1 ≤ cost := Cycle61MarkedHeight.commonProfileCost_ge_one N
  refine ⟨Dg + 1, 4*cost*(cmax^2)^N*(1 + Csum)*2^Dg, by positivity, ?_⟩
  -- the large-norm threshold
  let Nbig : ℝ := ((twistMod rayM η η₀).absNorm : ℝ) +
    ((Record12518109Natural.wholeAnchorMask rayM H hH η₀).absNorm : ℝ) +
    ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) +
    ∑ l, ((DetectorDictionaryInverseRawInitialGates.deletedBase (data l)).modulus.absNorm : ℝ)
  have hbig : ∀ᶠ U : ℝ in atTop, Nbig < U^wrmin :=
    (tendsto_rpow_atTop hwrmin).eventually (eventually_gt_atTop Nbig)
  filter_upwards [eventually_gt_atTop (1:ℝ), hbig,
    eventually_all.mpr (fun q => eventually_ge_atTop (Zq q))] with U hU1 hUbig hUZ
  refine ⟨hU1, ?_⟩
  intro label rows hnorm selected θ wr σ v t height hwmin hwm hσ hh ht hvh x hadm tstar n hn
    σ' hσ' freq hfreq
  have hU0 : 0 < U := zero_lt_one.trans hU1
  have hD (s : Slot) : 0 < U^(wr s) := Real.rpow_pos_of_pos hU0 _
  have hDbig (s : Slot) (hs : s ∈ selected) : Nbig < U^(wr s) :=
    lt_of_lt_of_le hUbig (Real.rpow_le_rpow_of_exponent_le hU1.le (hwmin s hs))
  have hN0 : ∀ l, (0:ℝ) ≤ ((DetectorDictionaryInverseRawInitialGates.deletedBase (data l)).modulus.absNorm : ℝ) :=
    fun l => Nat.cast_nonneg _
  have hT (s : Slot) (hs : s ∈ selected) :
      ((twistMod rayM η η₀).absNorm : ℝ) < U^(wr s) := by
    have := hDbig s hs
    have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => hN0 l)
    have h1 : (0:ℝ) ≤ ((Record12518109Natural.wholeAnchorMask rayM H hH η₀).absNorm : ℝ) :=
      Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hM (s : Slot) (hs : s ∈ selected) :
      ((Record12518109Natural.wholeAnchorMask rayM H hH η₀).absNorm : ℝ) < U^(wr s) := by
    have := hDbig s hs
    have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => hN0 l)
    have h1 : (0:ℝ) ≤ ((twistMod rayM η η₀).absNorm : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hF (s : Slot) (hs : s ∈ selected) :
      ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) < U^(wr s) := by
    have := hDbig s hs
    have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => hN0 l)
    have h1 : (0:ℝ) ≤ ((twistMod rayM η η₀).absNorm : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ ((Record12518109Natural.wholeAnchorMask rayM H hH η₀).absNorm : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hDel (s : Slot) (hs : s ∈ selected) :
      ((DetectorDictionaryInverseRawInitialGates.deletedBase (data label)).modulus.absNorm : ℝ) <
        U^(wr s) := by
    have := hDbig s hs
    have hl := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hN0 l) (Finset.mem_univ label)
    have h1 : (0:ℝ) ≤ ((twistMod rayM η η₀).absNorm : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ ((Record12518109Natural.wholeAnchorMask rayM H hH η₀).absNorm : ℝ) :=
      Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) :=
      Nat.cast_nonneg _
    linarith
  -- the polynomial factor
  let factor : FreeRow → ℂ := fun u => polynomial (coreFamily rayM H hH η η₀ u label) true
    ((logProfile^[n]) (inverseTest U tstar x)) (U^x) σ' freq
  have hfactor (u : FreeRow) : factor u =
      polynomial ((data label).character (ProbeHighRowFamily.momentElement u)) true
        ((logProfile^[n]) (inverseTest U tstar x)) (U^x) σ' freq :=
    HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _
      (fun I => LocalMoment.natural_raw_coefficients _ ⟨u.val, u.property.1⟩ I) _ _ _ _ _
  -- node slot heights `t' + v s` are bounded by `2·height`, paid by `(2(1+height))^Dg`
  set E : ℝ := (cmax^2)^N * ((1 + Csum) * (2*(1+height))^Dg) * U^(1+εm) with hE
  have hE0 : 0 ≤ E := by positivity
  have hcard : selected.card ≤ N := Finset.card_le_univ selected
  -- fixed-height moments at every node
  have hmoment (j : Fin (N+1)) (t' : ℝ) (ht' : t' ∈ Set.Icc (-height) height) :
      ∑ u ∈ rows, ‖factor u * ∏ s ∈ selected,
        naturalSlot (naturalRow (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀))
          u.val u.property.1).character (primePool rayM H 2 (U^(wr s)))
          (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ s)) I *
            HeckePrimeAnnular.annularWeight (Cycle61MarkedHeight.commonProfile W j.val)
              (U^(wr s)) (σ s) (t' + v s) I) (U^(wr s))‖^2 ≤ E := by
    have hslot (u : FreeRow) : ∏ s ∈ selected,
        naturalSlot (naturalRow (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀))
          u.val u.property.1).character (primePool rayM H 2 (U^(wr s)))
          (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ s)) I *
            HeckePrimeAnnular.annularWeight (Cycle61MarkedHeight.commonProfile W j.val)
              (U^(wr s)) (σ s) (t' + v s) I) (U^(wr s)) =
        ∏ s ∈ selected, ((cj j : ℂ) * Contract.directSlot u.val
          (Contract.canonicalPool (twistMod rayM η η₀) (twistPool rayM H η η₀) (U^(wr s)))
          (canonBeta rayM η η₀ (data label) (W' j) (U^(wr s)) (33/50) (t' + v s)) (U^(wr s))) := by
      apply Finset.prod_congr rfl
      intro s hs
      rw [node_slot_eq rayM H hH η η₀ (data label) (θ s) _ (W' j)
        ((Cycle61MarkedHeight.commonProfile_support W j.val).trans hWs) (cj j) (hW'eq j)
        (hD s) (σ s) (t' + v s) (hT s hs) (hM s hs) (hF s hs) (hDel s hs) u.val u.property.1,
        hσ s hs]
    simp only [hslot, prod_const_mul_sq]
    rw [← Finset.mul_sum]
    have hcj2 : ((cj j)^2)^selected.card ≤ (cmax^2)^N := by
      calc ((cj j)^2)^selected.card ≤ ((cj j)^2)^N :=
            pow_le_pow_right₀ (one_le_pow₀ (hcj j)) hcard
        _ ≤ (cmax^2)^N := pow_le_pow_left₀ (by positivity)
            (pow_le_pow_left₀ (zero_le_one.trans (hcj j)) (hcj_le j) 2) N
    -- the contract bound
    let L : selected → Finset (Ideal O) := fun s =>
      Contract.canonicalPool (twistMod rayM η η₀) (twistPool rayM H η η₀) (U^(wr s.val))
    let ell : selected → ℝ := fun s => wr s.val
    let β : selected → Ideal O → ℂ := fun s =>
      canonBeta rayM η η₀ (data label) (W' j) (U^(wr s.val)) (33/50) (t' + v s.val)
    have hh2 : 0 ≤ 2*height := by linarith
    have ht'a : |t'| ≤ height := abs_le.mpr ⟨ht'.1, ht'.2⟩
    have hclsv : Contract.canonicalSlotsRay (W' j) (33/50) (twistMod rayM η η₀)
        (twistSlot rayM H hH η η₀) le_rfl selected (data label) L ell β U (2*height) :=
      ⟨twistTheta rayM η η₀, fun s => t' + v s.val,
        fun s => (abs_add_le _ _).trans (by linarith [hvh s.val s.property]),
        fun _ => ⟨rfl, rfl⟩⟩
    have hfreq2 : freq ∈ Set.Icc (-(2*height)) (2*height) :=
      ⟨by linarith [hfreq.1], by linarith [hfreq.2]⟩
    have hrows : ∀ u ∈ rows.image ProbeHighRowFamily.momentElement,
        ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ U := by
      intro u hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      exact hnorm w hw
    have hbnd := hb (j, label) U (hUZ (j, label)) (ι := selected)
      (by simpa using hcard) L ell β (2*height) hh2 hclsv
      (fun s => (hwrmin.le.trans (hwmin s.val s.property)))
      (fun s => hwm s.val s.property)
      (fun s P hP => (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2.1)
      (fun s P hP => (Finset.mem_filter.mp hP).2)
      (fun s P hP => canon_beta_norm_le rayM H η η₀ (data label) (W' j) (hW'b j) _ _ _
        (by norm_num) P hP)
      (fun s => hDel s.val s.property) x
      (by simpa only [ell, Finset.sum_coe_sort] using hadm)
      (rows.image ProbeHighRowFamily.momentElement) hrows tstar false n hn σ' hσ' (2*height) freq
      hh2 le_rfl hfreq2
    rw [Finset.sum_image (fun u _ w _ huw =>
      Record12518109GainActual.momentElement_injective huw)] at hbnd
    simp only [HeckeDetectorCoefficientTransfer.orientedProfile, Bool.false_eq_true,
      ite_false] at hbnd
    have hsum : ∑ u ∈ rows, ‖factor u * ∏ s ∈ selected, Contract.directSlot u.val
        (Contract.canonicalPool (twistMod rayM η η₀) (twistPool rayM H η η₀) (U^(wr s)))
        (canonBeta rayM η η₀ (data label) (W' j) (U^(wr s)) (33/50) (t' + v s)) (U^(wr s))‖^2 ≤
        (Cq (j, label) * (1+2*height)^(deg (j, label))) * U^(1+εm) := by
      refine le_trans (le_of_eq ?_) hbnd
      apply Finset.sum_congr rfl
      intro u _
      rw [hfactor u, ← Finset.prod_coe_sort selected]
      rfl
    calc ((cj j)^2)^selected.card * ∑ u ∈ rows, ‖factor u * ∏ s ∈ selected,
          Contract.directSlot u.val
          (Contract.canonicalPool (twistMod rayM η η₀) (twistPool rayM H η η₀) (U^(wr s)))
          (canonBeta rayM η η₀ (data label) (W' j) (U^(wr s)) (33/50) (t' + v s))
          (U^(wr s))‖^2
        ≤ (cmax^2)^N * ((Cq (j, label) * (1+2*height)^(deg (j, label))) * U^(1+εm)) :=
          mul_le_mul hcj2 hsum (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
      _ ≤ E := by
          rw [hE]
          have h1 : (1:ℝ) ≤ 2*(1 + height) := by linarith
          have h2 : (1+2*height)^(deg (j, label)) ≤ (2*(1+height))^(deg (j, label)) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
          have : Cq (j, label) * (1+2*height)^(deg (j, label)) ≤
              (1 + Csum) * (2*(1+height))^Dg :=
            mul_le_mul (hCq_le _) (h2.trans (pow_le_pow_right₀ h1 (hdeg_le (j, label))))
              (by positivity) (by positivity)
          have hU' : 0 ≤ U^(1+εm) := Real.rpow_nonneg hU0.le _
          have : (Cq (j, label) * (1+2*height)^(deg (j, label))) * U^(1+εm) ≤
              ((1 + Csum) * (2*(1+height))^Dg) * U^(1+εm) := mul_le_mul_of_nonneg_right this hU'
          calc (cmax^2)^N * ((Cq (j, label) * (1+2*height)^(deg (j, label))) * U^(1+εm))
              ≤ (cmax^2)^N * (((1 + Csum) * (2*(1+height))^Dg) * U^(1+εm)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
  have hrw := Cycle61MarkedHeight.naturalSlot_rowwise_energy rows selected N hcard
    (fun u : FreeRow => (naturalRow (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀))
      u.val u.property.1).character)
    (fun s => primePool rayM H 2 (U^(wr s)))
    (fun s _ I hI => (Finset.mem_filter.mp hI).2.1.ne_zero)
    (fun s I => idealCoeff (relativeCharacter rayM H hH η₀ (θ s)) I) W
    (fun s => U^(wr s)) σ v (fun s _ => hD s) factor (-height) height E (by linarith) hE0 t
    (fun u hu => abs_le.mp (ht u hu)) hmoment
  refine le_trans (le_of_eq ?_) (hrw.trans ?_)
  · rfl
  · rw [hE]
    have h1 : (1:ℝ) ≤ 1 + height := by linarith
    have hU' : 0 ≤ U^(1+εm) := Real.rpow_nonneg hU0.le _
    calc (1 + 2*(height - -height)) * cost * ((cmax^2)^N * ((1 + Csum) * (2*(1+height))^Dg) *
          U^(1+εm))
        ≤ (4*(1+height)) * cost * ((cmax^2)^N * ((1 + Csum) * (2*(1+height))^Dg) *
          U^(1+εm)) := by
          gcongr; linarith
      _ = 4*cost*(cmax^2)^N*(1 + Csum)*2^Dg*(1+height)^(Dg+1)*U^(1+εm) := by rw [mul_pow]; ring

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Marked
