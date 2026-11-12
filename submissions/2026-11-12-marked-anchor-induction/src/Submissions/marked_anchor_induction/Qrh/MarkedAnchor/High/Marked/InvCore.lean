/- Copyright (c) 2026 Sil. Apache-2.0.
Uses Hailey Collet's `overlapping_inverse_marked_energy` (Apache-2.0) above `TOP`. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Stage

/-!
# High.Marked.InvCore

The `inverseMarked` half of `High.Inverse.HighMarkedInverseCoreInputs` per stage, from the
earlier anchors:

`highMarkedInverseInvField_stage (n) (hn) (hE : EarlierAnchors n) :
  HighMarkedInverseInvField (a0 n) (a1 n) (R n + 10^-6)`.

`HighMarkedInverseInvField` is `HighMarkedInverseCoreInputs` with the conclusion reduced to its
first conjunct (verbatim). Witness width `x ∈ [wc, 1)`: for `x ≥ TOP - 10^-7` HC's native
`overlapping_inverse_marked_energy` (`top_native_gates`); below, the slack grid of earlier anchors
(`stage_grid'`) and `Interface.FiberBridge.detector_inverse_of_rect` with the fixed-ray class
`canonicalSlotsRay W (33/50) rayM G hH` (`raySlot` is literally its slot vector). No premise.
The field has no pool-disjointness hypothesis (overlapping slots admitted); the relative twist `θ`
is common to all slots (`raySlotG1 … (fun _ => θ)`); the height degree `J` depends on the row data
(`∀ data ∃ J C`).

The `plainMarked` half is NOT derivable in this form (rows of the ball): the ordinary anchor
contract (`UnitFaceSource`) only bounds natural rows (`m = fixedBadMask·gen 1`, `f = 1`) that are
`initialKeep` (not fixed-inducing), while the field asks for all rows of the ball and every `RowData`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Anchor ChainData ChainCheck
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.MarkedAnchor.High
local notation "O" => HeckeFamily.O
local instance markedInvCoreQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- Verbatim copy of `High.Inverse.raySlot` (High/Inverse/Contract.lean), restated here so that
this module does not depend on the inverse-leaf chain; the two agree by `rfl`. -/
def raySlotG1 (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (data : RowData)
    {Slot : Type} (U : ℝ) (θ : Slot → RayQuotient.Characters rayM G.twist) (wr v : Slot → ℝ)
    (u : NonzeroElement) (s : Slot) : ℂ :=
  directSlot u.val (canonicalPool rayM G.pool (U^(wr s)))
    (rayCoeff rayM G hH W (33/50) data (θ s) (U^(wr s)) (v s)) (U^(wr s))

/-- The `inverseMarked` half of `HighMarkedInverseCoreInputs` (same quantifiers). -/
def HighMarkedInverseInvField (a0 a1 wlo : ℝ) : Prop :=
  ∀ (εm : ℝ), 0 < εm → ∃ meshm : ℝ, 0 < meshm ∧
  ∀ (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)
    (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∀ {Slot : Type} [Fintype Slot] [DecidableEq Slot] (wrmin : ℝ), 0 < wrmin →
    ∀ data : RowData, ∃ (J : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (slots : Finset Slot) (θ : RayQuotient.Characters rayM G.twist)
        (wr v : Slot → ℝ),
      (∀ s ∈ slots, wrmin ≤ wr s) → (∀ s ∈ slots, wr s ≤ meshm) →
      (∀ s ∈ slots, ∀ P ∈ canonicalPool rayM G.pool (U^(wr s)),
        ‖rayCoeff rayM G hH W (33/50) data θ (U^(wr s)) (v s) P‖ ≤ 1) →
      (∀ s ∈ slots, ((deletedBase data).modulus.absNorm : ℝ) < U^(wr s)) →
      ∀ (rows : Finset NonzeroElement),
        (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ U) →
      ∀ (wc : ℝ), wc ∈ cutoffs → wlo ≤ wc → ∀ height : ℝ, 0 ≤ height →
      (∀ s ∈ slots, |v s| ≤ height) →
      (∀ x : ℝ, wc ≤ x → x < 1 →
        ∀ selected : Finset Slot, selected ⊆ slots →
          (∑ s ∈ selected, wr s) ≤ selW a0 a1 (∑ s ∈ slots, wr s) x →
        ∀ n : ℕ, n ≤ 2 → ∀ σ' ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
        ∑ u ∈ rows, ‖polynomial (data.character u) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n])
            (HeckeDetectorInverseFiberCount.inverseTest U (3*wc/2+1/1000000) x))
          (U^x) σ' freq *
          (∏ s ∈ selected, raySlotG1 rayM G hH W data U (fun _ => θ) wr v u s)‖^2 ≤
            C * (1+height)^J * U^(1+εm))

/-- **The inverse marked inputs of the inverse HIGH child, per stage.** -/
theorem highMarkedInverseInvField_stage (n : ℕ) (hn : n < 176) (hE : EarlierAnchors n) :
    HighMarkedInverseInvField (a0 n) (a1 n) ((R n : ℝ) + 1/1000000) := by
  obtain ⟨ha1, ha1', hl⟩ := stage_line n hn
  obtain ⟨N, ρ, hsrc, hcov⟩ := stage_grid' n hn hE
  intro εm hεm
  choose meshI hmeshI hsI using fun k => (hsrc k).1 εm hεm
  let mesh' : Option (Fin N) → ℝ := fun o => o.elim 1 meshI
  have hmesh'pos (o : Option (Fin N)) : 0 < mesh' o := by
    cases o with
    | none => exact one_pos
    | some k => exact hmeshI k
  let meshm : ℝ := Finset.univ.inf' ⟨none, Finset.mem_univ _⟩ mesh'
  have hmI (k : Fin N) : meshm ≤ meshI k := Finset.inf'_le _ (Finset.mem_univ (some k))
  refine ⟨meshm, (Finset.lt_inf'_iff _).mpr (fun o _ => hmesh'pos o), ?_⟩
  intro rayM _ G hH W hWs hW Slot _ _ wrmin hwrmin
  have hcls : canonicalFamily (canonicalSlotsRay W (33/50) rayM G hH) :=
    ⟨W, hW, hWs, rayM, inferInstance, G, hH, rfl⟩
  obtain ⟨degN, hN⟩ := Record12518109GainDeletion.overlapping_inverse_marked_energy εm 1 hεm
    le_rfl (Fintype.card Slot)
  intro data
  -- the anchor degrees `degI k` depend on the row data
  choose degI CI ZI hCI hZI hbI using fun k => Interface.FiberBridge.detector_inverse_of_rect
    (hsI k) (canonicalSlotsRay W (33/50) rayM G hH) hcls (Fintype.card Slot) data
  obtain ⟨Cn, Un, hCn, hUn, hbN⟩ := hN data
  have hCIs : 0 ≤ ∑ k, CI k := Finset.sum_nonneg (fun k _ => (hCI k).le)
  refine ⟨degN + ∑ k, degI k, Cn + ∑ k, CI k, by linarith, ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop Un,
    eventually_all.mpr (fun k => eventually_ge_atTop (ZI k))] with U hU1 hUn' hUI
  refine ⟨hU1, ?_⟩
  intro slots θ wr v hwmin hwm hβ hdel rows hrows wc hwc hwlo height hh hvh x hx1 hx2 selected
    hsub hS n' hn' σ' hσ' freq hfreq
  have hU0 : 0 < U := zero_lt_one.trans hU1
  have hUp : 0 ≤ U^(1+εm) := Real.rpow_nonneg hU0.le _
  have h1 : (1:ℝ) ≤ 1 + height := by linarith
  have hwc0 : 0 < wc := lt_of_lt_of_le (by norm_num [cutLo]) hwc.1
  have hRx : (R n : ℝ) < x := by linarith [show (R n : ℝ) + 1/1000000 ≤ wc from hwlo]
  have hS0 : 0 ≤ ∑ s ∈ selected, wr s :=
    Finset.sum_nonneg (fun s hs => hwrmin.le.trans (hwmin s (hsub hs)))
  have hSsig : (∑ s ∈ selected, wr s) ≤ sig (a0 n) (a1 n) x := hS.trans (selW_le_sig _ _ _ _)
  -- the slot vector of `selected`
  let L : selected → Finset (Ideal O) := fun s => canonicalPool rayM G.pool (U^(wr s.val))
  let ell : selected → ℝ := fun s => wr s.val
  let β : selected → Ideal O → ℂ := fun s =>
    rayCoeff rayM G hH W (33/50) data θ (U^(wr s.val)) (v s.val)
  have hprod : ∀ u : NonzeroElement, (∏ s ∈ selected, raySlotG1 rayM G hH W data U (fun _ => θ) wr v u s) =
      ∏ i, directSlot u.val (L i) (β i) (U^(ell i)) := by
    intro u
    rw [← Finset.prod_coe_sort selected]
    rfl
  simp only [hprod]
  have hcard : Fintype.card selected ≤ Fintype.card Slot := by
    simpa using Finset.card_le_univ selected
  have hell0 : ∀ i, 0 ≤ ell i := fun i => hwrmin.le.trans (hwmin i.val (hsub i.property))
  have hprime : ∀ i, ∀ P ∈ L i, Prime P :=
    fun i P hP => (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2.1
  have hratio : ∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/U^(ell i)) ∈ Icc (1:ℝ) 2 :=
    fun i P hP => (Finset.mem_filter.mp hP).2
  have hβi : ∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1 := fun i P hP => hβ i.val (hsub i.property) P hP
  have hdeli : ∀ i, ((deletedBase data).modulus.absNorm : ℝ) < U^(ell i) :=
    fun i => hdel i.val (hsub i.property)
  have hsum : (∑ i, ell i) = ∑ s ∈ selected, wr s := Finset.sum_coe_sort selected wr
  have hx0 : 0 ≤ x := by linarith
  have hdom : ∀ (Ci : ℝ) (d : ℕ), 0 ≤ Ci → Ci ≤ Cn + ∑ k, CI k → d ≤ degN + ∑ k, degI k →
      Ci * (1+height)^d * U^(1+εm) ≤ (Cn + ∑ k, CI k) * (1+height)^(degN + ∑ k, degI k) *
        U^(1+εm) := by
    intro Ci d hCi0 hCi hd
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hCi (pow_le_pow_right₀ h1 hd) (by positivity) (by linarith)) hUp
  by_cases htop : topLo ≤ x
  · obtain ⟨g1, g2⟩ := top_native_gates ha1 ha1' hl htop hx2 hS0 hSsig
    have hb := hbN U hUn' hcard L ell β hell0 hprime hratio hβi hdeli x hx0
      (by rw [hsum]; exact g1) (by rw [hsum]; exact g2) rows hrows (3*wc/2+1/1000000) false n'
      hn' σ' hσ' height freq hh hfreq
    simp only [HeckeDetectorCoefficientTransfer.orientedProfile, Bool.false_eq_true,
      ite_false] at hb
    refine le_trans (le_of_eq rfl) (hb.trans (hdom _ _ hCn.le (by linarith) (by omega)))
  · push Not at htop
    obtain ⟨k, hk⟩ := hcov x hRx htop
    have hadm : (ρ k).Admissible x (∑ i, ell i) 1 := by
      rw [hsum]; exact AnchorRect.admissible_downward hk hx0 le_rfl hS0 hSsig
    -- the slot heights are bounded by the field's height
    have hclsv : canonicalSlotsRay W (33/50) rayM G hH selected data L ell β U height :=
      ⟨θ, fun i => v i.val, fun i => hvh i.val (hsub i.property), fun _ => ⟨rfl, rfl⟩⟩
    have hb := hbI k U (hUI k) hcard L ell β height hh hclsv hell0
      (fun i => (hwm i.val (hsub i.property)).trans (hmI k)) hprime hratio hβi hdeli x
      hadm rows hrows (3*wc/2+1/1000000) false n' hn' σ' hσ' height freq hh le_rfl hfreq
    simp only [HeckeDetectorCoefficientTransfer.orientedProfile, Bool.false_eq_true,
      ite_false] at hb
    have hCk : CI k ≤ Cn + ∑ k, CI k := by
      have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (hCI k).le) (Finset.mem_univ k)
      linarith
    have hdk : degI k ≤ degN + ∑ k, degI k := by
      have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (degI k))
        (Finset.mem_univ k)
      omega
    exact hb.trans (hdom _ _ (hCI k).le hCk hdk)

end
end Qrh.MarkedAnchor.High.Marked

#print axioms Qrh.MarkedAnchor.High.Marked.highMarkedInverseInvField_stage
