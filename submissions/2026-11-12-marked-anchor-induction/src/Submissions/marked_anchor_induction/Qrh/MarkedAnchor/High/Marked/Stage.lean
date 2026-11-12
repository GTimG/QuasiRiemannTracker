/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Grid
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Inverse
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.NativeInv
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.PlainEmpty

/-!
# High.Marked.Stage

**The marked core inputs per stage**:
`markedCoreR1_stage (hβ) (hres) (n) (hn) (hE : EarlierAnchors n) :
  MarkedCoreR1 (a0 n) (a1 n) (R n + 10^-6)` and its consumer form
`highMarkedCoreInputsR1_stage : HighMarkedCoreInputsR1 (a0 n) (a1 n) (R n + 10^-6)`
(bounded heights; no slot separation).

Witness width `x ∈ [wc, 1)`, `wc ≥ R n + 10^-6`, selection `S ≤ sig x`:
* inverse: `x ≥ TOP - 10^-7` native (`core_inverse_native`, `top_native_gates`); otherwise the
  grid rectangle of an earlier anchor (`stage_grid`, `core_inverse_of_rect`);
* ordinary: empty selection native (`core_plain_empty`); otherwise the grid rectangle
  (`x < TOP - 10^-7`) or the reserve global face (`top_global_face`), `core_plain_of_face`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount Cycle61Moment
open Qrh.MarkedAnchor.Anchor ChainData ChainCheck
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.MarkedAnchor.High
local notation "O" => HeckeFamily.O
local instance markedStageQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The grid for every stage (empty at stage 0, where `R 0 = TOP`). -/
theorem stage_grid' (n : ℕ) (hn : n < 176) (IH : EarlierAnchors n) :
    ∃ (N : ℕ) (ρ : Fin N → AnchorRect),
      (∀ k, UniformInverseRectSource canonicalFamily (ρ k) ∧ OrdinaryRectSource (ρ k)) ∧
      ∀ x : ℝ, (R n : ℝ) < x → x < topLo →
        ∃ k, (ρ k).Admissible x (sig (a0 n) (a1 n) x) 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    refine ⟨0, Fin.elim0, fun k => k.elim0, ?_⟩
    intro x hx1 hx2
    exfalso
    have : ((R 0 : ℚ) : ℝ) = 311/400 := by rw [R_eq]; norm_num
    rw [this] at hx1
    unfold topLo at hx2
    linarith
  · exact stage_grid n hpos hn IH

/-- A positive-width selection has positive total width. -/
theorem sum_pos_of_ne {Slot : Type} {selected : Finset Slot} {wr : Slot → ℝ} {wrmin : ℝ}
    (hwrmin : 0 < wrmin) (hw : ∀ s ∈ selected, wrmin ≤ wr s) (hne : selected.Nonempty) :
    0 < ∑ s ∈ selected, wr s :=
  Finset.sum_pos (fun s hs => lt_of_lt_of_le hwrmin (hw s hs)) hne

/-- **Marked core inputs per stage, witness-free form.** -/
theorem markedCoreR1_stage (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource) (n : ℕ) (hn : n < 176) (hE : EarlierAnchors n) :
    MarkedCoreR1 (a0 n) (a1 n) ((R n : ℝ) + 1/1000000) := by
  obtain ⟨ha1, ha1', hl⟩ := stage_line n hn
  obtain ⟨N, ρ, hsrc, hcov⟩ := stage_grid' n hn hE
  obtain ⟨B, L, c, hG, hL0, hgf⟩ := top_global_face hres
  intro εm hεm
  choose meshI hmeshI hsI using fun k => (hsrc k).1 εm hεm
  choose meshO hmeshO hsO using fun k => (hsrc k).2 εm hεm
  obtain ⟨meshG, hmeshG, hsG⟩ := hG εm hεm
  let mesh' : Option (Fin N) → ℝ := fun o => o.elim meshG (fun k => min (meshI k) (meshO k))
  have hmesh'pos (o : Option (Fin N)) : 0 < mesh' o := by
    cases o with
    | none => exact hmeshG
    | some k => exact lt_min (hmeshI k) (hmeshO k)
  let meshm : ℝ := Finset.univ.inf' ⟨none, Finset.mem_univ _⟩ mesh'
  have hmm (o : Option (Fin N)) : meshm ≤ mesh' o := Finset.inf'_le _ (Finset.mem_univ o)
  have hmI (k : Fin N) : meshm ≤ meshI k := (hmm (some k)).trans (min_le_left _ _)
  have hmO (k : Fin N) : meshm ≤ meshO k := (hmm (some k)).trans (min_le_right _ _)
  have hmG : meshm ≤ meshG := hmm none
  refine ⟨meshm, (Finset.lt_inf'_iff _).mpr (fun o _ => hmesh'pos o), ?_⟩
  intro rayM _ H hH W hWs hW η η₀ Slot _ _ wrmin hwrmin
  -- constants of every source
  choose JI CI hCI evI using fun k => core_inverse_of_rect (hsI k) rayM H hH W hWs hW η η₀ Slot
    wrmin hwrmin
  obtain ⟨Jn, Cn, hCn, evn⟩ := core_inverse_native εm hεm rayM H hH W hWs hW η η₀ Slot wrmin
    hwrmin
  choose JO CO hCO evO using fun k => core_plain_of_face (ρ k).Pmax 0 (ρ k).Smax (meshO k) εm
    le_rfl hεm (hsO k) rayM H hH W hWs hW η η₀ Slot
  obtain ⟨Jg, Cg, hCg, evg⟩ := core_plain_of_face B L c meshG εm hL0 hεm hsG rayM H hH W hWs hW
    η η₀ Slot
  obtain ⟨Je, Ce, hCe, eve⟩ := core_plain_empty hβ εm hεm rayM H hH η η₀
  let J : ℕ := Jn + Jg + Je + ∑ k, JI k + ∑ k, JO k
  let C : ℝ := Cn + Cg + Ce + ∑ k, CI k + ∑ k, CO k
  have hCIs : 0 ≤ ∑ k, CI k := Finset.sum_nonneg (fun k _ => (hCI k).le)
  have hCOs : 0 ≤ ∑ k, CO k := Finset.sum_nonneg (fun k _ => (hCO k).le)
  refine ⟨J, C, by positivity, ?_⟩
  filter_upwards [evn, evg, eve, eventually_all.mpr evI, eventually_all.mpr evO] with
    U hUn hUg hUe hUI hUO
  refine ⟨hUn.1, ?_⟩
  intro height hh slots θ wr σ v t hwmin hwm hσ hv rows hnorm hreg ht wc hwc hwlo label J' K'
    C' hC'
  -- dominating constants
  have h1 : (1:ℝ) ≤ 1 + height := by linarith
  have hU0 : 0 < U := zero_lt_one.trans hUn.1
  have hUp : 0 ≤ U^(1+εm) := Real.rpow_nonneg hU0.le _
  have dom : ∀ (Ci : ℝ) (Ji : ℕ), 0 ≤ Ci → Ci ≤ C → Ji ≤ J →
      Ci*(1+height)^Ji*U^(1+εm) ≤ C'*U^(1+εm) := by
    intro Ci Ji hCi0 hCiC hJiJ
    apply mul_le_mul_of_nonneg_right _ hUp
    refine le_trans ?_ hC'
    exact mul_le_mul hCiC (pow_le_pow_right₀ h1 hJiJ) (by positivity) (by positivity)
  have hwc1 : (R n : ℝ) + 1/1000000 ≤ wc := hwlo
  have hRwc : (R n : ℝ) < wc := by linarith
  have hwc0 : 0 < wc := lt_of_lt_of_le (by norm_num [cutLo]) hwc.1
  constructor
  · -- inverse marked
    intro hx1 hx2 selected hsub hS n' hn' σ' hσ' freq hfreq
    set x := Real.logb U ((2:ℝ)^J'.val) with hxdef
    have hS0 : 0 ≤ ∑ s ∈ selected, wr s :=
      Finset.sum_nonneg (fun s hs => hwrmin.le.trans (hwmin s (hsub hs)))
    have hSsig : (∑ s ∈ selected, wr s) ≤ sig (a0 n) (a1 n) x :=
      hS.trans (selW_le_sig _ _ _ _)
    by_cases htop : topLo ≤ x
    · obtain ⟨g1, g2⟩ := top_native_gates ha1 ha1' hl htop hx2 hS0 hSsig
      have hb := hUn.2 label rows hnorm selected θ wr σ v t height
        (fun s hs => hwmin s (hsub hs)) (fun s hs => hσ s (hsub hs)) hh ht x (by linarith) g1 g2
        (3*wc/2+1/1000000) n' hn' σ' hσ' freq hfreq
      refine hb.trans (dom _ _ hCn.le ?_ ?_)
      · show Cn ≤ Cn + Cg + Ce + ∑ k, CI k + ∑ k, CO k
        linarith [hCg, hCe]
      · show Jn ≤ Jn + Jg + Je + ∑ k, JI k + ∑ k, JO k
        omega
    · push Not at htop
      obtain ⟨k, hk⟩ := hcov x (by linarith) htop
      have hadm : (ρ k).Admissible x (∑ s ∈ selected, wr s) 1 :=
        AnchorRect.admissible_downward hk (by linarith) le_rfl hS0 hSsig
      have hb := (hUI k).2 label rows hnorm selected θ wr σ v t height
        (fun s hs => hwmin s (hsub hs)) (fun s hs => (hwm s (hsub hs)).trans (hmI k))
        (fun s hs => hσ s (hsub hs)) hh ht (fun s hs => hv s (hsub hs)) x hadm
        (3*wc/2+1/1000000) n' hn' σ' hσ' freq hfreq
      refine hb.trans (dom _ _ (hCI k).le ?_ ?_)
      · have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (hCI k).le)
          (Finset.mem_univ k)
        show CI k ≤ Cn + Cg + Ce + ∑ k, CI k + ∑ k, CO k
        linarith
      · have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (JI k))
          (Finset.mem_univ k)
        show JI k ≤ Jn + Jg + Je + ∑ k, JI k + ∑ k, JO k
        omega
  · -- plain marked
    intro hx1 hx2 selected hsub hS j k' hjk σ' hσ' freq hfreq
    set m := Real.logb U ((2:ℝ)^K'.val) with hmdef
    have hm0 : 0 ≤ m := by linarith
    have hS0 : 0 ≤ ∑ s ∈ selected, wr s :=
      Finset.sum_nonneg (fun s hs => hwrmin.le.trans (hwmin s (hsub hs)))
    have hSsig : (∑ s ∈ selected, wr s) ≤ sig (a0 n) (a1 n) (2*m) :=
      hS.trans (selW_le_sig _ _ _ _)
    rcases Finset.eq_empty_or_nonempty selected with hemp | hne
    · subst hemp
      have hb := hUe.2 label rows hreg hnorm m hm0 hx2.le height hh j k' hjk σ' hσ' freq hfreq
      simp only [Finset.prod_empty, mul_one]
      refine hb.trans (dom _ _ hCe.le ?_ ?_)
      · show Ce ≤ Cn + Cg + Ce + ∑ k, CI k + ∑ k, CO k
        linarith
      · show Je ≤ Jn + Jg + Je + ∑ k, JI k + ∑ k, JO k
        omega
    · have hSpos := sum_pos_of_ne hwrmin (fun s hs => hwmin s (hsub hs)) hne
      by_cases htop : topLo ≤ 2*m
      · obtain ⟨hB, hc⟩ := hgf (a0 n) (a1 n) ha1 ha1' hl (2*m) _ htop hx2 hSpos hSsig
        have hb := hUg.2 label rows hreg hnorm m hm0 (by linarith) selected θ wr σ v t height
          (fun s hs => hwrmin.le.trans (hwmin s (hsub hs)))
          (fun s hs => (hwm s (hsub hs)).trans hmG) (fun s hs => hσ s (hsub hs)) hh
          (fun s hs => hv s (hsub hs)) ht hc hB j k' hjk σ' hσ' freq hfreq
        refine hb.trans (dom _ _ hCg.le ?_ ?_)
        · show Cg ≤ Cn + Cg + Ce + ∑ k, CI k + ∑ k, CO k
          linarith
        · show Jg ≤ Jn + Jg + Je + ∑ k, JI k + ∑ k, JO k
          omega
      · push Not at htop
        obtain ⟨q, hq⟩ := hcov (2*m) (by linarith) htop
        obtain ⟨-, hP, -, hSm⟩ := hq
        rw [mul_one] at hP hSm
        have hb := (hUO q).2 label rows hreg hnorm m hm0 (by linarith) selected θ wr σ v t height
          (fun s hs => hwrmin.le.trans (hwmin s (hsub hs)))
          (fun s hs => (hwm s (hsub hs)).trans (hmO q)) (fun s hs => hσ s (hsub hs)) hh
          (fun s hs => hv s (hsub hs)) ht (hSsig.trans hSm) (by linarith) j k' hjk σ' hσ' freq
          hfreq
        refine hb.trans (dom _ _ (hCO q).le ?_ ?_)
        · have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (hCO k).le)
            (Finset.mem_univ q)
          show CO q ≤ Cn + Cg + Ce + ∑ k, CI k + ∑ k, CO k
          linarith
        · have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (JO k))
            (Finset.mem_univ q)
          show JO q ≤ Jn + Jg + Je + ∑ k, JI k + ∑ k, JO k
          omega

/-- **Marked core inputs per stage, consumer form** (`HighMarkedCoreInputsR` + bounded heights;
what `High.locFiberInputsH` consumes). -/
theorem highMarkedCoreInputsR1_stage (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource) (n : ℕ) (hn : n < 176) (hE : EarlierAnchors n) :
    HighMarkedCoreInputsR1 (a0 n) (a1 n) ((R n : ℝ) + 1/1000000) :=
  r1_of_marked (markedCoreR1_stage hβ hres n hn hE)

end
end Qrh.MarkedAnchor.High.Marked

#print axioms Qrh.MarkedAnchor.High.Marked.markedCoreR1_stage
#print axioms Qrh.MarkedAnchor.High.Marked.highMarkedCoreInputsR1_stage
