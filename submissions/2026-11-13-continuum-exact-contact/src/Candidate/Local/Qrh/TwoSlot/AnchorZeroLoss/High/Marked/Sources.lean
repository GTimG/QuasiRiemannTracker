/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Generic earlier-rectangle supplier for the actual smaller-tolerance HIGH family.
The proof is adapted from Sil's PR137 High.Marked.Stage, Apache-2.0. It removes
all dependence on the numerical stage table and retains the finite common-mesh
and physical coefficient contracts. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Native
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.Inverse
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.NativeInv
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.PlainEmpty

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount Cycle61Moment
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorZeroLoss.High
local notation "O" => HeckeFamily.O
local instance sourceQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- A positive-width selection has positive total width. -/
theorem sum_pos_of_ne {Slot : Type} {selected : Finset Slot} {wr : Slot → ℝ} {wrmin : ℝ}
    (hwrmin : 0 < wrmin) (hw : ∀ s ∈ selected, wrmin ≤ wr s) (hne : selected.Nonempty) :
    0 < ∑ s ∈ selected, wr s :=
  Finset.sum_pos (fun s hs => lt_of_lt_of_le hwrmin (hw s hs)) hne

/-- **Marked core inputs per stage, witness-free form.** -/
theorem markedCoreR1_of_sources_with_tolerances (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (pad shift a0 a1 wlo top B L c : ℝ)
    (hnative : ∀ x S : ℝ, top≤x → x<1 → 0≤S → S≤max 0 ((1-x)/2+(a0-a1*x)-pad) →
      x+2*S<1 ∧ 2*x+8*S<3)
    (N : ℕ) (ρ : Fin N → AnchorRect)
    (hsrc : ∀ k, UniformInverseRectSource canonicalFamily (ρ k) ∧ OrdinaryRectSource (ρ k))
    (hcov : ∀ x : ℝ, wlo≤x → x<top → ∃ k, (ρ k).Admissible x (max 0 ((1-x)/2+(a0-a1*x)-pad)) 1)
    (hG : QRH.Record1252270103Source.GlobalSource B L c) (hL0 : 0≤L)
    (hgf : ∀ x S : ℝ, top≤x → x<1 → 0<S → S≤max 0 ((1-x)/2+(a0-a1*x)-pad) → x+L*S≤B ∧ S≤c) :
    MarkedCoreR1 a0 a1 wlo pad shift := by
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
  have hwc1 : wlo ≤ wc := hwlo
  have hwc0 : 0 < wc := lt_of_lt_of_le (by norm_num [cutLo]) hwc.1
  constructor
  · -- inverse marked
    intro hx1 hx2 selected hsub hS n' hn' σ' hσ' freq hfreq
    set x := Real.logb U ((2:ℝ)^J'.val) with hxdef
    have hS0 : 0 ≤ ∑ s ∈ selected, wr s :=
      Finset.sum_nonneg (fun s hs => hwrmin.le.trans (hwmin s (hsub hs)))
    have hSsig : (∑ s ∈ selected, wr s) ≤ max 0 ((1-x)/2+(a0-a1*x)-pad) :=
      hS.trans (min_le_left _ _)
    by_cases htop : top ≤ x
    · obtain ⟨g1, g2⟩ := hnative _ _ htop hx2 hS0 hSsig
      have hb := hUn.2 label rows hnorm selected θ wr σ v t height
        (fun s hs => hwmin s (hsub hs)) (fun s hs => hσ s (hsub hs)) hh ht x (by linarith) g1 g2
        (3*wc/2+shift) n' hn' σ' hσ' freq hfreq
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
        (3*wc/2+shift) n' hn' σ' hσ' freq hfreq
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
    have hSsig : (∑ s ∈ selected, wr s) ≤ max 0 ((1-2*m)/2+(a0-a1*(2*m))-pad) :=
      hS.trans (min_le_left _ _)
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
      by_cases htop : top ≤ 2*m
      · obtain ⟨hB, hc⟩ := hgf (2*m) _ htop hx2 hSpos hSsig
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


/-- Compatibility with the frozen finite source tolerances. -/
theorem markedCoreR1_of_sources (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (a0 a1 wlo top B L c : ℝ)
    (hnative : ∀ x S : ℝ, top≤x → x<1 → 0≤S → S≤sig a0 a1 x →
      x+2*S<1 ∧ 2*x+8*S<3)
    (N : ℕ) (ρ : Fin N → AnchorRect)
    (hsrc : ∀ k, UniformInverseRectSource canonicalFamily (ρ k) ∧ OrdinaryRectSource (ρ k))
    (hcov : ∀ x : ℝ, wlo≤x → x<top → ∃ k, (ρ k).Admissible x (sig a0 a1 x) 1)
    (hG : QRH.Record1252270103Source.GlobalSource B L c) (hL0 : 0≤L)
    (hgf : ∀ x S : ℝ, top≤x → x<1 → 0<S → S≤sig a0 a1 x → x+L*S≤B ∧ S≤c) :
    MarkedCoreR1 a0 a1 wlo := by
  simpa only [sig] using markedCoreR1_of_sources_with_tolerances hβ
    (1/10000000000000) (1/1000000000000) a0 a1 wlo top B L c
    hnative N ρ hsrc hcov hG hL0 hgf


end
end Qrh.TwoSlot.AnchorZeroLoss.High.Marked

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Marked.markedCoreR1_of_sources
