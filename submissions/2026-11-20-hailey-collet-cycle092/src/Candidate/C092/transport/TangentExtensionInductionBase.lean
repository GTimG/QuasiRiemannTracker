/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Acyclic induction through all 68 actual O.2 paired source stages. -/
import Candidate.C092.transport.TangentExtensionCheckedStage
import Candidate.C092.transport.TangentExtensionGeometry
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Reserve.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.TangentExtension.Certificate
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price Qrh.TwoSlot.AnchorZeroLoss
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData

def StageOutput (n : ℕ) : Prop :=
  ∀ r : ℝ,((stage n).left:ℝ) ≤ r → r ≤ ((stage n).R:ℝ) →
    AnchorAt r (fY ((stage n).R:ℝ) (stage n).gain (stage n).cut r)

/-- Actual source induction: every HIGH call is to a strictly earlier source,
while both output source rectangles retain every positive decrement. -/
theorem all_stage_outputs_of_entry
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hentry0 : AnchorAt (stage 0).R (stage 0).gain)
    (hprior0 : ∀ x : ℝ,((stage 0).R:ℝ) ≤ x → x ≤ 311/400 →
      ∃ gain : ℝ,0 ≤ gain ∧ (stage 0).a0-(stage 0).a1*x ≤ gain ∧ AnchorAt x gain) :
    ∀ n : ℕ,n < 68 → StageOutput n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hentry : AnchorAt (stage n).R (stage n).gain := by
      cases n with
      | zero => exact hentry0
      | succ m =>
        have hm : m < 68 := by omega
        have hb := (Stage.ok_sound (local_checked m hm)).1
        have hA := ih m (Nat.lt_succ_self m) hm (stage m).left le_rfl
          (Rat.cast_le.mpr hb.2.2.2.1.le)
        obtain ⟨he,hgain,hrest⟩ := adjacent_geometry m hn
        apply hA.mono he.le
        rw [he]
        linarith
    have hprior : ∀ x : ℝ,((stage n).R:ℝ) < x → x ≤ 311/400 → ∃ gain : ℝ,
        0 ≤ gain ∧ ((stage n).a0:ℝ)-((stage n).a1:ℝ)*x ≤ gain ∧ AnchorAt x gain := by
      intro x hx hxTop
      by_cases hx0 : ((stage 0).R:ℝ) ≤ x
      · obtain ⟨gain,hg0,hg,hA⟩ := hprior0 x hx0 hxTop
        have ha0 := congrArg (fun q : ℚ=>(q:ℝ)) (all_line ⟨n,hn⟩).1
        have ha1 := congrArg (fun q : ℚ=>(q:ℝ)) (all_line ⟨n,hn⟩).2
        exact ⟨gain,hg0,by rw [ha0,ha1];exact hg,hA⟩
      · have hnpos : 0 < n := by
          by_contra he
          have hn0 : n=0 := by omega
          subst n
          linarith
        obtain ⟨j,hj,hxlo,hxhi⟩ := Qrh.TwoSlot.AnchorExtension.finite_partition_cover
          (fun i=>((stage i).R:ℝ)) hnpos hx.le (le_of_not_ge hx0)
        rw [(adjacent_geometry j (by omega)).1] at hxlo
        have hA := ih j hj (by omega) x hxlo hxhi
        have hS := ordinary_hyp (stage j) (local_checked j (by omega)) x hxlo hxhi
        have hl := previous_minorant n hn j hj x hxlo hxhi
        have hp : (0:ℝ)<(pad:ℝ) := by norm_num [pad]
        exact ⟨fY ((stage j).R:ℝ) (stage j).gain (stage j).cut x,hS.Y_nonneg,
          by unfold sourceLine at hl;linarith,hA⟩
    intro r hlo hhi
    exact checked_stage_anchor (stage n) (local_checked n hn) parentFace hβ
      (Reserve.reserveParametricSource hβ) (parent_source hβ) hentry hprior r hlo hhi

/-- Every real point in the new interval belongs to an actual complete stage. -/
theorem full_cover {r : ℝ} (hlo : (18/25:ℝ) ≤ r) (hhi : r ≤ 1467/2000) :
    ∃ j < 68,((stage j).left:ℝ) ≤ r ∧ r ≤ (stage j).R := by
  by_cases hlast : r ≤ ((stage 67).R:ℝ)
  · refine ⟨67,by norm_num,?_,hlast⟩
    rw [last_left]
    norm_num
    exact hlo
  · have hr0 : r ≤ ((stage 0).R:ℝ) := by rw [first_R];norm_num;exact hhi
    obtain ⟨j,hj,hrlo,hrhi⟩ := Qrh.TwoSlot.AnchorExtension.finite_partition_cover
      (fun i=>((stage i).R:ℝ)) (by norm_num : 0 < 67) (le_of_not_ge hlast) hr0
    rw [(adjacent_geometry j (by omega)).1] at hrlo
    exact ⟨j,by omega,hrlo,hrhi⟩

/-- The new source line follows from genuine paired moments, not scalar checks alone. -/
theorem finite_improved_moments_of_entry
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hentry0 : AnchorAt (stage 0).R (stage 0).gain)
    (hprior0 : ∀ x : ℝ,((stage 0).R:ℝ) ≤ x → x ≤ 311/400 →
      ∃ gain : ℝ,0 ≤ gain ∧ (stage 0).a0-(stage 0).a1*x ≤ gain ∧ AnchorAt x gain) :
    ImprovedMoments (18/25) (1467/2000) (targetG0:ℝ) (targetG1:ℝ) := by
  intro r hlo hhi
  obtain ⟨j,hj,hrlo,hrhi⟩ := full_cover hlo hhi
  have hA := all_stage_outputs_of_entry hβ hentry0 hprior0 j hj r hrlo hrhi
  have hb := (Stage.ok_sound (local_checked j hj)).1
  rcases hb with ⟨hR0,hR1,hleft,hlt,hk0,hk1,hz,ha,ha1,hu,hw,hline,hgain,hL,hR⟩
  have hLr : (targetG0:ℝ)-(targetG1:ℝ)*(stage j).left+(pad:ℝ) <
      fY ((stage j).R:ℝ) (stage j).gain (stage j).cut (stage j).left := by
    have h : ((fline targetG0 targetG1 (stage j).left+pad:ℚ):ℝ) < (((stage j).Y (stage j).left:ℚ):ℝ) := Rat.cast_lt.mpr hL
    simpa only [fline,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,cast_Y] using h
  have hRr : (targetG0:ℝ)-(targetG1:ℝ)*(stage j).R+(pad:ℝ) <
      fY ((stage j).R:ℝ) (stage j).gain (stage j).cut (stage j).R := by
    have h : ((fline targetG0 targetG1 (stage j).R+pad:ℚ):ℝ) < (((stage j).Y (stage j).R:ℚ):ℝ) := Rat.cast_lt.mpr hR
    simpa only [fline,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,cast_Y] using h
  have hltR : ((stage j).left:ℝ)<(stage j).R := Rat.cast_lt.mpr hlt
  have hm := QRH.Cycle092.TangentExtension.source_minorant_between hltR hrlo hrhi hLr hRr
  have hp : (0:ℝ)<(pad:ℝ) := by norm_num [pad]
  apply hA.mono le_rfl
  linarith

end QRH.Cycle092.TangentExtension.Certificate
#print axioms QRH.Cycle092.TangentExtension.Certificate.all_stage_outputs_of_entry
#print axioms QRH.Cycle092.TangentExtension.Certificate.finite_improved_moments_of_entry
