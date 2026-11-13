/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Physical paired-source induction on the checked finite chain. All output
rectangles retain their arbitrary positive decrement and common-mesh contracts. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.ChainGeometry

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorZeroLoss.Certificate
open Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native

def StageOutput (n : ℕ) : Prop :=
  ∀ r : ℝ,((stage n).left:ℝ)≤r → r≤((stage n).R:ℝ) →
    AnchorAt r (fY ((stage n).R:ℝ) (stage n).gain (stage n).cut r)

/-- Every checked stage is a genuine paired moment supplier, proved in acyclic
order from the native seed and the known parent/reserve sources. -/
theorem all_stage_outputs (F : ParentFace)
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hbase : AnchorAt (311/400) 0) : ∀ n : ℕ,n<8192 → StageOutput n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hentry : AnchorAt (stage n).R (stage n).gain := by
      cases n with
      | zero =>
        rw [seed.1,seed.2.1]
        norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero]
        exact hbase
      | succ m =>
        have hm : m<8192 := by omega
        have hb := (Stage.ok_sound (local_checked m hm)).1
        have hle : ((stage m).left:ℝ)≤(stage m).R := Rat.cast_le.mpr hb.2.2.2.1.le
        have hA := ih m (Nat.lt_succ_self m) hm (stage m).left le_rfl hle
        obtain ⟨he,hgain,hrest⟩ := adjacent_geometry m hn
        apply hA.mono he.le
        rw [he]
        linarith
    have hprior : ∀x : ℝ,((stage n).R:ℝ)<x → x≤311/400 → ∃gain : ℝ,0≤gain ∧
        ((stage n).a0:ℝ)-((stage n).a1:ℝ)*x≤gain ∧ AnchorAt x gain := by
      intro x hx hxTop
      by_cases hzero : n=0
      · subst n
        have he : ((stage 0).R:ℝ)=311/400 := by rw [seed.1]; norm_num
        rw [he] at hx
        linarith
      · have hnpos : 0<n := Nat.pos_of_ne_zero hzero
        have hx0 : x≤((stage 0).R:ℝ) := by rw [seed.1]; norm_num; exact hxTop
        obtain ⟨j,hj,hxlo,hxhi⟩ := Qrh.TwoSlot.AnchorExtension.finite_partition_cover
          (fun i=>((stage i).R:ℝ)) hnpos hx.le hx0
        rw [(adjacent_geometry j (by omega)).1] at hxlo
        have hA := ih j hj (by omega) x hxlo hxhi
        have hS := ordinary_hyp (stage j) (local_checked j (by omega)) x hxlo hxhi
        have hl := previous_minorant n hn j hj x hxlo hxhi
        have hp : (0:ℝ)<(pad:ℝ) := by norm_num [pad]
        refine ⟨fY ((stage j).R:ℝ) (stage j).gain (stage j).cut x,hS.Y_nonneg,?_,hA⟩
        unfold sourceLine at hl
        linarith
    intro r hlo hhi
    exact checked_stage_anchor (stage n) (local_checked n hn) F hβ hres hparent hentry hprior r hlo hhi

/-- The checked finite intervals cover the full source range. -/
theorem full_cover {r : ℝ} (hlo : 1467/2000≤r) (hhi : r≤311/400) :
    ∃ j<8192,((stage j).left:ℝ)≤r ∧ r≤((stage j).R:ℝ) := by
  by_cases hlast : r≤((stage 8191).R:ℝ)
  · refine ⟨8191,by norm_num,?_,hlast⟩
    rw [last_left]
    norm_num
    exact hlo
  · have hr0 : r≤((stage 0).R:ℝ) := by rw [seed.1]; norm_num; exact hhi
    obtain ⟨j,hj,hrlo,hrhi⟩ := Qrh.TwoSlot.AnchorExtension.finite_partition_cover
      (fun i=>((stage i).R:ℝ)) (by norm_num : 0<8191) (le_of_not_ge hlast) hr0
    rw [(adjacent_geometry j (by omega)).1] at hrlo
    exact ⟨j,by omega,hrlo,hrhi⟩

/-- The final affine source family is supplied by the actual finite induction.
This is a moment theorem, not an endpoint nonvanishing declaration. -/
theorem finite_improved_moments (F : ParentFace)
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hbase : AnchorAt (311/400) 0) :
    ImprovedMoments (1467/2000) (311/400) (targetG0:ℝ) (targetG1:ℝ) := by
  intro r hlo hhi
  obtain ⟨j,hj,hrlo,hrhi⟩ := full_cover hlo hhi
  have hA := all_stage_outputs F hβ hres hparent hbase j hj r hrlo hrhi
  have hb := (Stage.ok_sound (local_checked j hj)).1
  rcases hb with ⟨hR0,hR1,hleft,hlt,hk0,hk1,hz,ha,ha1,hu,hw,hline,hgain,hL,hR⟩
  have hLr : (targetG0:ℝ)-(targetG1:ℝ)*(stage j).left+(pad:ℝ)<
      fY ((stage j).R:ℝ) (stage j).gain (stage j).cut (stage j).left := by
    have h : ((fline targetG0 targetG1 (stage j).left+pad:ℚ):ℝ)<
        (((stage j).Y (stage j).left:ℚ):ℝ) := Rat.cast_lt.mpr hL
    simpa only [fline,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,cast_Y] using h
  have hRr : (targetG0:ℝ)-(targetG1:ℝ)*(stage j).R+(pad:ℝ)<
      fY ((stage j).R:ℝ) (stage j).gain (stage j).cut (stage j).R := by
    have h : ((fline targetG0 targetG1 (stage j).R+pad:ℚ):ℝ)<
        (((stage j).Y (stage j).R:ℚ):ℝ) := Rat.cast_lt.mpr hR
    simpa only [fline,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,cast_Y] using h
  have hltR : ((stage j).left:ℝ)<(stage j).R := by exact_mod_cast hlt
  have hm := Qrh.TwoSlot.AnchorContinuum.source_minorant_between hltR hrlo hrhi hLr hRr
  have hp : (0:ℝ)<(pad:ℝ) := by norm_num [pad]
  apply hA.mono le_rfl
  linarith

end Qrh.TwoSlot.AnchorZeroLoss.Certificate
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Certificate.all_stage_outputs
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Certificate.finite_improved_moments
