/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PureSourceCurveCrossing
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveFamilyMargins
namespace Qrh.JointDetector.RepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set

theorem compact_pure_family_uniform_crossing {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    (B L s n : α → ℝ) (hB : Continuous B) (hL : Continuous L)
    (hs : Continuous s) (hn : Continuous n)
    (hcert : ∀ q, PureCrossing (B q) (L q) (s q) (n q)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ν, ν∈Icc (n q) (3/4:ℝ) →
      ∀ a∈Icc (0:ℝ) ν, ε ≤ 1-ν*(B q-L q*s q)-a*s q-
        rawRepeatedCountRate (B q) (L q) (1/10) ν a := by
  let low : Set (α×(ℝ×ℝ)) :=
    (univ ×ˢ (Icc (0:ℝ) (3/4) ×ˢ Icc (0:ℝ) (3/4))) ∩
      {x | n x.1 ≤ x.2.1} ∩ {x | x.2.2 ≤ x.2.1}
  have hlowCompact : IsCompact low :=
    ((isCompact_univ.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      (isClosed_le (hn.comp continuous_fst) (continuous_fst.comp continuous_snd))).inter_right
      (isClosed_le (continuous_snd.comp continuous_snd)
        (continuous_fst.comp continuous_snd))
  have hlowNe : low.Nonempty := by
    let q : α := Classical.choice (inferInstance : Nonempty α)
    refine ⟨(q,n q,0),⟨⟨by simp,⟨(hcert q).n_pos.le,(hcert q).n_upper.le⟩,
      by norm_num⟩,by change n q ≤ n q; exact le_rfl⟩,?_⟩
    exact (hcert q).n_pos.le
  have hlowCont : ContinuousOn (fun x : α×(ℝ×ℝ) =>
      1-x.2.1*(B x.1-L x.1*s x.1)-x.2.2*s x.1-
      rawRepeatedCountRate (B x.1) (L x.1) (1/10) x.2.1 x.2.2) low := by
    intro x hx
    have hc := hcert x.1
    have hνp : 0 < x.2.1 := hc.n_pos.trans_le hx.1.2
    have hνhi : x.2.1 ≤ 3/4 := hx.1.1.2.1.2
    have ha0 : 0 ≤ x.2.2 := hx.1.1.2.2.1
    have haν : x.2.2 ≤ x.2.1 := hx.2
    have hraw := rawRate_continuousAt_varying (c:=1/10)
      ((hB.comp continuous_fst).continuousAt) ((hL.comp continuous_fst).continuousAt)
      ((continuous_fst.comp continuous_snd).continuousAt)
      ((continuous_snd.comp continuous_snd).continuousAt) hνp hνhi hc.L_lower ha0 haν
    have hb := (hB.comp (continuous_fst : Continuous (Prod.fst : α×(ℝ×ℝ)→α))).continuousAt (x:=x)
    have hl := (hL.comp (continuous_fst : Continuous (Prod.fst : α×(ℝ×ℝ)→α))).continuousAt (x:=x)
    have hss := (hs.comp (continuous_fst : Continuous (Prod.fst : α×(ℝ×ℝ)→α))).continuousAt (x:=x)
    have hfun : ContinuousAt (fun x : α×(ℝ×ℝ) =>
      1-x.2.1*(B x.1-L x.1*s x.1)-x.2.2*s x.1-
      rawRepeatedCountRate (B x.1) (L x.1) (1/10) x.2.1 x.2.2) x := by fun_prop
    exact hfun.continuousWithinAt
  obtain ⟨εl,hεl,hlow⟩ := compact_positive_margin low hlowCompact hlowNe _ hlowCont (by
    intro x hx
    have hh := (hcert x.1).raw_crossing ⟨hx.1.2,hx.1.1.2.1.2⟩
      (show x.2.2∈Icc (0:ℝ) (1*x.2.1) by simpa using (show x.2.2∈Icc (0:ℝ) x.2.1 from ⟨hx.1.1.2.2.1,hx.2⟩))
    linarith)
  refine ⟨εl,hεl,?_⟩
  intro q ν hν a ha
  have hl := hlow (q,ν,a) ⟨⟨⟨by simp,⟨(hcert q).n_pos.le.trans hν.1,hν.2⟩,
    ⟨ha.1,ha.2.trans hν.2⟩⟩,hν.1⟩,ha.2⟩
  exact hl

namespace PureCrossing
variable {B L s n : ℝ} (h : PureCrossing B L s n)
include h
theorem nearby_crossing {ε s' : ℝ} (hε : 0 < ε)
    (hmargin : ∀ ν∈Icc n (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε ≤ 1-ν*(B-L*s)-a*s-rawRepeatedCountRate B L (1/10) ν a)
    (hclose : |s'-s| ≤ ε/(2*L)) :
    ∀ ν∈Icc n (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε/2 ≤ 1-ν*(B-L*s')-a*s'-rawRepeatedCountRate B L (1/10) ν a := by
  intro ν hν a ha
  have hn := h.n_pos.trans_le hν.1
  have hLp : 0 < L := by linarith [h.L_lower]
  have hcoef : 0 ≤ ν*L-a := by nlinarith [ha.2,h.L_lower]
  have hcoefhi : ν*L-a ≤ L := by nlinarith [ha.1,hν.2]
  have hd := (abs_le.mp hclose).1
  have heq : L*(ε/(2*L))=ε/2 := by field_simp
  have hp1 := mul_le_mul_of_nonneg_left hd hcoef
  have hp2 := mul_le_mul_of_nonneg_right hcoefhi
    (show 0 ≤ ε/(2*L) by positivity)
  have hg := hmargin ν hν a ha
  nlinarith

end PureCrossing

theorem compact_pure_family_nearby_crossing {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    (B L s n : α → ℝ) (hB : Continuous B) (hL : Continuous L)
    (hs : Continuous s) (hn : Continuous n)
    (hcert : ∀ q, PureCrossing (B q) (L q) (s q) (n q))
    (Lmax : ℝ) (hLmax : ∀ q, L q ≤ Lmax) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ∀ q s', |s'-s q| ≤ ρ →
      ∀ ν∈Icc (n q) (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε ≤ 1-ν*(B q-L q*s')-a*s'-
        rawRepeatedCountRate (B q) (L q) (1/10) ν a := by
  obtain ⟨ε,hε,hm⟩ := compact_pure_family_uniform_crossing B L s n hB hL hs hn hcert
  have hM : 0 < Lmax := by
    let q : α := Classical.choice (inferInstance : Nonempty α)
    have := (hcert q).L_lower
    linarith [hLmax q]
  refine ⟨ε/2,ε/(2*Lmax),half_pos hε,by positivity,?_⟩
  intro q s' hclose
  have hLp : 0 < L q := by linarith [(hcert q).L_lower]
  have htol : ε/(2*Lmax) ≤ ε/(2*L q) :=
    div_le_div_of_nonneg_left hε.le (by positivity) (by linarith [hLmax q])
  exact (hcert q).nearby_crossing hε (hm q) (hclose.trans htol)

theorem compact_pure_family_secant_tolerance {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    (B L s n : α → ℝ) (hB : Continuous B) (hL : Continuous L)
    (hs : Continuous s) (hn : Continuous n)
    (hcert : ∀ q, PureCrossing (B q) (L q) (s q) (n q)) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ∀ q s', |s'-s q| ≤ ρ →
      ∀ ν∈Icc (n q) (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε ≤ 1-ν*(B q-L q*s')-a*s'-
        rawRepeatedCountRate (B q) (L q) (1/10) ν a := by
  obtain ⟨q,_,hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (univ : Set α).Nonempty)
    hL.continuousOn
  exact compact_pure_family_nearby_crossing B L s n hB hL hs hn hcert (L q)
    (fun q' => hmax (Set.mem_univ q'))

end
end Qrh.JointDetector.RepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.compact_pure_family_secant_tolerance
