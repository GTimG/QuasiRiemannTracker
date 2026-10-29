/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveMargins

namespace Qrh.JointDetector.RepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set

theorem rawRate_continuousAt_varying {α : Type*} [TopologicalSpace α]
    {B L ν v : α → ℝ} {c : ℝ} {x : α}
    (hB : ContinuousAt B x) (hL : ContinuousAt L x)
    (hν : ContinuousAt ν x) (hv : ContinuousAt v x)
    (hνp : 0 < ν x) (hνhi : ν x ≤ 3/4) (hLp : 3/2 ≤ L x)
    (hv0 : 0 ≤ v x) (hvν : v x ≤ ν x) :
    ContinuousAt (fun y => rawRepeatedCountRate (B y) (L y) c (ν y) (v y)) x := by
  have hLpos : 0 < L x := by linarith
  have hp0 : 0 ≤ v x/(2*ν x) := by positivity
  have hp : v x/(2*ν x) ≤ 1/2 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hD1 := (branch_den_pos hνp hνhi hp (by norm_num : (0:ℝ)<2)).ne'
  have hcoef : 0 < 2-4*(v x/(2*ν x))/(L x) := by
    have hq : 4*(v x/(2*ν x))/(L x) ≤ 4/3 :=
      (div_le_iff₀ hLpos).2 (by linarith)
    linarith
  have hD2 := (branch_den_pos hνp hνhi hp hcoef).ne'
  have hden1 : ContinuousAt
      (fun y => crossingDen (ν y) (v y/(2*ν y)) 2) x := by
    unfold crossingDen
    fun_prop (disch := positivity)
  have hden2 : ContinuousAt
      (fun y => crossingDen (ν y) (v y/(2*ν y)) (2-4*(v y/(2*ν y))/(L y))) x := by
    unfold crossingDen
    fun_prop (disch := positivity)
  have h2ν : 2*ν x ≠ 0 := by positivity
  have hLne : L x ≠ 0 := hLpos.ne'
  unfold rawRepeatedCountRate capCrossingRate budgetCrossingRate crossingRate
  fun_prop (disch := assumption)

/-- The parameter type is compact (for instance the subtype of one closed
polynomial piece). No continuity outside that piece is required. -/
theorem compact_family_uniform_crossing {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    (B L s n r : α → ℝ) (hB : Continuous B) (hL : Continuous L)
    (hs : Continuous s) (hn : Continuous n) (hr : Continuous r)
    (hcert : ∀ q, RayCrossing (B q) (L q) (s q) (n q) (r q)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ν, ν∈Icc (n q) (3/4:ℝ) →
      ∀ a∈Icc (0:ℝ) ν, ε ≤ 1-ν*(B q-L q*s q)-a*s q-
        combineSelected (rawRepeatedCountRate (B q) (L q) (1/10)) ν a := by
  let low : Set (α×(ℝ×ℝ)) :=
    (univ ×ˢ (Icc (0:ℝ) (3/4) ×ˢ Icc (0:ℝ) (3/4))) ∩
      {x | n x.1 ≤ x.2.1} ∩ {x | x.2.2 ≤ r x.1*x.2.1}
  have hlowCompact : IsCompact low :=
    ((isCompact_univ.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      (isClosed_le (hn.comp continuous_fst) (continuous_fst.comp continuous_snd))).inter_right
      (isClosed_le (continuous_snd.comp continuous_snd)
        ((hr.comp continuous_fst).mul (continuous_fst.comp continuous_snd)))
  have hlowNe : low.Nonempty := by
    let q : α := Classical.choice (inferInstance : Nonempty α)
    refine ⟨(q,n q,0),⟨⟨by simp,⟨(hcert q).n_pos.le,(hcert q).n_upper.le⟩,
      by norm_num⟩,by change n q ≤ n q; exact le_rfl⟩,?_⟩
    exact (mul_pos (hcert q).ray_pos (hcert q).n_pos).le
  have hlowCont : ContinuousOn (fun x : α×(ℝ×ℝ) =>
      1-x.2.1*(B x.1-L x.1*s x.1)-x.2.2*s x.1-
      rawRepeatedCountRate (B x.1) (L x.1) (1/10) x.2.1 x.2.2) low := by
    intro x hx
    have hc := hcert x.1
    have hνp : 0 < x.2.1 := hc.n_pos.trans_le hx.1.2
    have hνhi : x.2.1 ≤ 3/4 := hx.1.1.2.1.2
    have ha0 : 0 ≤ x.2.2 := hx.1.1.2.2.1
    have haν : x.2.2 ≤ x.2.1 := hx.2.trans (by nlinarith [hc.ray_le])
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
    have hh := (hcert x.1).raw_crossing ⟨hx.1.2,hx.1.1.2.1.2⟩ ⟨hx.1.1.2.2.1,hx.2⟩
    linarith)
  let upper : Set (α×ℝ) := (univ ×ˢ Icc (0:ℝ) (3/4)) ∩ {x | n x.1 ≤ x.2}
  have hupperCompact : IsCompact upper := (isCompact_univ.prod isCompact_Icc).inter_right
    (isClosed_le (hn.comp continuous_fst) continuous_snd)
  have hupperNe : upper.Nonempty := by
    let q : α := Classical.choice (inferInstance : Nonempty α)
    exact ⟨(q,n q),⟨by simp,⟨(hcert q).n_pos.le,(hcert q).n_upper.le⟩⟩,by change n q ≤ n q; exact le_rfl⟩
  let F : α×ℝ → ℝ := fun x =>
    1-x.2*(B x.1-L x.1*s x.1)-(r x.1*x.2)*s x.1-
      jointCountExponent x.2 (r x.1*x.2)
  have hupperCont : ContinuousOn F upper := by
    intro x hx
    have hc := hcert x.1
    have hνp : 0 < x.2 := hc.n_pos.trans_le hx.2
    have haν : r x.1*x.2 ≤ x.2 := by nlinarith [hc.ray_le]
    have hd : 3*(1-x.2)+2*(x.2-r x.1*x.2) ≠ 0 := by nlinarith [hx.1.2.2]
    have hb := (hB.comp continuous_fst).continuousAt (x:=x)
    have hl := (hL.comp continuous_fst).continuousAt (x:=x)
    have hss := (hs.comp continuous_fst).continuousAt (x:=x)
    have hrr := (hr.comp continuous_fst).continuousAt (x:=x)
    have hfun : ContinuousAt F x := by
      unfold F jointCountExponent witnessDen
      fun_prop (disch := assumption)
    exact hfun.continuousWithinAt
  obtain ⟨εu,hεu,hupper⟩ := compact_positive_margin upper hupperCompact hupperNe F hupperCont (by
    intro x hx
    have hc := hcert x.1
    have hnpos := hc.n_pos.trans_le hx.2
    have hra : r x.1*x.2 ≤ x.2 := by nlinarith [hc.ray_le]
    have hh := hc.selected_crossing ⟨hx.2,hx.1.2.2⟩
    simp only [detectorRate,if_pos hra] at hh
    dsimp [F]; linarith)
  refine ⟨min εl εu,lt_min hεl hεu,?_⟩
  intro q ν hν a ha
  have hc := hcert q
  have hnpos := hc.n_pos.trans_le hν.1
  have hra : r q*ν ≤ ν := by nlinarith [hc.ray_le]
  by_cases hla : a ≤ r q*ν
  · have hl := hlow (q,ν,a) ⟨⟨⟨by simp,⟨hnpos.le,hν.2⟩,⟨ha.1,ha.2.trans hν.2⟩⟩,hν.1⟩,hla⟩
    have hh := combineSelected_le_raw (rawRepeatedCountRate (B q) (L q) (1/10)) ν a
    have hm := min_le_left εl εu
    dsimp at hl
    linarith
  · have hal : r q*ν ≤ a := le_of_lt (lt_of_not_ge hla)
    have hcut : (500001/1000000:ℝ) < r q*ν := by
      have := mul_le_mul_of_nonneg_left hν.1 hc.ray_pos.le
      linarith [hc.selected_gap]
    have hm := selectedTerm_antitone (P:=B q-L q*s q) (H:=1) (S:=s q) hν.2
      (show (1/2:ℝ) ≤ r q*ν by linarith) (by norm_num) (by linarith [hc.s_cap])
      (show r q*ν∈Icc (r q*ν) ν from ⟨le_rfl,hra⟩)
      (show a∈Icc (r q*ν) ν from ⟨hal,ha.2⟩) hal
    have hh := hupper (q,ν) ⟨⟨by simp,⟨hnpos.le,hν.2⟩⟩,hν.1⟩
    have he : detectorRate ν (r q*ν)=jointCountExponent ν (r q*ν) := by simp [detectorRate,hra]
    have hsel := combineSelected_le_selected (rawRepeatedCountRate (B q) (L q) (1/10))
      (ν:=ν) (hcut.le.trans hal)
    have hmin := min_le_right εl εu
    dsimp [F] at hh
    rw [←he] at hh
    nlinarith

/-- One secant tolerance and one reserve work for every point of a compact
piece. The finite source partition can therefore be fixed before slots. -/
theorem compact_family_nearby_crossing {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    (B L s n r : α → ℝ) (hB : Continuous B) (hL : Continuous L)
    (hs : Continuous s) (hn : Continuous n) (hr : Continuous r)
    (hcert : ∀ q, RayCrossing (B q) (L q) (s q) (n q) (r q))
    (Lmax : ℝ) (hLmax : ∀ q, L q ≤ Lmax) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ∀ q s', |s'-s q| ≤ ρ →
      ∀ ν∈Icc (n q) (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε ≤ 1-ν*(B q-L q*s')-a*s'-
        combineSelected (rawRepeatedCountRate (B q) (L q) (1/10)) ν a := by
  obtain ⟨ε,hε,hm⟩ := compact_family_uniform_crossing B L s n r hB hL hs hn hr hcert
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

theorem compact_family_secant_tolerance {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    (B L s n r : α → ℝ) (hB : Continuous B) (hL : Continuous L)
    (hs : Continuous s) (hn : Continuous n) (hr : Continuous r)
    (hcert : ∀ q, RayCrossing (B q) (L q) (s q) (n q) (r q)) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ∀ q s', |s'-s q| ≤ ρ →
      ∀ ν∈Icc (n q) (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε ≤ 1-ν*(B q-L q*s')-a*s'-
        combineSelected (rawRepeatedCountRate (B q) (L q) (1/10)) ν a := by
  obtain ⟨q,_,hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (univ : Set α).Nonempty)
    hL.continuousOn
  exact compact_family_nearby_crossing B L s n r hB hL hs hn hr hcert (L q)
    (fun q' => hmax (Set.mem_univ q'))

end
end Qrh.JointDetector.RepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.compact_family_uniform_crossing

#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.compact_family_secant_tolerance
