/- Repeated marks: the actual HIGH gaps with the repeated-mark gain.
Fork of the `some` case of Collet's `nf_actual_uniform_reserve`
(Record1252270103Source/Core/PhysicalReserve.lean, Apache-2.0). The HIGH facet gaps come from the
repeated-mark gate (`high_uniform_reserve`), the family gaps from the kept gates of
`SourceValidC` through Collet's `family_reserve`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalReserve
import Submissions.arvi_repeated_marks_20261024.Finite.SourceValid2
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Source
noncomputable section
open Record1252270103Finite QRH.Record1252270103Source.PhysicalScalar QRH.RepeatedMarks.Finite

/-- The gain of a HIGH parent `h` with eight copies of each marked slot. -/
def selectedGainK (n low h : Source) (b ν : ℝ) : ℝ :=
  QRH.RepeatedMarks.gainK ν 8 (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) (b-2*(n.allowance:ℝ))
    (sourceFReal n low b-(n.allowance:ℝ))

/-- Collet's `ActualGaps` for a HIGH parent, with the repeated-mark gain. The cell condition of
the common-width payment (Lemma C) travels with the gaps. -/
def ActualGapsK (n low h : Source) (b ν reserve : ℝ) : Prop :=
  reserve≤1-sourceBase n low b ν+selectedGainK n low h b ν-(n.highFee:ℝ) ∧
    (∀j, reserve≤familyGap n low b ν j) ∧
    0≤b-2*(n.allowance:ℝ) ∧ 2*(b-2*(n.allowance:ℝ))≤sourceFReal n low b-(n.allowance:ℝ)

theorem actualGapsK_mono {n low h : Source} {b ν r s : ℝ} (hrs : r≤s)
    (hg : ActualGapsK n low h b ν s) : ActualGapsK n low h b ν r :=
  ⟨hrs.trans hg.1, fun j=>hrs.trans (hg.2.1 j), hg.2.2⟩

/-- The available marked width is positive on the whole cell. -/
theorem slot_width_pos (n low : Source) (high : Option Source) (hv : SourceValidC n low high)
    {b : ℝ} (hb : b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) : 0<b-2*(n.allowance:ℝ) := by
  have hg := (hv.2.2.2.2.2.2.2.2.2.2.2.2 (crossing n low) (by simp)).1 1
  have h1 : (0:ℚ)<crossing n low-2*n.allowance := by simpa [scalarGate] using hg
  have h2 : (0:ℝ)<(crossing n low:ℝ)-2*(n.allowance:ℝ) := by exact_mod_cast h1
  linarith [hb.1]

/-- The reserve is chosen before every width, density and later finite family. -/
theorem nf_actual_uniform_reserve_K (n low h : Source) (hv : SourceValid2 n low (some h)) :
    ∃reserve : ℝ,0<reserve ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ν∈Set.Icc (n.q:ℝ) (3/4),ActualGapsK n low h b ν reserve := by
  obtain ⟨hC,hH,hq34,hcell⟩ := hv
  obtain ⟨δ,hδ,hall⟩ := nfC_uniform_margin n low (some h) hC
  have hgood := hC.2.2.2.2.2.2.2.2.2.2.2.1 h (by simp)
  have hq : (1/2:ℝ)≤n.q := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hC.2.2.2.2.2.1
    norm_num at hh
    exact hh
  have hB0 : (22/23:ℝ)≤h.B := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hgood.1
    norm_num at hh
    exact hh
  have hB1 : (h.B:ℝ)≤1 := by exact_mod_cast hgood.2.1
  have hL : 1<(h.L:ℝ) := by exact_mod_cast hgood.2.2.1
  have hc0 : 0≤(h.cap:ℝ) := by exact_mod_cast hgood.2.2.2.1
  have hc1 : (h.cap:ℝ)≤1 := by exact_mod_cast hgood.2.2.2.2.le
  obtain ⟨r1,hr1,hres⟩ := high_uniform_reserve n low h 8 (by norm_num) hC.2.2.2.2.2.1 hq34
    hB0 hB1 hL hc0 hc1 (hH h (by simp))
  refine ⟨min r1 (δ/12),lt_min hr1 (by positivity),?_⟩
  intro b hb ν hν
  have hS := slot_width_pos n low (some h) hC hb
  have hF : 0≤sourceFReal n low b-(n.allowance:ℝ) := by
    have hc := cell_ratio_full n low hcell hb
    linarith
  refine ⟨?_,?_,hS.le,cell_ratio_full n low hcell hb⟩
  · have hr := hres b hb ν hν hS.le hF
    push_cast at hr
    exact (min_le_left _ _).trans hr
  · have hfam := family_reserve (high:=some h) (hq.trans hν.1) hν.2 hδ (le_refl (12:ℝ))
      (fun j=>(hall b hb ν hν).2.2 _ (Or.inr (by simp [familyIndex])))
    intro j
    exact (min_le_right _ _).trans (hfam j)

end
end QRH.RepeatedMarks.Source
