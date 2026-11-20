/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The actual independently colored native SideFrame retains original
sources, labels, scalar weights, envelope and packed-row divisor fibres.
Whole-frame child selection starts from the full original label set after
forming the literal colored source; no old coefficient carrier is used.
-/
import Candidate.C092.transport.RegularColoredFrameNativeClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open QRH.Record1252270103KernelMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

def framegEnergy (ω₁ ω₂ η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (v : ℝ) : ℝ :=
  if h : Fits η r x then
    (x.G.absNorm:ℝ)*(x.D.absNorm:ℝ)*pairNorm x.d*r.norm*frameRawEnergy ω₁ ω₂ η r x h v else 0

theorem framegEnergy_nonneg (ω₁ ω₂ η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (v : ℝ) :
    0≤framegEnergy ω₁ ω₂ η r x v := by
  unfold framegEnergy
  split_ifs with h
  · have hraw : 0≤frameRawEnergy ω₁ ω₂ η r x h v := by
      unfold frameRawEnergy frameLabelEnergy
      exact CenteredMomentRestrictedSourceNormalization.sourceRestrictedEnergy_nonneg _ _ _ _ _ _
        (dyadicScale_pos _) (fun _=>ballProfile_nonneg _)
    have hn : 0≤r.norm := div_nonneg (Real.rpow_nonneg (zero_lt_one.trans r.hZ).le _) (sq_nonneg _)
    have hp : 0≤pairNorm x.d := by unfold pairNorm; positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp) hn) hraw
  · exact le_rfl

def frameSideFrame (L : ℝ) (θ : GData L) (mesh : ℝ) (ω₁ ω₂ η : Character) (Z : ℝ) : QRH.SilDensitySplit.CubeFree.Second.SideFrame :=
  { gFrame L θ mesh η Z with
    energy := framegEnergy ω₁ ω₂ η
    energy_nonneg := framegEnergy_nonneg ω₁ ω₂ η }

/-- Actual whole-frame selection on the original label set, after the
literal colored source has been formed. Only nonpositive energy labels
are omitted. No cancellation-dependent coefficient carrier is substituted. -/
theorem frame_select_actual_labels (θ : GData L) (ε : ℝ) (hε : 0<ε) (δ : ℝ) (hδ : 0<δ) :
    ∃ Cred : ℝ,0<Cred ∧ ∀ (mesh Z : ℝ),mesh≤1 → ∀ (η ω₁ ω₂ : Character)
      (r : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z)) (v : ℝ),
    ∃ c : GLabel θ mesh Z→Finset (Fin θ.N)×ℝ×ℝ,
      let good := labels.filter (fun x=>0<gWeight x*framegEnergy ω₁ ω₂ η r x v)
      (∀x∈good,Fits η r x ∧ 0<(c x).2.1 ∧ 0<(c x).2.2 ∧
        (((c x).2.1≤r.X₁ ∧ (c x).2.2≤r.X₂) ∨ ((c x).2.1≤r.Y₁ ∧ (c x).2.2≤r.Y₂))) ∧
      (∑x∈labels,gWeight x*framegEnergy ω₁ ω₂ η r x v) ≤ r.norm *
        ∑x∈good,frameExtractionWeight Cred ε δ r x*
          frameChildE ω₁ ω₂ η r v (x.anchor r) (c x).1 (c x).2.1 (c x).2.2
            (r.V₀*x.twist) (dyadicScale (x.n 1)) := by
  obtain ⟨Cred,hCred,hred⟩ := frame_label_reduction_native θ ε hε δ hδ
  refine ⟨Cred,hCred,?_⟩
  intro mesh Z hmesh η ω₁ ω₂ r labels v
  have hn : 0≤r.norm := div_nonneg (Real.rpow_nonneg (zero_lt_one.trans r.hZ).le _) (sq_nonneg _)
  have hpn (x : GLabel θ mesh Z) : 0≤(x.G.absNorm:ℝ)*(x.D.absNorm:ℝ)*pairNorm x.d := by
    have hp : 0≤pairNorm x.d := by unfold pairNorm; positivity
    positivity
  have hsel : ∀x∈labels,∃ c : Finset (Fin θ.N)×ℝ×ℝ,
      gWeight x*framegEnergy ω₁ ω₂ η r x v≤0 ∨
      (Fits η r x ∧ 0<c.2.1 ∧ 0<c.2.2 ∧
        ((c.2.1≤r.X₁ ∧ c.2.2≤r.X₂) ∨ (c.2.1≤r.Y₁ ∧ c.2.2≤r.Y₂)) ∧
        gWeight x*framegEnergy ω₁ ω₂ η r x v≤r.norm*
          (frameExtractionWeight Cred ε δ r x*frameChildE ω₁ ω₂ η r v (x.anchor r) c.1 c.2.1 c.2.2
            (r.V₀*x.twist) (dyadicScale (x.n 1)))) := by
    intro x hx
    by_cases hf : Fits η r x
    · rcases hred mesh Z hmesh η ω₁ ω₂ r x hf v with h0 | ⟨A,X₁,X₂,hX₁,hX₂,hXY,he⟩
      · refine ⟨(∅,1,1),Or.inl ?_⟩
        unfold framegEnergy
        rw [dif_pos hf]
        exact mul_nonpos_of_nonneg_of_nonpos (gWeight_nonneg x)
          (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hpn x) hn) h0)
      · refine ⟨(A,X₁,X₂),Or.inr ⟨hf,hX₁,hX₂,hXY,?_⟩⟩
        unfold framegEnergy
        rw [dif_pos hf]
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left he (mul_nonneg (hpn x) hn)) (gWeight_nonneg x)
        exact hh.trans_eq (by unfold frameExtractionWeight; ring)
    · exact ⟨(∅,1,1),Or.inl (by simp only [framegEnergy,dif_neg hf,mul_zero,le_refl])⟩
  choose! c hc using hsel
  refine ⟨c,?_,?_⟩
  · intro x hx
    obtain ⟨hx,hpos⟩ := Finset.mem_filter.mp hx
    rcases hc x hx with hn | ⟨hf,hX₁,hX₂,hXY,he⟩
    · exact False.elim (not_le.mpr hpos hn)
    · exact ⟨hf,hX₁,hX₂,hXY⟩
  · rw [←Finset.sum_filter_add_sum_filter_not labels (fun x=>0<gWeight x*framegEnergy ω₁ ω₂ η r x v)]
    have hneg : (∑x∈labels.filter (fun x=>¬0<gWeight x*framegEnergy ω₁ ω₂ η r x v),
        gWeight x*framegEnergy ω₁ ω₂ η r x v)≤0 :=
      Finset.sum_nonpos (fun x hx=>not_lt.mp (Finset.mem_filter.mp hx).2)
    apply (add_le_of_nonpos_right hneg).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    obtain ⟨hx,hpos⟩ := Finset.mem_filter.mp hx
    rcases hc x hx with hn | ⟨hf,hX₁,hX₂,hXY,he⟩
    · exact False.elim (not_le.mpr hpos hn)
    · exact he

#print axioms frameSideFrame
#print axioms framegEnergy_nonneg
#print axioms frame_select_actual_labels
end
end QRH.Cycle092.RegularColoredForward
