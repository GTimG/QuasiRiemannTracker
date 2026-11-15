/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Native and reserve ordinary suppliers above an arbitrary legal seed. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.EarlierGrid
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafMarkedInput

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.High.Marked
noncomputable section
open Qrh.MarkedAnchor.Interface.Native Qrh.TwoSlot.AnchorZeroLoss.High

def sourcePad : ℝ := 1/10000000000000

theorem selection_cases {a0 a1 x S : ℝ} (hS : S≤sig a0 a1 x) :
    S≤0 ∨ S≤(1-x)/2+(a0-a1*x)-sourcePad := by
  change S≤max 0 ((1-x)/2+(a0-a1*x)-sourcePad) at hS
  rcases le_total 0 ((1-x)/2+(a0-a1*x)-sourcePad) with h | h
  · rw [max_eq_right h] at hS; exact Or.inr hS
  · rw [max_eq_left h] at hS; exact Or.inl hS

theorem top_line_bound {T a0 a1 x : ℝ} (ha : 0≤a1) (ha1 : a1≤2/5)
    (hl : a0-a1*T≤0) (hx : T-sourcePad≤x) :
    a0-a1*x≤(2/5)*sourcePad := by
  have hp : 0<sourcePad := by norm_num [sourcePad]
  nlinarith

/-- The native inverse gates hold above any seed in the enlarged seed range. -/
theorem native_gates_above_seed {T a0 a1 : ℝ} (hT : 3/4≤T)
    (ha : 0≤a1) (ha1 : a1≤2/5) (hl : a0-a1*T≤0)
    (x S : ℝ) (hx : T-sourcePad≤x) (hx1 : x<1) (hS0 : 0≤S)
    (hS : S≤sig a0 a1 x) : x+2*S<1 ∧ 2*x+8*S<3 := by
  have hlx := top_line_bound ha ha1 hl hx
  rcases selection_cases hS with hs | hs
  · have heq : S=0 := le_antisymm hs hS0
    subst S
    constructor <;> linarith
  · norm_num [sourcePad] at hlx hs hx
    constructor <;> linarith

/-- The single reserve source is fixed before all physical arithmetic data.
Its cap and source budget both retain their actual positive decrement. -/
theorem ordinary_source_above_seed (hres : ReserveParametricSource) :
    ∃ B L c : ℝ, QRH.Record1252270103Source.GlobalSource B L c ∧ 0≤L ∧
      ∀ T a0 a1 : ℝ,3/4≤T → 0≤a1 → a1≤2/5 → a0-a1*T≤0 →
      ∀ x S : ℝ,T-sourcePad≤x → x<1 → 0<S → S≤sig a0 a1 x →
        x+L*S≤B ∧ S≤c := by
  have hp : 0<sourcePad := by norm_num [sourcePad]
  obtain ⟨B,L,c,hsrc,hL0,hL,hB,hc⟩ := hres (sourcePad/10) (by positivity)
  refine ⟨B,L,c,hsrc,hL0,?_⟩
  intro T a0 a1 hT ha ha1 hl x S hx hx1 hS0 hS
  have hlx := top_line_bound ha ha1 hl hx
  rcases selection_cases hS with hs | hs
  · linarith
  · have hSsmall : S≤3/20-sourcePad/10 := by
      norm_num [sourcePad] at hlx hs hx ⊢
      linarith
    have hLS := mul_le_mul_of_nonneg_right hL hS0.le
    constructor
    · norm_num [sourcePad] at hlx hs hx hLS hSsmall hB
      nlinarith
    · exact hSsmall.trans hc

/-- The complete actual HIGH marked input supplied by preceding anchors.
All finite rectangle meshes are chosen before the physical data and heights. -/
theorem markedCore_of_earlier
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (R T wlo a0 a1 : ℝ) (hR : R<wlo) (hwlo : 0≤wlo)
    (hTlo : 3/4≤T) (hThi : T≤7/9)
    (ha : 0≤a1) (ha1 : a1≤2/5) (hl : a0-a1*T≤0)
    (hprior : ∀r : ℝ,R<r → r≤T → ∃z : ℝ,0≤z ∧ a0-a1*r≤z ∧
      Qrh.MarkedAnchor.Interface.Contract.AnchorAt r z) :
    MarkedCoreR1 a0 a1 wlo := by
  obtain ⟨N,ρ,hsrc,hcov⟩ := finite_grid_of_earlier R T wlo a0 a1 0 sourcePad (sourcePad/10)
    hR hwlo hThi ha ha1 (by norm_num [sourcePad]) (by norm_num [sourcePad])
    (by norm_num [sourcePad]) (by norm_num [sourcePad])
    (by norm_num [sourcePad]; nlinarith)
    (fun r hr hrT=>by simpa only [add_zero] using hprior r hr hrT)
  obtain ⟨B,L,c,hG,hL0,hGcov⟩ := ordinary_source_above_seed hres
  have hM := markedCoreR1_of_sources hβ a0 a1 wlo (T-sourcePad) B L c
    (native_gates_above_seed hTlo ha ha1 hl) N ρ hsrc hcov hG hL0
    (hGcov T a0 a1 hTlo ha ha1 hl)
  exact hM

/-- Bounded-height consumer form of the same common source supplier. -/
theorem highMarkedCoreInputs_of_earlier
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (R T wlo a0 a1 : ℝ) (hR : R<wlo) (hwlo : 0≤wlo)
    (hTlo : 3/4≤T) (hThi : T≤7/9)
    (ha : 0≤a1) (ha1 : a1≤2/5) (hl : a0-a1*T≤0)
    (hprior : ∀r : ℝ,R<r → r≤T → ∃z : ℝ,0≤z ∧ a0-a1*r≤z ∧
      Qrh.MarkedAnchor.Interface.Contract.AnchorAt r z) :
    HighMarkedCoreInputsH a0 a1 wlo := by
  have h := r1_of_marked (markedCore_of_earlier hβ hres R T wlo a0 a1
    hR hwlo hTlo hThi ha ha1 hl hprior)
  exact h

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Marked
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Marked.native_gates_above_seed
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Marked.ordinary_source_above_seed

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Marked.highMarkedCoreInputs_of_earlier

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Marked.markedCore_of_earlier
