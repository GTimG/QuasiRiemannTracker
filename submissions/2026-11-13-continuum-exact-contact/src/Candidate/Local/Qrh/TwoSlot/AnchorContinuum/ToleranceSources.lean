/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.Tolerances
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.TopSources

/-! Actual native and reserve sources for a variable coupled tolerance.
The finite earlier-anchor grid and physical HIGH consumers are separate. -/

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.Tolerances
noncomputable section
open Qrh.MarkedAnchor.Interface.Native

theorem selection_cases {q a0 a1 x S : ℝ} (hS : S ≤ sig q a0 a1 x) :
    S ≤ 0 ∨ S ≤ (1-x)/2+(a0-a1*x)-sourcePad q := by
  unfold sig at hS
  rcases le_total 0 ((1-x)/2+(a0-a1*x)-sourcePad q) with h | h
  · rw [max_eq_right h] at hS
    exact Or.inr hS
  · rw [max_eq_left h] at hS
    exact Or.inl hS

theorem top_line_bound {q T a0 a1 x : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a1) (ha1 : a1 ≤ 2/5)
    (hl : a0-a1*T ≤ 0) (hx : T-sourcePad q ≤ x) :
    a0-a1*x ≤ (2/5)*sourcePad q := by
  have hp : 0 < sourcePad q := div_pos hq (by norm_num)
  nlinarith

theorem native_gates_above_seed {q T a0 a1 : ℝ} (hq : 0 < q)
    (hqu : q ≤ 1/1000000000000) (hT : 3/4 ≤ T)
    (ha : 0 ≤ a1) (ha1 : a1 ≤ 2/5) (hl : a0-a1*T ≤ 0)
    (x S : ℝ) (hx : T-sourcePad q ≤ x) (hx1 : x < 1) (hS0 : 0 ≤ S)
    (hS : S ≤ sig q a0 a1 x) : x+2*S < 1 ∧ 2*x+8*S < 3 := by
  have hlx := top_line_bound hq ha ha1 hl hx
  rcases selection_cases hS with hs | hs
  · have heq : S=0 := le_antisymm hs hS0
    subst S
    constructor <;> linarith
  · unfold sourcePad at hlx hs hx
    constructor <;> linarith

/-- A genuine ordinary source with a positive tolerance chosen before the
arithmetic data. Its source budget and cap decrease together. -/
theorem ordinary_source_above_seed (hres : ReserveParametricSource)
    {q : ℝ} (hq : 0 < q) (hqu : q ≤ 1/1000000000000) :
    ∃ B L c : ℝ, QRH.Record1252270103Source.GlobalSource B L c ∧ 0 ≤ L ∧
      ∀ T a0 a1 : ℝ, 3/4 ≤ T → 0 ≤ a1 → a1 ≤ 2/5 → a0-a1*T ≤ 0 →
      ∀ x S : ℝ, T-sourcePad q ≤ x → x < 1 → 0 < S → S ≤ sig q a0 a1 x →
        x+L*S ≤ B ∧ S ≤ c := by
  have hp : 0 < sourcePad q := div_pos hq (by norm_num)
  obtain ⟨B,L,c,hsrc,hL0,hL,hB,hc⟩ := hres (sourcePad q/10) (by positivity)
  refine ⟨B,L,c,hsrc,hL0,?_⟩
  intro T a0 a1 hT ha ha1 hl x S hx hx1 hS0 hS
  have hlx := top_line_bound hq ha ha1 hl hx
  rcases selection_cases hS with hs | hs
  · linarith
  · have hSsmall : S ≤ 3/20-sourcePad q/10 := by
      unfold sourcePad at hlx hs hx ⊢
      linarith
    have hLS := mul_le_mul_of_nonneg_right hL hS0.le
    constructor
    · unfold sourcePad at hlx hs hx hLS hSsmall hB
      nlinarith
    · exact hSsmall.trans hc

/-- A finite grid of genuine paired rectangles for the variable source pad. -/
theorem source_grid_of_earlier {q : ℝ} (hq : 0 < q)
    (hqu : q ≤ 1/1000000000000)
    (R T wlo a0 a1 : ℝ) (hR : R < wlo) (hwlo : 0 ≤ wlo)
    (hThi : T ≤ 7/9) (ha : 0 ≤ a1) (ha1 : a1 ≤ 2/5)
    (hprior : ∀ r : ℝ, R < r → r ≤ T → ∃ z : ℝ, 0 ≤ z ∧ a0-a1*r ≤ z ∧
      Qrh.MarkedAnchor.Interface.Contract.AnchorAt r z) :
    ∃ (N : ℕ) (ρ : Fin N → Qrh.MarkedAnchor.Interface.Contract.AnchorRect),
      (∀ k, Qrh.MarkedAnchor.Interface.Contract.UniformInverseRectSource
        Qrh.MarkedAnchor.Interface.Contract.canonicalFamily (ρ k) ∧
        Qrh.MarkedAnchor.Interface.Contract.OrdinaryRectSource (ρ k)) ∧
      ∀ x : ℝ, wlo ≤ x → x < T-sourcePad q →
        ∃ k, (ρ k).Admissible x (sig q a0 a1 x) 1 := by
  have hp : 0 < sourcePad q := div_pos hq (by norm_num)
  apply Qrh.TwoSlot.AnchorZeroLoss.High.Marked.finite_grid_of_earlier_with_pad
    R T wlo a0 a1 0 (sourcePad q) (sourcePad q/10) (sourcePad q)
    hR hwlo hThi ha ha1 hp (by positivity)
  · unfold sourcePad
    linarith
  · linarith
  · nlinarith
  · simpa only [add_zero] using hprior

/-- Complete witness-free marked core moments at a variable coupled tolerance.
This supplies the actual inverse and ordinary polynomials with all their masks,
common profiles and height bounds; the physical HIGH leaf is a later consumer. -/
theorem markedCore_of_earlier
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource) {q : ℝ} (hq : 0 < q)
    (hqu : q ≤ 1/1000000000000)
    (R T wlo a0 a1 : ℝ) (hR : R < wlo) (hwlo : 0 ≤ wlo)
    (hTlo : 3/4 ≤ T) (hThi : T ≤ 7/9)
    (ha : 0 ≤ a1) (ha1 : a1 ≤ 2/5) (hl : a0-a1*T ≤ 0)
    (hprior : ∀ r : ℝ, R < r → r ≤ T → ∃ z : ℝ, 0 ≤ z ∧ a0-a1*r ≤ z ∧
      Qrh.MarkedAnchor.Interface.Contract.AnchorAt r z) :
    Qrh.TwoSlot.AnchorZeroLoss.High.Marked.MarkedCoreR1 a0 a1 wlo
      (sourcePad q) q := by
  obtain ⟨N,ρ,hsrc,hcov⟩ := source_grid_of_earlier hq hqu R T wlo a0 a1
    hR hwlo hThi ha ha1 hprior
  obtain ⟨B,L,c,hG,hL0,hGcov⟩ := ordinary_source_above_seed hres hq hqu
  exact Qrh.TwoSlot.AnchorZeroLoss.High.Marked.markedCoreR1_of_sources_with_tolerances
    hβ (sourcePad q) q a0 a1 wlo (T-sourcePad q) B L c
    (native_gates_above_seed hq hqu hTlo ha ha1 hl) N ρ hsrc hcov hG hL0
    (hGcov T a0 a1 hTlo ha ha1 hl)

/-- The same variable-tolerance moment supplier in the bounded-height,
supported-witness form required by the physical HIGH consumer. -/
theorem highMarkedCoreInputs_of_earlier
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource) {q : ℝ} (hq : 0 < q)
    (hqu : q ≤ 1/1000000000000)
    (R T wlo a0 a1 : ℝ) (hR : R < wlo) (hwlo : 0 ≤ wlo)
    (hTlo : 3/4 ≤ T) (hThi : T ≤ 7/9)
    (ha : 0 ≤ a1) (ha1 : a1 ≤ 2/5) (hl : a0-a1*T ≤ 0)
    (hprior : ∀ r : ℝ, R < r → r ≤ T → ∃ z : ℝ, 0 ≤ z ∧ a0-a1*r ≤ z ∧
      Qrh.MarkedAnchor.Interface.Contract.AnchorAt r z) :
    Qrh.TwoSlot.AnchorZeroLoss.High.HighMarkedCoreInputsH a0 a1 wlo
      (sourcePad q) q := by
  exact Qrh.TwoSlot.AnchorZeroLoss.High.Marked.r1_of_marked_with_tolerances
    (markedCore_of_earlier hβ hres hq hqu R T wlo a0 a1 hR hwlo
      hTlo hThi ha ha1 hl hprior)

end
end Qrh.TwoSlot.AnchorContinuum.Tolerances
