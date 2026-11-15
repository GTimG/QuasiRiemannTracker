/- Copyright (c) 2026 Sil. Apache-2.0.
Modified by Joseph Bebel (2026-11-12): zero-stage-decrement ordinary anchor.
Derived from PR137 Price/Gates and Price/Stage at pinned head
9d81a4c0b0e8338ef458f3ba5139657ae5404fde. The old checkpoint is unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Price.Stage
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.Price.Leaf

/-!
A zero-stage-decrement variant of Sil's ordinary analytic step. The prior
rectangle is used at the strictly positive decrement β/4. The output still
has every requested positive decrement β. HIGH is an abstract physical
supplier with its actual price; no HIGH estimate is introduced here.
-/
set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss
noncomputable section
open QRH.SilDensitySplit.CubeFree
open Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract (OrdinaryRectSource anchorRect
  anchorRect_restricts)

/-! ### Step data -/

/-- **Per-stage step data** of the ordinary anchor step at `r` with decrement `β`. -/
def stageData (F : ParentFace) (R z k r β : ℝ) (high : QRH.SilDensitySplit.CubeFree.Price)
    (hk : 0 ≤ k) (hβ : 0 < β) : Ordinary.StepData where
  B₀ := F.B₀
  L₀ := F.L₀
  c₀ := F.c₀
  B := r - β
  L := 0
  c := (1-r)/2 + (fY R z k r - (0 : ℝ)) - β
  κ := 3/4
  s₀ := (F.B₀ - (r - β))/F.L₀
  Hmin := 1/2
  Hmax := 3
  sel := fun _ w => min (fu R r) w
  price := anchorPrice k (R - (β/4)) (β/4) ((1-R)/2 + z - (β/4)) hk (div_pos hβ (by norm_num))
    high
  lref := 7/50
  alpha := 3/5
  Pref := 2/3

section Gates
variable (F : ParentFace) {R z k r : ℝ} (hS : StageHyp R z k r)
  (high : QRH.SilDensitySplit.CubeFree.Price) (hH : HighAt high R z k r) (hk0 : 0 ≤ k)
  {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000)

/-- The target width `c` in terms of `fS`. -/
theorem stage_c_eq : (stageData F R z k r β high hk0 hβ0).c = fS R z k r - (0 : ℝ) - β := by
  show (1-r)/2 + (fY R z k r - (0 : ℝ)) - β = fS R z k r - (0 : ℝ) - β
  unfold fS; ring

include hS hβ0 hβ1 in
/-- The reference gates of the fork with reserve `ρ = 1/100` (gates 2, 4, 6). -/
theorem stage_reference : Ordinary.ReferenceAt (stageData F R z k r β high hk0 hβ0) (1/100) := by
  have hc := stage_c_eq F high hk0 (r := r) (z := z) (R := R) hβ0
  have hu0 := hS.u_nonneg
  have g2 := hS.g2
  have g4 := hS.g4
  have g6 := hS.g6
  have hu := hS.hu
  refine ⟨by norm_num, show (0:ℝ) < 7/50 by norm_num, show 2*(7/50:ℝ) < 2/3 by norm_num,
    show (0:ℝ) < 3/5 by norm_num, show (3/5:ℝ) < 2/3 by norm_num, ?_, ?_, ?_⟩
  · show (1:ℝ)/100 ≤ 1 - (r - β); linarith [hS.hr.2, hS.hR.2]
  · show (1:ℝ)/100 ≤ 1 - (r - β) - (1 - 0)*(stageData F R z k r β high hk0 hβ0).c
    rw [hc]; linarith
  · intro ε _ S hs0 hSc
    rw [hc] at hSc
    have hsel : min (fu R r) S ≤ fu R r := min_le_left _ _
    refine ⟨?_, ?_, ?_⟩
    · show (1:ℝ)/100 ≤ 5/6 + 3/5*(7/50) - (r - β) - (1 - 0)*S - 3*min (fu R r) S
      linarith
    · show (1:ℝ)/100 ≤ 5/6 - 2/3 - S - 3*min (fu R r) S
      linarith
    · show (1:ℝ)/100 ≤ (1 - (r - β)) + (0 - 1)*S - 4*min (fu R r) S
      linarith

include hS hH hβ0 hβ1 in
/-- **The ledger** `price ≤ u + ε/16` at every side above the floor `ε/12`, with mesh and
frequency tolerance `≤ min (β/64) (ε/(256(lip+1)))`. -/
theorem stage_ledger (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ × ℝ × ℝ, Ordinary.LedgerAt (stageData F R z k r β high hk0 hβ0) ε p.1 p.2.1 p.2.2 := by
  have hlip := high.lip_nonneg
  set m : ℝ := min (β/64) (ε/(256*(high.lip+1))) with hmdef
  have hm0 : 0 < m := lt_min (div_pos hβ0 (by norm_num)) (div_pos hε (by linarith))
  have hmβ : m ≤ β/64 := min_le_left _ _
  have hmε : high.lip*m ≤ ε/256 := by
    have h1 : m ≤ ε/(256*(high.lip+1)) := min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith
  refine ⟨(ε/12, m, m), show (0:ℝ) < ε/12 from div_pos hε (by norm_num), ?_, hm0, hm0, ?_⟩
  · show ε/12 ≤ ε/(16*(3/4:ℝ)); norm_num
  intro mesh hmesh0 hmeshL tl htl0 htlL g hfloor
  change mesh ≤ m at hmeshL
  change tl ≤ m at htlL
  -- the side data, unfolded
  obtain ⟨_, hSc⟩ := g.hS
  obtain ⟨hf0, hfcg⟩ := g.hf
  have hroot := g.hroot
  obtain ⟨hsel1, hsel2⟩ := g.hsel
  obtain ⟨hs0, hs1⟩ := g.hs
  obtain ⟨ht1, ht2⟩ := g.ht
  have hc := stage_c_eq F high hk0 (r := r) (z := z) (R := R) hβ0
  rw [hc] at hSc
  change g.PC + (g.cg - g.f) + 0*g.S ≤ r - β + tl at hroot
  change min (fu R r) (g.S - g.f) ≤ g.u at hsel1
  change g.u ≤ min (fu R r) (g.S - g.f) + mesh at hsel2
  change ε/12 ≤ g.S - g.f at hfloor
  change (1/2:ℝ) ≤ 1 + g.t - 6*g.u ∧ 1 + g.t - 6*g.u ≤ 3 ∧
    (anchorPrice k (R - (β/4)) (β/4) ((1-R)/2 + z - (β/4)) hk0 (div_pos hβ0 (by norm_num))
      high).f (g.S - g.f) g.PC g.s (1 + g.t - 6*g.u) ≤ g.u + ε/16
  rw [anchorPrice_f]
  -- scalar facts
  have hu0 := hS.u_nonneg
  have hu := hS.hu
  have hHeq := hS.H_eq
  have hH1 := hS.H_le_one
  have hRH := hS.RH
  have hsid := hS.s_identity
  have hR := hS.hR
  have hk := hS.hk
  have hkpos := hS.k_pos
  have hSR := hS.hSR
  have hSlow := hS.S_lower
  have hz := hS.hz
  have g2 := hS.g2
  have hd1 : 0 < β/4 := by linarith
  set u₀ := fu R r with hu₀
  set H₀ := fH R r with hH₀
  set x := tl + 6*mesh with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxm : x ≤ 7*m := by rw [hx]; linarith
  have hule : g.u ≤ u₀ + mesh := hsel2.trans (by linarith [min_le_left u₀ (g.S - g.f)])
  have hPC : g.PC ≤ r - β + tl := by linarith
  have hHlo : H₀ - x ≤ 1 + g.t - 6*g.u := by linarith
  have hlipx : high.lip*(tl + x) ≤ ε/32 := by
    have : tl + x ≤ 8*m := by rw [hx]; linarith
    have := mul_le_mul_of_nonneg_left this hlip
    linarith
  refine ⟨by linarith, by linarith, ?_⟩
  -- HIGH: from the stage point `(r, s*, H₀)` by monotonicity and the Lipschitz bounds
  have high_bound : ∀ s' : ℝ, g.s ≤ s' →
      high.f (g.S - g.f) g.PC g.s (1 + g.t - 6*g.u) ≤
        high.f (g.S - g.f) r s' H₀ + ε/32 := by
    intro s' hs'
    have e1 := high.mono (g.S - g.f) (r + tl) g.PC s' g.s (1 + g.t - 6*g.u) (by linarith) hs'
    have e2 := hH.antiM (g.S - g.f) (r + tl) s' (H₀ + -x) (1 + g.t - 6*g.u) (by linarith)
    have e3 := high.lipM (g.S - g.f) (r + tl) s' H₀ (-x)
    rw [abs_neg, abs_of_nonneg hx0] at e3
    have e4 := high.lipP (g.S - g.f) r s' H₀ tl htl0
    have : high.lip*tl + high.lip*x = high.lip*(tl + x) := by ring
    linarith
  by_cases hw : u₀ ≤ g.S - g.f
  · -- a full selection `u ≥ u*`
    have hsel : min u₀ (g.S - g.f) = u₀ := min_eq_left hw
    rw [hsel] at hsel1
    have hss : g.s ≤ fs R z k r := by
      have : fs R z k r = fS R z k r - u₀ := rfl
      linarith
    refine max_le ?_ ?_
    · -- LOW: the previous anchor at radius `H₀ - x`
      set B₁ := R - (β/4) with hB₁
      set c₁ := (1-R)/2 + z - (β/4) with hc₁
      set ℓ : ℝ := β/4 with hℓ
      have hℓ0 : 0 < ℓ := by rw [hℓ]; linarith
      have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; linarith
      have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; linarith
      have hc₁1 : c₁ ≤ 1 := by rw [hc₁]; linarith
      have hn1 : deletionNeed B₁ ℓ c₁ g.PC g.s (1 + g.t - 6*g.u) ≤
          deletionNeed B₁ ℓ c₁ (r - β + tl) (fS R z k r - (0 : ℝ) - β - u₀) (H₀ - x) :=
        (deletionNeed_mono hℓ0 hPC (by linarith)).trans
          (deletionNeed_antiM hℓ0 hB₁0 hc₁0 hHlo)
      have hn2 := deletionNeed_le_max B₁ ℓ c₁ (r - β + tl) (fS R z k r - (0 : ℝ) - β - u₀)
        (H₀ - x)
      -- the cap defect: `k X = u* + k (H₀ δ₁ - δ - β + c₁ x)`
      have hX : k*((fS R z k r - (0 : ℝ) - β - u₀) - c₁*(H₀ - x)) ≤ u₀ := by
        have e : fS R z k r - u₀ = H₀*((1-R)/2 + z) + u₀/k := hsid
        have e2 : k*((fS R z k r - (0 : ℝ) - β - u₀) - c₁*(H₀ - x)) =
            u₀ + k*(H₀*(β/4) - (0 : ℝ) - β + c₁*x) := by
          have : fS R z k r - (0 : ℝ) - β - u₀ = H₀*((1-R)/2 + z) + u₀/k - (0 : ℝ) - β := by
            linarith
          have hkne : k ≠ 0 := hkpos.ne'
          have hku : k*(u₀/k) = u₀ := by field_simp
          rw [this, hc₁]; linear_combination hku
        have q1 : H₀*(β/4) ≤ (β/4) := mul_le_of_le_one_left hd1.le hH1
        have q2 : c₁*x ≤ x := mul_le_of_le_one_left hx0 hc₁1
        have hQ : H₀*(β/4) - (0 : ℝ) - β + c₁*x ≤ 0 := by linarith
        have := mul_nonpos_of_nonneg_of_nonpos hk0 hQ
        linarith
      -- the budget defect is negative: `P + ℓ s - B₁ M < 0`
      have hY : (r - β + tl + ℓ*(fS R z k r - (0 : ℝ) - β - u₀) - B₁*(H₀ - x))/ℓ < 0 := by
        apply div_neg_of_neg_of_pos _ hℓ0
        have e1 : B₁*(H₀ - x) = r - (β/4)*H₀ - R*x + (β/4)*x := by
          rw [hB₁]; linear_combination hRH
        have q1 : (β/4)*H₀ ≤ (β/4) := mul_le_of_le_one_right hd1.le hH1
        have q2 : 0 ≤ (β/4)*x := mul_nonneg hd1.le hx0
        have q3 : R*x ≤ x := mul_le_of_le_one_left hx0 (by linarith)
        have q4 : ℓ*(fS R z k r - (0 : ℝ) - β - u₀) ≤ ℓ*(1/6) :=
          mul_le_mul_of_nonneg_left (by linarith) hℓ0.le
        rw [e1]
        linarith
      have hmax : max 0 (max ((fS R z k r - (0 : ℝ) - β - u₀) - c₁*(H₀ - x))
          ((r - β + tl + ℓ*(fS R z k r - (0 : ℝ) - β - u₀) - B₁*(H₀ - x))/ℓ)) ≤
          max 0 ((fS R z k r - (0 : ℝ) - β - u₀) - c₁*(H₀ - x)) :=
        max_le (le_max_left _ _) (max_le (le_max_right _ _) (hY.le.trans (le_max_left _ _)))
      have hkX : k * max 0 ((fS R z k r - (0 : ℝ) - β - u₀) - c₁*(H₀ - x)) ≤ u₀ := by
        rcases le_total ((fS R z k r - (0 : ℝ) - β - u₀) - c₁*(H₀ - x)) 0 with h0 | h0
        · rw [max_eq_left h0, mul_zero]; exact hu0
        · rw [max_eq_right h0]; exact hX
      have hk1 := mul_le_mul_of_nonneg_left (hn1.trans (hn2.trans hmax)) hk0
      linarith
    · -- HIGH
      have := high_bound (fs R z k r) hss
      have h2 : high.f (g.S - g.f) r (fs R z k r) H₀ ≤ u₀ := hH.ledger _
      linarith
  · -- not enough live marks: everything selected, `s ≤ 0`
    replace hw : g.S - g.f < u₀ := lt_of_not_ge hw
    have hsel : min u₀ (g.S - g.f) = g.S - g.f := min_eq_right hw.le
    rw [hsel] at hsel1
    have hsn : g.s ≤ 0 := by linarith
    refine max_le ?_ ?_
    · rw [deletionNeed_of_nonpos hsn, mul_zero]
      linarith
    · have := high_bound 0 hsn
      have h2 : high.f (g.S - g.f) r 0 H₀ ≤ 0 := hH.empty _
      linarith

include hS hH hβ0 hβ1 in
/-- **The step gates** of the ordinary anchor step at a stage point. -/
theorem stageGates : Ordinary.StepGates (stageData F R z k r β high hk0 hβ0) where
  face := by
    have hc := stage_c_eq F high hk0 (r := r) (z := z) (R := R) hβ0
    have hSl := hS.S_lower
    have g2 := hS.g2
    refine ⟨?_, F.hB.2, F.hL, le_rfl, ?_, ?_, F.hc.2⟩
    · show r - β ≤ F.B₀; linarith [hS.hr.2, hS.hR.2, F.hB.1]
    · rw [hc]; linarith [hS.hr.2, hS.hR.2]
    · rw [hc]; linarith
  kappa := rfl
  crossing := by
    have hL := F.hL
    refine ⟨?_, ?_, fun _ => ?_⟩
    · show 0 ≤ (F.B₀ - (r - β))/F.L₀
      exact div_nonneg (by linarith [hS.hr.2, hS.hR.2, F.hB.1]) hL.le
    · show (F.L₀ - 0)*((F.B₀ - (r - β))/F.L₀) ≤ F.B₀ - (r - β)
      have hL0 : F.L₀ ≠ 0 := hL.ne'
      rw [sub_zero]; exact le_of_eq (by field_simp)
    · show (F.B₀ - (r - β))/F.L₀ ≤ F.c₀
      rw [div_le_iff₀ hL]
      linarith [F.hcross, hS.hr.1]
  envelope := by
    show (0:ℝ) < 1/2 ∧ (1:ℝ)/2 < 1 ∧ (3:ℝ) ≤ 3
    norm_num
  sel_spec := by
    intro ε _
    have hu0 := hS.u_nonneg
    refine ⟨fun a _ b _ hab => min_le_min le_rfl hab, fun w hw _ => ⟨le_min hu0 hw, min_le_right _ _⟩⟩
  ledger := stage_ledger F hS high hH hk0 hβ0 hβ1
  reference := ⟨1/100, stage_reference F hS high hk0 hβ0 hβ1⟩

end Gates


/-- One actual ordinary source step with no fixed decrement in the stage gain. -/
theorem ordinary_stage_zero [shift : Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift] (F : ParentFace) {R z k r : ℝ}
    (hS : StageHyp R z k r) (high : QRH.SilDensitySplit.CubeFree.Price)
    (hH : HighAt high R z k r) (hk0 : 0 ≤ k)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000)
    (href : Ordinary.Reference.ReferenceLaneFine (stageData F R z k r β high hk0 hβ0))
    (hbeta : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hprev : ∀ δ' : ℝ, 0 < δ' → OrdinaryRectSource (anchorRect R z δ'))
    (hhigh : Qrh.TwoSlot.AnchorZeroLoss.High.HighBranchMesh high k) :
    OrdinaryRectSource (anchorRect r (fY R z k r) β) := by
  have G := stageGates F hS high hH hk0 hβ0 hβ1
  have hd1 : 0 < β/4 := by linarith
  have hsoft : QRH.Record1252270103Source.GlobalSource (R - β/4) (β/4)
      ((1-R)/2 + z - β/4) :=
    globalSource_soft (by linarith) (hprev (β/4) hd1)
  have hleaf : PricedPackedSource (stageData F R z k r β high hk0 hβ0).price
      (stageData F R z k r β high hk0 hβ0).Hmin
      ((stageData F R z k r β high hk0 hβ0).Hmax + 1) 4 :=
    Qrh.TwoSlot.AnchorZeroLoss.Price.anchor_priced_source (R - β/4) (β/4) ((1-R)/2 + z - β/4) k (1/2) (3+1) 4 high
      hd1 hk0 (by linarith [hS.hk.1]) (by linarith [hS.hk.2]) hbeta
      ⟨by linarith [hS.hR.1], by linarith [hS.hR.2],
        by linarith [hS.hR.2, hS.hz]⟩
      (by norm_num) (by norm_num) hsoft hhigh
  have hout := Ordinary.anchor_ordinary_step_four _ G href hbeta hparent hleaf
  change QRH.Record1252270103Source.GlobalSource (r - β) 0
    ((1-r)/2 + (fY R z k r - 0) - β) at hout
  change QRH.Record1252270103Source.GlobalSource (r - β) 0
    ((1-r)/2 + fY R z k r - β)
  simpa only [sub_zero] using hout

/-- All positive requested decrements, including those greater than .001. -/
theorem ordinary_stage_zero_all [shift : Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift] (F : ParentFace) {R z k r : ℝ}
    (hS : StageHyp R z k r) (high : QRH.SilDensitySplit.CubeFree.Price)
    (hH : HighAt high R z k r) (hk0 : 0 ≤ k)
    (href : ∀ β : ℝ, ∀ hβ0 : 0 < β, β ≤ 1/1000 →
      Ordinary.Reference.ReferenceLaneFine (stageData F R z k r β high hk0 hβ0))
    (hbeta : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hprev : ∀ δ' : ℝ, 0 < δ' → OrdinaryRectSource (anchorRect R z δ'))
    (hhigh : Qrh.TwoSlot.AnchorZeroLoss.High.HighBranchMesh high k) :
    ∀ β : ℝ, 0 < β → OrdinaryRectSource (anchorRect r (fY R z k r) β) := by
  intro β hβ
  by_cases hle : β ≤ 1/1000
  · exact ordinary_stage_zero F hS high hH hk0 hβ hle (href β hβ hle)
      hbeta hparent hprev hhigh
  · exact (ordinary_stage_zero F hS high hH hk0 (by norm_num : (0:ℝ) < 1/1000)
      le_rfl (href (1/1000) (by norm_num) le_rfl) hbeta hparent hprev hhigh).restrict
        (anchorRect_restricts (by linarith) (by linarith))

end
end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.ordinary_stage_zero_all
