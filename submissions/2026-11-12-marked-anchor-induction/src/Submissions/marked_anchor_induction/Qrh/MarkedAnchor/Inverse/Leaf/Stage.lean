/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Leaf.Child
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Reduction
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Anchor.ChainData

/-!
# Inverse.Leaf.Stage — the inverse child of one anchor step

Stage point: established anchor `(R, z)`, `S_R = (1-R)/2 + z`, cut `k`, new free width `r ≤ R`,
`h = H = r/R`, `u = fu R r = (1-H)/6`, `Y = fY R z k r`, stage decrement `D` (`= δ = 4·10^-8` in
the chain), anchor decrement `β > 0`, reduction slack `κ > 0`. The new (parent) inverse rectangle is
`anchorRect r (Y - D) β = ⟨r-β, (1-r)/2 + (Y-D) - β⟩`. The child of the reduction has free width
`≤ r-β+2κ`, marks `≤ (1-r)/2+(Y-D)-β-u+3κ` (absolute), and is normalized at a radius `Hc` with
`H-κ ≤ Hc ≤ H+κ`: `childRectAt … Hc`. The reduction's `childRect` is `Hc = 1-6u-κ = H-κ`.

LOW: previous anchor `anchorRect R z (β/2)`. The ledger uses the identity
`s0 = H S_R + u/k` (proved as a ring identity at every real `r`):
`k·(Sc - Sp)·Hc = u - kD - kβ(1-Hc/2) + 3kκ + k S_R (H-Hc) ≤ u - kD - kβ/2 + k(3+S_R+β/2)κ`,
i.e. the stage balance `k·need - u = -k·δ` with the extra reserve `kβ/2` and the slack `κ`.
Hence the LOW price is at most the excess `x = a/Hc` (absolute excess `a` at the child radius)
whenever `u - kD - kβ/2 + k(3+S_R+β/2)κ ≤ a`; `a = u` is the child budget `H + u`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Leaf
noncomputable section

open Qrh.MarkedAnchor.Interface.Contract
open Qrh.MarkedAnchor.Anchor.ChainData

/-- The child rectangle normalized at radius `Hc`. -/
def childRectAt (Pmax Smax u κ Hc : ℝ) : AnchorRect :=
  ⟨(Pmax+2*κ)/Hc, (Smax-u+3*κ)/Hc⟩

theorem childRect_eq_at (Pmax Smax u κ : ℝ) :
    childRect Pmax Smax u κ = childRectAt Pmax Smax u κ (1-6*u-κ) := rfl

theorem fu_nonneg {R r : ℝ} (hR : 0 < R) (hrR : r ≤ R) : 0 ≤ fu R r := by
  unfold fu
  have : r/R ≤ 1 := (div_le_one hR).mpr hrR
  linarith

theorem one_sub_six_fu {R r : ℝ} : 1-6*fu R r = r/R := by unfold fu; ring

/-- The free-width gate of the child against the previous anchor. -/
theorem stage_child_pmax {R r β κ Hc : ℝ} (hR : 0 < R) (hrR : r ≤ R) (hβR : β/2 ≤ R)
    (hHc0 : 0 < Hc) (hHc1 : r/R - κ ≤ Hc) (hκP : (2+R)*κ ≤ β/2) (hβ : 0 < β) (hκ : 0 < κ) :
    (r-β+2*κ)/Hc ≤ R-β/2 := by
  rw [div_le_iff₀ hHc0]
  have hRh : R*(r/R) = r := mul_div_cancel₀ r hR.ne'
  have hh1 : r/R ≤ 1 := (div_le_one hR).mpr hrR
  have hβh : β*(r/R) ≤ β := mul_le_of_le_one_right hβ.le hh1
  have h1 : (R-β/2)*(r/R-κ) ≤ (R-β/2)*Hc := mul_le_mul_of_nonneg_left hHc1 (by linarith)
  have ex : (R-β/2)*(r/R-κ) = R*(r/R) - R*κ - β*(r/R)/2 + β*κ/2 := by ring
  have e2 : (2+R)*κ = 2*κ + R*κ := by ring
  have hβκ : 0 ≤ β*κ := mul_nonneg hβ.le hκ.le
  rw [ex, hRh] at h1
  linarith

/-- The LOW ledger of the stage at normalization radius `Hc`: `k·(Sc - Sp) ≤ x`. -/
theorem stage_child_ledger {R z k r D β κ Hc x : ℝ} (hR : 0 < R) (hrR : r ≤ R) (hk : 0 < k)
    (hβ : 0 < β) (hSR : 0 ≤ (1-R)/2 + z) (hHc0 : 0 < Hc) (hHc2 : Hc ≤ r/R + κ)
    (hHc1 : r/R - κ ≤ Hc)
    (hxled : fu R r - k*D - k*(β/2) + k*((3 + ((1-R)/2+z) + β/2)*κ) ≤ x*Hc) :
    k*(((1-r)/2 + (fY R z k r - D) - β - fu R r + 3*κ)/Hc - ((1-R)/2 + z - β/2)) ≤ x := by
  have hne : Hc ≠ 0 := hHc0.ne'
  set A : ℝ := (1-r)/2 + (fY R z k r - D) - β - fu R r + 3*κ with hA
  set SR : ℝ := (1-R)/2 + z with hSRdef
  have hAk : A/Hc*Hc = A := div_mul_cancel₀ A hne
  have e : k*(A/Hc - (SR - β/2))*Hc = k*(A/Hc*Hc) - k*(SR - β/2)*Hc := by ring
  rw [hAk] at e
  have hRh : R*(r/R) = r := mul_div_cancel₀ r hR.ne'
  have hkq : k*(1/k) = 1 := by field_simp
  have hid : k*A = k*(r/R)*SR + fu R r - k*D - k*β + 3*k*κ := by
    rw [hA, hSRdef]
    simp only [fY, fu]
    linear_combination (k/2) * hRh + ((1 - r/R)/6) * hkq
  have hh1 : r/R ≤ 1 := (div_le_one hR).mpr hrR
  have hkb : 0 ≤ k*β := mul_nonneg hk.le hβ.le
  have hkS : 0 ≤ k*SR := mul_nonneg hk.le hSR
  -- `k S_R (H - Hc) ≤ k S_R κ` and `k β Hc / 2 ≤ k β (1+κ)/2`
  have hb1 : k*SR*(r/R - Hc) ≤ k*SR*κ := mul_le_mul_of_nonneg_left (by linarith) hkS
  have hb2 : k*β*Hc ≤ k*β*(1+κ) := mul_le_mul_of_nonneg_left (by linarith) hkb
  have e3 : k*((3 + SR + β/2)*κ) = 3*k*κ + k*SR*κ + k*β*κ/2 := by ring
  have e4 : k*SR*(r/R - Hc) = k*(r/R)*SR - k*SR*Hc := by ring
  have e5 : k*β*(1+κ) = k*β + k*β*κ := by ring
  have hmain : k*(A/Hc - (SR - β/2))*Hc ≤ x*Hc := by
    rw [e]
    have e6 : k*(SR - β/2)*Hc = k*SR*Hc - k*β*Hc/2 := by ring
    rw [e6, hid]
    linarith
  exact le_of_mul_le_mul_right hmain hHc0

/-- **The inverse child of a stage at normalization radius `Hc`**, excess `x`. -/
theorem inverse_child_stage_at (fam : SlotClass → Prop) (hsub : ∀ cls, fam cls → SubClosed cls)
    (R z k r D β κ Hc x : ℝ) (hR : 0 < R) (hrR : r ≤ R) (hk : 0 < k) (hβ : 0 < β) (hκ : 0 < κ)
    (hHc0 : 0 < Hc) (hHc1 : r/R - κ ≤ Hc) (hHc2 : Hc ≤ r/R + κ)
    (hκP : (2+R)*κ ≤ β/2) (hβS : β/2 ≤ (1-R)/2 + z) (hβR : β/2 ≤ R) (hx : 0 ≤ x)
    (hxled : fu R r - k*D - k*(β/2) + k*((3 + ((1-R)/2+z) + β/2)*κ) ≤ x*Hc)
    (hprev : ∀ δ' : ℝ, 0 < δ' → UniformInverseRectSource fam (anchorRect R z δ'))
    (hhigh : InverseHighEnergy fam
      (childRectAt (r-β) ((1-r)/2 + (fY R z k r - D) - β) (fu R r) κ Hc) k x) :
    UniformInverseRectSourceExcess fam
      (childRectAt (r-β) ((1-r)/2 + (fY R z k r - D) - β) (fu R r) κ Hc) x := by
  refine inverse_child_of_prev fam hsub (ρp := anchorRect R z (β/2)) hk.le hx ?_ ?_ ?_
    (hprev (β/2) (by linarith)) hhigh
  · show (r-β+2*κ)/Hc ≤ R-β/2
    exact stage_child_pmax hR hrR hβR hHc0 hHc1 hκP hβ hκ
  · show 0 ≤ (1-R)/2 + z - β/2
    linarith
  · show k*(((1-r)/2 + (fY R z k r - D) - β - fu R r + 3*κ)/Hc - ((1-R)/2 + z - β/2)) ≤ x
    exact stage_child_ledger hR hrR hk hβ (by linarith) hHc0 hHc2 hHc1 hxled

/-- Absolute form: excess `a/Hc` (absolute excess `a` at the child radius `Hc`). -/
theorem inverse_child_stage_abs (fam : SlotClass → Prop) (hsub : ∀ cls, fam cls → SubClosed cls)
    (R z k r D β κ Hc a : ℝ) (hR : 0 < R) (hrR : r ≤ R) (hk : 0 < k) (hβ : 0 < β) (hκ : 0 < κ)
    (hHc0 : 0 < Hc) (hHc1 : r/R - κ ≤ Hc) (hHc2 : Hc ≤ r/R + κ)
    (hκP : (2+R)*κ ≤ β/2) (hβS : β/2 ≤ (1-R)/2 + z) (hβR : β/2 ≤ R) (ha : 0 ≤ a)
    (hled : fu R r - k*D - k*(β/2) + k*((3 + ((1-R)/2+z) + β/2)*κ) ≤ a)
    (hprev : ∀ δ' : ℝ, 0 < δ' → UniformInverseRectSource fam (anchorRect R z δ'))
    (hhigh : InverseHighEnergy fam
      (childRectAt (r-β) ((1-r)/2 + (fY R z k r - D) - β) (fu R r) κ Hc) k (a/Hc)) :
    UniformInverseRectSourceExcess fam
      (childRectAt (r-β) ((1-r)/2 + (fY R z k r - D) - β) (fu R r) κ Hc) (a/Hc) :=
  inverse_child_stage_at fam hsub R z k r D β κ Hc (a/Hc) hR hrR hk hβ hκ hHc0 hHc1 hHc2 hκP
    hβS hβR (div_nonneg ha hHc0.le) (by rw [div_mul_cancel₀ _ hHc0.ne']; exact hled) hprev hhigh

/-- **The reduction's child rectangle** (`Hc = 1-6u-κ`) with the excess `u/(1-6u-κ)` (child
budget `H + u`), under `(3+S_R+β/2)κ ≤ β/2` and `D ≥ 0`. -/
theorem inverse_child_stage_u (fam : SlotClass → Prop) (hsub : ∀ cls, fam cls → SubClosed cls)
    (R z k r D β κ : ℝ) (hR : 0 < R) (hrR : r ≤ R) (hk : 0 < k) (hD : 0 ≤ D) (hβ : 0 < β)
    (hκ : 0 < κ) (hrad : 6*fu R r + κ < 1) (hκP : (2+R)*κ ≤ β/2)
    (hκS : (3 + ((1-R)/2+z) + β/2)*κ ≤ β/2) (hβS : β/2 ≤ (1-R)/2 + z) (hβR : β/2 ≤ R)
    (hprev : ∀ δ' : ℝ, 0 < δ' → UniformInverseRectSource fam (anchorRect R z δ'))
    (hhigh : InverseHighEnergy fam
      (childRect (r-β) ((1-r)/2 + (fY R z k r - D) - β) (fu R r) κ) k
      (fu R r/(1-6*fu R r-κ))) :
    UniformInverseRectSourceExcess fam
      (childRect (r-β) ((1-r)/2 + (fY R z k r - D) - β) (fu R r) κ)
      (fu R r/(1-6*fu R r-κ)) := by
  have hpos : 0 < 1-6*fu R r-κ := by linarith
  have e : 1-6*fu R r-κ = r/R - κ := by rw [one_sub_six_fu]
  have h1 := mul_le_mul_of_nonneg_left hκS hk.le
  have h2 : 0 ≤ k*D := mul_nonneg hk.le hD
  exact inverse_child_stage_abs fam hsub R z k r D β κ (1-6*fu R r-κ) (fu R r) hR hrR hk hβ hκ
    hpos (by rw [e]) (by rw [e]; linarith) hκP hβS hβR (fu_nonneg hR hrR) (by linarith)
    hprev hhigh

end
end Qrh.MarkedAnchor.Inverse.Leaf

#print axioms Qrh.MarkedAnchor.Inverse.Leaf.inverse_child_stage_at
#print axioms Qrh.MarkedAnchor.Inverse.Leaf.inverse_child_stage_abs
#print axioms Qrh.MarkedAnchor.Inverse.Leaf.inverse_child_stage_u
