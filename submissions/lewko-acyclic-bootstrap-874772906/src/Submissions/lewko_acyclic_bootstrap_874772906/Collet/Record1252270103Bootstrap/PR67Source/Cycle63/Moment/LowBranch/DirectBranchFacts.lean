import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.DirectDeletion
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The direct deletion of a first-level LOW child of the unit width that is too narrow for the second step is paid by
the amplifier, the allowance of its labels and the reserve of the cell. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section

/-- A first-level LOW child of the unit width whose nominal width `ν`, widened by `δ`, is below the least width `Mstar`
of the second step is paid by the direct deletion at the rate `κq`. The log norms are those of the own first ideal
`c`, the other first ideal `d`, the active conductor `R`, the own second ideal `e`, the common radical `p₂`, the common
frequency generator `g₂`, the inactive set `t₂` and the nonunit frequency generator `V`. The child has the capacity
`x₁ + x₂ + 6 κ rem - ν` at most `gbar + 6 a + omega + spad` less its extraction `min c d + (e - g₂) + t₂`. The deficit
of the deletion at zero extraction, the reserve `L` and the slacks fit in the room of the cell. The overshoot of the
deletion, the amplifier `a`, the allowance `Bσ + e - p₂` of the labels and the reserve `L` then satisfy the conditions
of the direct deletion with the padding `omega + εpad`. -/
theorem direct_branch_facts {κq κ a gbar L c d R e p₂ g₂ t₂ V x₁ x₂ rem ν δ omega spad εpad ωmax δmax Mstar : ℝ}
    (hκq : 0 ≤ κq) (hκq2 : κq ≤ 1 / 2)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hRd : R ≤ d) (hp₂ : p₂ ≤ e) (hL : L ≤ a)
    (ht₂ : 0 ≤ t₂) (homega : 0 ≤ omega) (hεpad : 0 ≤ εpad) (hδ : 0 ≤ δ) (hspad : spad ≤ εpad)
    (hωmax : omega ≤ ωmax) (hδmax : δ ≤ δmax)
    (hνdef : ν = 1 - (max (c - d) 0 + g₂ - t₂) - 6 * a - omega)
    (hV : V + t₂ ≤ ν + δ)
    (hprime : κq * (g₂ - t₂ - V) ≤ (e - p₂) + κq * ((e - g₂) + t₂))
    (hN4 : x₁ + x₂ + 6 * κ * rem - ν ≤ gbar + 6 * a + omega + spad - (min c d + ((e - g₂) + t₂)))
    (hnarrow : ν + δ < Mstar)
    (hcert : (κq * (gbar + 6 * a) - a) + L + κq * (δmax + εpad) + 2 * κq * ωmax ≤
      κq * (1 - 6 * a - 2 * Mstar)) :
    0 ≤ max (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0 ∧
    x₁ + x₂ + 6 * κ * rem - ν ≤ max (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0 + (omega + εpad) ∧
    κq * max (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0 ≤
      a + (max (3 * c - 5 * d - R) 0 / 6 + (e - p₂)) - L := by
  have hεs : 0 ≤ omega + εpad := add_nonneg homega hεpad
  set v := max (c - d) 0 + g₂ - t₂ with hv
  set G := max (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0 with hG
  -- the selection of the width reduction
  have hsel : (κq * (gbar + 6 * a) - a) + κq * (omega + εpad) + L ≤ κq * (max (c - d) 0 + g₂ - t₂ - V) := by
    have hnum : (κq * (gbar + 6 * a) - a) + (L + κq * (δ + εpad)) ≤ κq * (1 - 6 * a - 2 * (Mstar + omega - δ)) := by
      have h1 := mul_le_mul_of_nonneg_left hδmax hκq
      have h2 := mul_le_mul_of_nonneg_left hωmax hκq
      have h3 := mul_nonneg hκq hδ
      nlinarith [h1, h2, h3, hcert]
    have h := direct_deletion_selection (κq := κq) (a := a) (gbar := gbar) (ω := omega + εpad)
      (L := L + κq * (δ + εpad)) (Mstar := Mstar + omega - δ) (v := v) (vN := V - δ - εpad)
      (M1 := ν - εpad) hκq (by rw [hνdef]; ring) (by linarith) (by rw [hνdef] at hnarrow; linarith) hnum
    have h4 : κq * (v - (V - δ - εpad)) = κq * (max (c - d) 0 + g₂ - t₂ - V) + κq * (δ + εpad) := by
      rw [hv]; ring
    linarith only [h, h4]
  -- the reserve of the direct deletion
  have hres := direct_deletion_slack_nonneg (κq := κq) (a := a) (gbar := gbar) (ω := omega + εpad) (L := L)
    (c := c) (d := d) (R := R) (s := e) (p₂ := p₂) (g := g₂) (t := t₂) (vN := V) (r := 0) (f := 0) (κ6 := 0)
    hκq hκq2 le_rfl le_rfl le_rfl hc hd hRd hp₂ hL hprime hsel
  have hGle : G ≤ max (gbar + 6 * a + (omega + εpad) - (min c d + (e - g₂) + t₂ + 0 + 0 * 0)) 0 := by
    apply max_le_max _ le_rfl
    linarith only [hεs]
  have hκG := mul_le_mul_of_nonneg_left hGle hκq
  refine ⟨le_max_right _ _, ?_, ?_⟩
  · have := le_max_left (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0
    linarith only [hN4, hspad, this]
  · have h2 : κq * max (gbar + 6 * a + (omega + εpad) - (min c d + (e - g₂) + t₂ + 0 + 0 * 0)) 0 ≤
        a + (max (3 * c - 5 * d - R) 0 / 6 + (e - p₂)) - L := by
      linarith only [hres]
    exact hκG.trans h2

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
