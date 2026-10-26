import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondFullNormalizedContraction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open CenteredMomentLogDyadic CenteredMomentSectorLocalization

/-- A common four-dyad box bounds the ratio image even when arbitrarily
many source labels share the same dyads. -/
theorem second_ratio_bins_card_le_box {Label : Type*} [Fintype Label]
    (s : Label → SecondBlockSource) (box : Finset (Fin 4 → ℤ))
    (hbox : ∀ l, (s l).dyad ∈ box) :
    (secondRatioBins s).card ≤ box.card := by
  let ratio := fun n : Fin 4 → ℤ => n 0 + n 1 - n 2 - n 3
  have hsub : secondRatioBins s ⊆ box.image ratio := by
    intro r hr
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr ⟨(s l).dyad, hbox l, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Pay the ratio overhead from its actual shared box. This estimate
does not bound the normalized energy; that remains a separate input. -/
theorem second_ratio_decay_le_box {Label : Type*} [Fintype Label]
    (s : Label → SecondBlockSource) (box : Finset (Fin 4 → ℤ))
    (hbox : ∀ l, (s l).dyad ∈ box) (E : ℝ) (hE : 0 ≤ E) (A : ℕ) :
    (∑ r ∈ secondRatioBins s, E / (1 + dyadicScale r)^A) ≤ (box.card : ℝ)*E := by
  have hcount : ((secondRatioBins s).card : ℝ) ≤ box.card := by
    exact_mod_cast second_ratio_bins_card_le_box s box hbox
  calc
    _ ≤ ∑ _r ∈ secondRatioBins s, E := Finset.sum_le_sum (fun r _ =>
      div_le_self hE (one_le_pow₀ (by linarith [dyadicScale_pos r])))
    _ = ((secondRatioBins s).card : ℝ)*E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hE

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
