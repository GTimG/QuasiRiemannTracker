/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The early attaining-width banks permit both inverse and native repeat counts
to be chosen after scale, from a packet family fixed before that scale. -/
import Candidate.C092.transport.SourceInverseP6Price
import Candidate.C092.transport.SourceInverseP6Unmarked

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open Filter

theorem finite_repeat_packets {Packet : Type*} (Ki Kl : ℕ)
    (valid : ℕ → ℕ → Packet → Prop) (bound : ℕ → ℕ → Packet → ℝ → Prop)
    (h : ∀ ki,ki ≤ Ki → ∀ kl,kl ≤ Kl → ∃ p : Packet,valid ki kl p ∧
      ∀ᶠ U : ℝ in atTop,bound ki kl p U) :
    ∃ packets : Fin (Ki+1) → Fin (Kl+1) → Packet,
      (∀ ki kl,valid ki.val kl.val (packets ki kl)) ∧
      ∀ᶠ U : ℝ in atTop,∀ (ki : Fin (Ki+1)) (kl : Fin (Kl+1)),
        bound ki.val kl.val (packets ki kl) U := by
  choose packets hv he using fun (ki : Fin (Ki+1)) (kl : Fin (Kl+1)) =>
    h ki.val (Nat.le_of_lt_succ ki.isLt) kl.val (Nat.le_of_lt_succ kl.isLt)
  refine ⟨packets,hv,?_⟩
  exact Filter.eventually_all.mpr (fun ki => Filter.eventually_all.mpr (he ki))

#print axioms finite_repeat_packets
end
end QRH.Cycle092.SourceInverseP6
