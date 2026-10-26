/- Copyright (c) 2026 Sil. Apache-2.0.
The actual finite selected block for the global source. Upward overshoot
costs one mesh in its size and improves, rather than harms, the slot gate.
Reuses the baseline's whole-slot selector; no lower bound on any slot.
 -/
import Candidate.FourthPower.MixedLedger
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotRemoval

set_option autoImplicit false
namespace Candidate.FourthPower.GlobalSlotSelection
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths.CenteredMomentSlotRemoval

/-- A direct specialization of the existing finite selector. Exhausting
the set is harmless because the target does not exceed its total width. -/
theorem upward_subset {ι : Type*} (J : Finset ι) (w : ι→ℝ)
    (target mesh : ℝ) (hm : 0≤mesh)
    (hw : ∀i∈J,0≤w i) (hwm : ∀i∈J,w i≤mesh)
    (ht : 0≤target) (hfull : target≤∑i∈J,w i) :
    ∃ R : Finset ι, R⊆J ∧ target≤∑i∈R,w i ∧
      (∑i∈R,w i)≤min (∑i∈J,w i) (target+mesh) := by
  obtain ⟨R,hR,hbound,hpay⟩ := whole_slot_removal J w mesh (1/6) target
    hm (by norm_num) ht hw hwm
  norm_num only [show (6:ℝ)*(1/6)=1 by norm_num,div_one,one_mul] at hbound hpay
  refine ⟨R,hR,?_,hbound⟩
  rcases hpay with he | hp
  · simpa only [he] using hfull
  · exact hp

/-- The two branches use TOTAL surviving width. Small slots are never
discarded individually, rounded up individually, or charged a mesh each. -/
def Specification {ι : Type*} (J : Finset ι) (w : ι→ℝ)
    (rho mesh : ℝ) (R : Finset ι) : Prop :=
  R⊆J ∧ ((∑i∈J,w i)≤rho → R=∅) ∧
    (rho<(∑i∈J,w i) →
      (43/100:ℝ)*(∑i∈J,w i)≤(∑i∈R,w i) ∧
      (∑i∈R,w i)≤min (∑i∈J,w i) ((43/100:ℝ)*(∑i∈J,w i)+mesh))

theorem exists_selection {ι : Type*} (J : Finset ι) (w : ι→ℝ)
    (rho mesh : ℝ) (hm : 0≤mesh)
    (hw : ∀i∈J,0≤w i) (hwm : ∀i∈J,w i≤mesh) :
    ∃ R : Finset ι, Specification J w rho mesh R := by
  classical
  have hS : 0≤∑i∈J,w i := Finset.sum_nonneg hw
  by_cases hsmall : (∑i∈J,w i)≤rho
  · refine ⟨∅,Finset.empty_subset _,fun _=>rfl,?_⟩
    intro hlarge
    exact (not_lt_of_ge hsmall hlarge).elim
  · obtain ⟨R,hR,hlo,hhi⟩ := upward_subset J w
      ((43/100:ℝ)*(∑i∈J,w i)) mesh hm hw hwm
      (by linarith) (by linarith)
    exact ⟨R,hR,fun h=>(hsmall h).elim,fun _=>⟨hlo,hhi⟩⟩

/-- A concrete finite subset supplied by the proved selector. This is
fixed by the slot widths, before any prime assignment is summed over. -/
def selectedSlots {ι : Type*} (J : Finset ι) (w : ι→ℝ)
    (rho mesh : ℝ) (hm : 0≤mesh)
    (hw : ∀i∈J,0≤w i) (hwm : ∀i∈J,w i≤mesh) : Finset ι :=
  Classical.choose (exists_selection J w rho mesh hm hw hwm)

theorem selectedSlots_spec {ι : Type*} (J : Finset ι) (w : ι→ℝ)
    (rho mesh : ℝ) (hm : 0≤mesh)
    (hw : ∀i∈J,0≤w i) (hwm : ∀i∈J,w i≤mesh) :
    Specification J w rho mesh (selectedSlots J w rho mesh hm hw hwm) :=
  Classical.choose_spec (exists_selection J w rho mesh hm hw hwm)

/-- On the floor branch D is the empty product and deleting all residual
slots costs at most 3*rho/4, independently of their number. -/
theorem small_branch {ι : Type*} (J R : Finset ι) (w : ι→ℝ)
    (rho mesh : ℝ) (hspec : Specification J w rho mesh R)
    (hsmall : (∑i∈J,w i)≤rho) :
    R=∅ ∧ (∑i∈R,w i)=0 ∧ (3/4:ℝ)*(∑i∈J\R,w i)≤3*rho/4 := by
  classical
  have he := hspec.2.1 hsmall
  refine ⟨he,?_,?_⟩
  · rw [he,Finset.sum_empty]
  · simpa only [he,Finset.sdiff_empty] using
      (show (3/4:ℝ)*(∑i∈J,w i)≤3*rho/4 by linarith)

/-- The actual complement has width exactly S-d. The upward overshoot
is beneficial here, so the reserve has no mesh loss. -/
theorem large_branch {ι : Type*} (J R : Finset ι) (w : ι→ℝ)
    (rho mesh : ℝ) (hrho : 0<rho)
    (hspec : Specification J w rho mesh R) (hlarge : rho<(∑i∈J,w i)) :
    (43/100:ℝ)*(∑i∈J,w i)≤(∑i∈R,w i) ∧
      (∑i∈R,w i)≤(43/100:ℝ)*(∑i∈J,w i)+mesh ∧
      (∑i∈J\R,w i)+(∑i∈R,w i)=(∑i∈J,w i) ∧
      (∑i∈J,w i)/400≤(∑i∈R,w i)-(3/4:ℝ)*(∑i∈J\R,w i) ∧
      rho/400<(∑i∈R,w i)-(3/4:ℝ)*(∑i∈J\R,w i) ∧
      (3/4:ℝ)*(∑i∈J\R,w i)<(∑i∈R,w i) := by
  classical
  obtain ⟨hlo,hhi⟩ := hspec.2.2 hlarge
  have hsplit := Finset.sum_sdiff hspec.1 (f:=w)
  have hreserve : (∑i∈J,w i)/400≤
      (∑i∈R,w i)-(3/4:ℝ)*(∑i∈J\R,w i) := by linarith
  refine ⟨hlo,hhi.trans (min_le_right _ _),hsplit,hreserve,?_,?_⟩
  · linarith
  · exact MixedLedger.slot_gate (by linarith) hlo (by linarith)

/-- A single aggregate enclosure error, not one error per slot. The
formula records exactly what reserve remains after that extra loss. -/
theorem gate_after_loss {S d s rho loss : ℝ} (hlarge : rho<S)
    (hd : (43/100:ℝ)*S≤d) (hs : s≤S-d) :
    rho/400-loss<d-(3/4:ℝ)*s-loss := by
  linarith

theorem gate_with_half_reserve {S d s rho loss : ℝ}
    (hrho : 0<rho) (hlarge : rho<S)
    (hd : (43/100:ℝ)*S≤d) (hs : s≤S-d) (hloss : loss≤rho/800) :
    rho/800<d-(3/4:ℝ)*s-loss ∧ (3/4:ℝ)*s+loss<d := by
  have h := gate_after_loss hlarge hd hs (loss:=loss)
  constructor <;> linarith

end
end Candidate.FourthPower.GlobalSlotSelection
