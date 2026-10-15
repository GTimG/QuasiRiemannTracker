import Candidate.Cycle62.Marked.DeletionFiniteExceptions
import Candidate.Cycle62.Marked.DeletionMaxAmplitude

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckeInverseAmplification ProbePhysical LocalMoment
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- The complete small-root transfer: the actual raw/core slot comparison,
the rescaled marked core estimate and the finite removed initial rows
produce the precise fiber input consumed by the raw sixth-power lift. -/
theorem small_root_marked_fiber_from_core {Slot : Type*}
    (R : Finset NonzeroFrequency) (B : NZIdeal) (E : Finset FreeRow)
    (slots : Finset Slot) (Qraw : NonzeroFrequency→Slot→ℂ) (Qcore : FreeRow→Slot→ℂ)
    (U C κ ρ δ S g cap loss : ℝ)
    (hU : 1<U) (hC : 0≤C) (hκ : κ<1/6)
    (hB : (B.val.absNorm : ℝ)≤U^κ) (hg : 0≤g) (hcap : 0≤cap)
    (hloss : 0≤loss) (hρ : g*cap≤ρ) (hρ0 : 0≤ρ)
    (hpoint : ∀u∈sixthFreeFiber R B,‖∏s∈slots,Qraw (sixthFrequencyEquiv (u,B)) s‖^2≤U^(δ*S+loss))
    (hclose : ∀u∈sixthFreeFiber R B,u∉E → ∀s∈slots,
      ‖Qraw (sixthFrequencyEquiv (u,B)) s-Qcore u s‖≤1/2)
    (hcore : ∀d : ℝ,0<d → 1-6*κ≤d → d≤1 → U^d=U/(B.val.absNorm : ℝ)^6 →
      (∑u∈(sixthFreeFiber R B).filter (fun u=>u∉E),
        (∏s∈slots,max 1 ‖Qcore u s‖)^2) ≤
        C*(U^d)^(ρ+δ*(S/d)-g*min (S/d) cap+loss)) :
    (∑u∈sixthFreeFiber R B,‖∏s∈slots,Qraw (sixthFrequencyEquiv (u,B)) s‖^2) ≤
      ((4:ℝ)^slots.card*C+(E.card:ℝ))*
        (U^(δ*S+loss-g*min S (cap*(1-6*κ)))*(U/(B.val.absNorm : ℝ)^6)^ρ) := by
  have hBN : 1≤(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hUp : 0<U := zero_lt_one.trans hU
  obtain ⟨d,hd,hd₀,hd1,hbase,hscale⟩ := core_window_scale U _ κ hU hBN hκ hB
  have hpow := rescaled_marked_power U d (1-6*κ) ρ δ S g cap loss hU.le hd hd₀ hd1 hg hcap hloss
  rw [hbase] at hpow
  have hgain : g*min S (cap*(1-6*κ))≤(1-6*κ)*ρ := by
    have h1 := mul_le_mul_of_nonneg_left (min_le_right S (cap*(1-6*κ))) hg
    have h2 := mul_le_mul_of_nonneg_right hρ (show 0≤1-6*κ by linarith)
    nlinarith
  have henv := small_root_exception_envelope U (B.val.absNorm : ℝ) κ ρ
    (δ*S+loss) (g*min S (cap*(1-6*κ))) hU hBN hB hρ0 hgain
  apply finite_exception_weighted_extension (sixthFreeFiber R B) E
    (fun u=>‖∏s∈slots,Qraw (sixthFrequencyEquiv (u,B)) s‖^2)
    ((4:ℝ)^slots.card*C) (U^(δ*S+loss)) _ (by positivity) henv hpoint
  calc
    _ ≤ (4:ℝ)^slots.card * ∑u∈(sixthFreeFiber R B).filter (fun u=>u∉E),
          (∏s∈slots,max 1 ‖Qcore u s‖)^2 := by
      rw [Finset.mul_sum]
      have hh := Finset.sum_le_sum (s := (sixthFreeFiber R B).filter (fun u=>u∉E))
        (fun u hu=>slot_product_comparison slots (Qraw (sixthFrequencyEquiv (u,B))) (Qcore u)
          (hclose u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2))
      convert hh using 1
      · congr 1
        ext u
        simp
    _ ≤ (4:ℝ)^slots.card*(C*(U^d)^(ρ+δ*(S/d)-g*min (S/d) cap+loss)) :=
      mul_le_mul_of_nonneg_left (hcore d hd hd₀ hd1 hbase) (pow_nonneg (by norm_num) _)
    _ ≤ (4:ℝ)^slots.card*(C*(U^(δ*S-g*min S (cap*(1-6*κ))+loss)*
          (U/(B.val.absNorm : ℝ)^6)^ρ)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      apply mul_le_mul_of_nonneg_left _ hC
      rwa [hbase]
    _ = _ := by rw [show δ*S-g*min S (cap*(1-6*κ))+loss = δ*S+loss-g*min S (cap*(1-6*κ)) by ring];ring

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.small_root_marked_fiber_from_core
