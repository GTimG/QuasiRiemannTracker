/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A positive measured maximum picks a genuine original slot with a width
floor fixed before the varying slot scales and frequency rows. -/
import Candidate.C092.transport.TinyCoreSlots
import Candidate.C092.transport.LowActualResponse

namespace QRH.Cycle092.AttainingMark
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentWholeSlotDeletion CenteredMomentHeckeSlots
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O

theorem maximum_attained {ι : Type*} [Fintype ι] (U pay b F : ℝ) (w amp : ι → ℝ)
    (hU : 1 < U) (hp : 0 < pay) (hb : 0 ≤ b) (hF : 0 ≤ F)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ amp i) (hcap : ∀ i, amp i ≤ F*U^(w i))
    (hpay : F*U^b ≤ pay) (he : 0 < response U pay w amp) :
    ∃ i : ι, b < w i ∧ amp i = pay*U^(response U pay w amp*w i) := by
  obtain ⟨o,_,ho⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ) (H:=⟨none,Finset.mem_univ _⟩)
    (fun i : Option ι => i.elim 0 (fun j => slotResponse U pay (w j) (amp j)))
  change response U pay w amp = _ at ho
  cases o with
  | none => simp only [Option.elim_none] at ho; linarith
  | some i =>
    change response U pay w amp = slotResponse U pay (w i) (amp i) at ho
    have hwi : 0 < w i := lt_of_le_of_ne (hw i) (by intro hz; rw [ho] at he; simp [slotResponse,←hz] at he)
    have hai : 0 < amp i := lt_of_le_of_ne (ha i) (by intro hz; rw [ho] at he; simp [slotResponse,←hz] at he)
    have h : response U pay w amp*w i = Real.logb U (amp i/pay) := by
      rw [ho]; exact div_mul_cancel₀ _ hwi.ne'
    have hval : amp i = pay*U^(response U pay w amp*w i) := by
      rw [h,Real.rpow_logb (zero_lt_one.trans hU) hU.ne' (div_pos hai hp)]; field_simp
    have ha' : pay < amp i := by
      conv_rhs => rw [hval]
      exact lt_mul_of_one_lt_right hp (Real.one_lt_rpow hU (mul_pos he hwi))
    refine ⟨i,lt_of_not_ge (fun hh => ?_),hval⟩
    exact ha'.not_ge ((hcap i).trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hh) hF).trans hpay))

variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_OriginalAttainingMark_e02ba912e02a6ae3_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem original_attaining_width {ι : Type*} [Fintype ι]
    (W : ℝ→ℂ) (hW : Continuous W) (hs : Function.support W ⊆ Set.Icc (1:ℝ) 2) :
    ∃ F : ℝ, 0 < F ∧ ∀ (U pay b : ℝ), 1 < U → 0 ≤ b → F*U^b ≤ pay →
      ∀ (η η₀ : Character) (m A z : O) (t : ℝ)
        (θ : ι → RayQuotient.Characters M H) (w σ v : ι → ℝ), (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ σ i) →
      let S := originalPools M H 2 U w
      let c := originalCoefficients M H hH η₀ θ W U w σ v
      let P := fun i => U^(w i)
      let amp := fun i => ‖normalizedSlot η m A z (S i) (c i) t (P i)‖^2
      0 < response U pay w amp →
      ∃ i : ι, b < w i ∧ amp i = pay*U^(response U pay w amp*w i) := by
  obtain ⟨B,hB,hc⟩ := TinyCore.original_slot_coefficient_bound W hW hs
  refine ⟨(256*B)^2,by positivity,?_⟩
  intro U pay b hU hb hpay η η₀ m A z t θ w σ v hw hσ
  dsimp only
  intro he
  have hUp := zero_lt_one.trans hU
  apply maximum_attained U pay b ((256*B)^2) w _ hU ((by positivity : 0 < (256*B)^2*U^b).trans_le hpay)
    hb (sq_nonneg _) hw (fun _ => sq_nonneg _) _ hpay he
  intro i
  let P := U^(w i)
  have hp : 0<P := Real.rpow_pos_of_pos hUp _
  let S := originalPools M H 2 U w i
  let c := originalCoefficients M H hH η₀ θ W U w σ v i
  have hh := rowSlot_bound η m A z S c t (2*P) B (by positivity) hB.le (fun I _ => hc _ _ _ _ I hp (hσ i))
    (fun I _ hI => TinyCore.original_slot_norm_cap W hs _ _ _ _ I hp hI)
  change ‖(Real.sqrt P:ℂ)⁻¹*rowSlot η m A z S c t‖^2 ≤ (256*B)^2*P
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hp]
  apply (div_le_iff₀ hp).mpr
  nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hh 2]

#print axioms original_attaining_width
end
end QRH.Cycle092.AttainingMark
