import WeightedQRH.NumeratorLabelPrimeBound
import WeightedQRH.NumeratorLabelReconstruction

/-! Actual error-label coefficient mass, with every physical prime label summed
and with the final subpower loss chosen independently of the label count. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actual_physical_label_mass (epsilon c d B : ℝ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (W : ι → ℝ → ℂ) (Y : ι → ℝ),
      (∀ i, 1 ≤ Y i) → (∀ i, Function.support (W i) ⊆ Set.Icc c d) →
      (∀ i y, ‖W i y‖ ≤ B) → ∀ (x z : ℂ) (alpha eps rho Ccond Cu : ℝ),
      (51 / 100 : ℝ) ≤ alpha → alpha ≤ 1 → 0 < eps → eps ≤ 1 / 1000 →
      x.re = alpha + 16 * eps → z.re = 17 / 50 → 0 ≤ rho → rho ≤ 1 →
      1 - alpha - 6 * eps ≤ 1 / 2 - rho → -(1 / 100 : ℝ) ≤ 1 / 2 - rho →
      1 + firsteps ≤ x.re + (1 / 2 - rho) →
      0 < Ccond → 0 ≤ Cu → Cu ≤ Ccond * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) →
      let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
      let weight : ∀ i, T i → ℂ := fun i P => physicalSlotWeight P.val (W i) (Y i) z
      Summable (fun e : LabelPacketIndex S u T => ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ∧
      (∑' e : LabelPacketIndex S u T, ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon * ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
  obtain ⟨C1,hC1,hmass⟩ := actual_label_packet_mass (ι:=ι) (epsilon/2) (by linarith)
  obtain ⟨C2,hC2,hprime⟩ := error_label_prime_product_bound (epsilon/2) c d B (Fintype.card ι)
    (by linarith) hc hd hB
  refine ⟨C1*C2,mul_pos hC1 hC2,?_⟩
  intro S hS firsteps hfirst η u T hT hdis hη W Y hY hWS hWB x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  let weight : ∀ i, T i → ℂ := fun i P => physicalSlotWeight P.val (W i) (Y i) z
  obtain ⟨hs,hm⟩ := hmass S hS firsteps hfirst η u T hT hdis hη weight x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  refine ⟨hs,hm.trans ?_⟩
  have hp := hprime ι le_rfl u T Y W hY hWS hWB z hz
  change (∏ i, ∑ P : T i, 2880*‖weight i P‖*errorSize u P.val) ≤ _ at hp
  have hNu : (0 : ℝ) < (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  calc
    _ ≤ (C1*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2)) *
        (C2*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2) * ∏ i, (Y i)^(-(4 / 25 : ℝ))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      rw [show (C1*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2)) *
          (C2*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2) * ∏ i, (Y i)^(-(4 / 25 : ℝ))) =
          (C1*C2)*((((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2))*
          (((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2))) * ∏ i, (Y i)^(-(4 / 25 : ℝ)) by ring]
      rw [←Real.rpow_add hNu,show epsilon/2+epsilon/2=epsilon by ring]

end WeightedQRH.Numerator
