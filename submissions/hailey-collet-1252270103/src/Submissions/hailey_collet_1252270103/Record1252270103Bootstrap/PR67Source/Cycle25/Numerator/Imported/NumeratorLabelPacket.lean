import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.NumeratorErrorLabels
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Numerator.Imported.NumeratorPacketMellin
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.NumeratorLabelPacket
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! The complete coefficient packet after summing all physical error-prime labels. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance labelPacketIndex_countable (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) : Countable (WeightedQRH.Numerator.LabelPacketIndex S u T) := by
  unfold WeightedQRH.Numerator.LabelPacketIndex
  infer_instance

/-- Uniform in every error-label tuple, row, finite exclusion set and height. -/
theorem actual_label_packet_mass (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (_hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (_hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (_hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (weight : ∀ i, T i → ℂ) (x z : ℂ) (alpha eps rho Ccond Cu : ℝ),
      (51 / 100 : ℝ) ≤ alpha → alpha ≤ 1 → 0 < eps → eps ≤ 1 / 1000 →
      x.re = alpha + 16 * eps → z.re = 17 / 50 → 0 ≤ rho → rho ≤ 1 →
      1 - alpha - 6 * eps ≤ 1 / 2 - rho → -(1 / 100 : ℝ) ≤ 1 / 2 - rho →
      1 + firsteps ≤ x.re + (1 / 2 - rho) →
      0 < Ccond → 0 ≤ Cu → Cu ≤ Ccond * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) →
      let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
      Summable (fun e : WeightedQRH.Numerator.LabelPacketIndex S u T => ‖WeightedQRH.Numerator.labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (WeightedQRH.Numerator.labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(WeightedQRH.Numerator.labelPacketScale S u T e : ℝ))^rho) ∧
      (∑' e : WeightedQRH.Numerator.LabelPacketIndex S u T, ‖WeightedQRH.Numerator.labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (WeightedQRH.Numerator.labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(WeightedQRH.Numerator.labelPacketScale S u T e : ℝ))^rho) ≤
        (C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon) *
          ∏ i, ∑ P : T i, 2880 * ‖weight i P‖ * WeightedQRH.Numerator.errorSize u P.val := by
  obtain ⟨C,hC,hpref⟩ := WeightedQRH.Numerator.coefficient_prefactor_subpower epsilon hepsilon
  refine ⟨C,hC,?_⟩
  intro S hS firsteps hfirst η u T hT hdis hη weight x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
  have hL : 0 ≤ L := div_nonneg hCu0 (mul_nonneg hCcond.le (by positivity))
  let M := C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon
  have hpacket (P : ∀ i, T i) :
      Summable (fun e : WeightedQRH.Numerator.ErrorPacketIndex S u (WeightedQRH.Numerator.labelPrimes T P) =>
        ‖WeightedQRH.Numerator.errorPacketCoefficient S hS η u (WeightedQRH.Numerator.labelPrimes T P) (WeightedQRH.Numerator.labelSupported S hS T hT P) x z e‖ *
        (WeightedQRH.Numerator.errorPacketScale S u (WeightedQRH.Numerator.labelPrimes T P) e : ℝ)^(-(1 / 2 : ℝ)) *
        max 1 (L * (WeightedQRH.Numerator.errorPacketScale S u (WeightedQRH.Numerator.labelPrimes T P) e : ℝ))^rho) ∧
      (∑' e : WeightedQRH.Numerator.ErrorPacketIndex S u (WeightedQRH.Numerator.labelPrimes T P),
        ‖WeightedQRH.Numerator.errorPacketCoefficient S hS η u (WeightedQRH.Numerator.labelPrimes T P) (WeightedQRH.Numerator.labelSupported S hS T hT P) x z e‖ *
        (WeightedQRH.Numerator.errorPacketScale S u (WeightedQRH.Numerator.labelPrimes T P) e : ℝ)^(-(1 / 2 : ℝ)) *
        max 1 (L * (WeightedQRH.Numerator.errorPacketScale S u (WeightedQRH.Numerator.labelPrimes T P) e : ℝ))^rho) ≤
        M * WeightedQRH.Numerator.errorProductSize u (WeightedQRH.Numerator.labelPrimes T P) := by
    have hηP : ∀ Q ∈ WeightedQRH.Numerator.labelPrimes T P, IsCoprime Q.val η.modulus := by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hη i _ (P i).property
    have hQP : ∀ Q ∈ WeightedQRH.Numerator.labelPrimes T P, (4 : ℝ) ≤ Q.val.absNorm := by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact_mod_cast hS.tail.norm_four _ (hT i _ (P i).property)
    have hc := WeightedQRH.Numerator.actual_conductor_packet_cap u (WeightedQRH.Numerator.labelPrimes T P) (WeightedQRH.Numerator.labelSupported S hS T hT P)
      Ccond Cu hCcond hCu
    obtain ⟨hs,hm⟩ := WeightedQRH.Numerator.error_packet_damped_mass S hS firsteps hfirst η u (WeightedQRH.Numerator.labelPrimes T P)
      (WeightedQRH.Numerator.labelSupported S hS T hT P) hηP x z alpha eps rho L hQP halpha halpha1 heps heps1 hx hz
      hrho hrho1 hline hleft hmargin hL hc
    refine ⟨hs,hm.trans ?_⟩
    have hp := mul_le_mul_of_nonneg_right (hpref (markExclusions S (WeightedQRH.Numerator.labelPrimes T P)) u)
      (WeightedQRH.Numerator.errorProductSize_nonneg u (WeightedQRH.Numerator.labelPrimes T P))
    simpa only [mul_assoc,M] using hp
  have hh := WeightedQRH.Numerator.finite_label_damped_mass
    (fun P => WeightedQRH.Numerator.errorPacketCoefficient S hS η u (WeightedQRH.Numerator.labelPrimes T P) (WeightedQRH.Numerator.labelSupported S hS T hT P) x z)
    (fun P e => (WeightedQRH.Numerator.errorPacketScale S u (WeightedQRH.Numerator.labelPrimes T P) e : ℝ))
    (fun P e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast WeightedQRH.Numerator.errorPacketScale_one_le S u (WeightedQRH.Numerator.labelPrimes T P) e))
    (fun P => ∏ i, weight i (P i)) (fun P => WeightedQRH.Numerator.errorProductSize u (WeightedQRH.Numerator.labelPrimes T P)) L rho M
    (fun P => (hpacket P).1) (fun P => (hpacket P).2)
  refine ⟨hh.1,?_⟩
  change _ ≤ M * _
  exact hh.2.trans_eq (congrArg (fun t : ℝ => M*t) (WeightedQRH.Numerator.error_label_mass_factor u T hdis weight))

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
end Record1252270103Bootstrap.PR67
