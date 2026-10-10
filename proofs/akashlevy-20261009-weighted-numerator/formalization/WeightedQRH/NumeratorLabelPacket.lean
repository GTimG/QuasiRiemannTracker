import WeightedQRH.NumeratorErrorLabels
import WeightedQRH.NumeratorPacketMellin

/-! The complete coefficient packet after summing all physical error-prime labels. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators NNReal Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def labelPrimes (T : ι → Finset ProbePhysical.PrimeIdeal) (P : ∀ i, T i) :
    Finset ProbePhysical.PrimeIdeal := Finset.univ.image (fun i => (P i).val)

theorem labelSupported (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
    (P : ∀ i, T i) : ∀ Q ∈ labelPrimes T P, Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad _ (hT i _ (P i).property)

def LabelPacketIndex (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) := Σ P : ∀ i, T i, ErrorPacketIndex S u (labelPrimes T P)

def errorPacketBase (S : Finset (Ideal O)) (u : FreeRow)
    (T : Finset ProbePhysical.PrimeIdeal) : ErrorPacketIndex S u T :=
  ⟨(fun _ => 0), (fun _ => 0), ⟨∅, fun _ => 0⟩⟩

def labelPacketBase (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (P : ∀ i, T i) : LabelPacketIndex S u T :=
  ⟨P,errorPacketBase S u (labelPrimes T P)⟩

instance labelPacketIndex_countable (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) : Countable (LabelPacketIndex S u T) := by
  unfold LabelPacketIndex
  infer_instance

def labelPacketCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ i P, P ∈ T i → P.val ∉ S) (weight : ∀ i, T i → ℂ) (x z : ℂ)
    (e : LabelPacketIndex S u T) : ℂ :=
  (∏ i, weight i (e.1 i)) *
    errorPacketCoefficient S hS η u (labelPrimes T e.1) (labelSupported S hS T hT e.1) x z e.2

def labelPacketScale (S : Finset (Ideal O)) (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (e : LabelPacketIndex S u T) : ℝ≥0 := errorPacketScale S u (labelPrimes T e.1) e.2

theorem labelPacketScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (e : LabelPacketIndex S u T) :
    1 ≤ labelPacketScale S u T e := errorPacketScale_one_le S u (labelPrimes T e.1) e.2

/-- Uniform in every error-label tuple, row, finite exclusion set and height. -/
theorem actual_label_packet_mass (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (weight : ∀ i, T i → ℂ) (x z : ℂ) (alpha eps rho Ccond Cu : ℝ),
      (51 / 100 : ℝ) ≤ alpha → alpha ≤ 1 → 0 < eps → eps ≤ 1 / 1000 →
      x.re = alpha + 16 * eps → z.re = 17 / 50 → 0 ≤ rho → rho ≤ 1 →
      1 - alpha - 6 * eps ≤ 1 / 2 - rho → -(1 / 100 : ℝ) ≤ 1 / 2 - rho →
      1 + firsteps ≤ x.re + (1 / 2 - rho) →
      0 < Ccond → 0 ≤ Cu → Cu ≤ Ccond * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) →
      let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
      Summable (fun e : LabelPacketIndex S u T => ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ∧
      (∑' e : LabelPacketIndex S u T, ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ≤
        (C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon) *
          ∏ i, ∑ P : T i, 2880 * ‖weight i P‖ * errorSize u P.val := by
  obtain ⟨C,hC,hpref⟩ := coefficient_prefactor_subpower epsilon hepsilon
  refine ⟨C,hC,?_⟩
  intro S hS firsteps hfirst η u T hT hdis hη weight x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
  have hL : 0 ≤ L := div_nonneg hCu0 (mul_nonneg hCcond.le (by positivity))
  let M := C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon
  have hpacket (P : ∀ i, T i) :
      Summable (fun e : ErrorPacketIndex S u (labelPrimes T P) =>
        ‖errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z e‖ *
        (errorPacketScale S u (labelPrimes T P) e : ℝ)^(-(1 / 2 : ℝ)) *
        max 1 (L * (errorPacketScale S u (labelPrimes T P) e : ℝ))^rho) ∧
      (∑' e : ErrorPacketIndex S u (labelPrimes T P),
        ‖errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z e‖ *
        (errorPacketScale S u (labelPrimes T P) e : ℝ)^(-(1 / 2 : ℝ)) *
        max 1 (L * (errorPacketScale S u (labelPrimes T P) e : ℝ))^rho) ≤
        M * errorProductSize u (labelPrimes T P) := by
    have hηP : ∀ Q ∈ labelPrimes T P, IsCoprime Q.val η.modulus := by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hη i _ (P i).property
    have hQP : ∀ Q ∈ labelPrimes T P, (4 : ℝ) ≤ Q.val.absNorm := by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact_mod_cast hS.tail.norm_four _ (hT i _ (P i).property)
    have hc := actual_conductor_packet_cap u (labelPrimes T P) (labelSupported S hS T hT P)
      Ccond Cu hCcond hCu
    obtain ⟨hs,hm⟩ := error_packet_damped_mass S hS firsteps hfirst η u (labelPrimes T P)
      (labelSupported S hS T hT P) hηP x z alpha eps rho L hQP halpha halpha1 heps heps1 hx hz
      hrho hrho1 hline hleft hmargin hL hc
    refine ⟨hs,hm.trans ?_⟩
    have hp := mul_le_mul_of_nonneg_right (hpref (markExclusions S (labelPrimes T P)) u)
      (errorProductSize_nonneg u (labelPrimes T P))
    simpa only [mul_assoc,M] using hp
  have hh := finite_label_damped_mass
    (fun P => errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z)
    (fun P e => (errorPacketScale S u (labelPrimes T P) e : ℝ))
    (fun P e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u (labelPrimes T P) e))
    (fun P => ∏ i, weight i (P i)) (fun P => errorProductSize u (labelPrimes T P)) L rho M
    (fun P => (hpacket P).1) (fun P => (hpacket P).2)
  refine ⟨hh.1,?_⟩
  change _ ≤ M * _
  exact hh.2.trans_eq (congrArg (fun t : ℝ => M*t) (error_label_mass_factor u T hdis weight))

end WeightedQRH.Numerator
