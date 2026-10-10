import WeightedQRH.NumeratorErrorPacket
import WeightedQRH.NumeratorDeficit

/-! Two-line absolute coefficient masses and actual conductor absorption. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators NNReal Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

theorem coefficient_left_weight (A : ℂ) (N L rho : ℝ) (hN : 0 < N) (hL : 0 ≤ L) :
    ‖A‖ * N ^ (-(1 / 2 : ℝ)) * (L * N)^rho =
      L^rho * (‖A‖ * N^(-(1 / 2 - rho))) := by
  rw [Real.mul_rpow hL hN.le]
  calc
    _ = L^rho * ‖A‖ * (N^(-(1 / 2 : ℝ)) * N^rho) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN]
      rw [show -(1 / 2 : ℝ) + rho = -(1 / 2 - rho) by ring]
      ring

theorem coefficient_max_weight_bound (A : ℂ) (N L rho : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hrho : 0 ≤ rho) :
    ‖A‖ * N^(-(1 / 2 : ℝ)) * max 1 (L * N)^rho ≤
      ‖A‖ * N^(-(1 / 2 : ℝ)) + L^rho * (‖A‖ * N^(-(1 / 2 - rho))) := by
  rw [Real.rpow_max zero_le_one (mul_nonneg hL hN.le) hrho,Real.one_rpow]
  have ht : 0 ≤ (L * N)^rho := Real.rpow_nonneg (mul_nonneg hL hN.le) rho
  calc
    _ ≤ ‖A‖ * N^(-(1 / 2 : ℝ)) * (1 + (L * N)^rho) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact max_le (by linarith) (by linarith)
    _ = _ := by rw [mul_add,mul_one,coefficient_left_weight A N L rho hN hL]

theorem mass_deficit_absorption (M B D L rho : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (hrho : 0 ≤ rho) (hmass : M ≤ B * D^rho) (hcap : L * D ≤ 1) :
    L^rho * M ≤ B := by
  calc
    _ ≤ L^rho * (B * D^rho) :=
      mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hL rho)
    _ = B * (L * D)^rho := by rw [Real.mul_rpow hL hD]; ring
    _ ≤ B * 1^rho := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hL hD) hcap hrho) hB
    _ = B := by rw [Real.one_rpow,mul_one]

theorem two_line_coefficient_mass {ι : Type*} (A : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i, 0 < N i) (L rho B : ℝ) (hL : 0 ≤ L) (hrho : 0 ≤ rho)
    (hc : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ))))
    (hl : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 - rho))))
    (hcm : (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ))) ≤ B)
    (hlm : L^rho * (∑' i, ‖A i‖ * (N i)^(-(1 / 2 - rho))) ≤ B) :
    Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ∧
    (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ≤ 2 * B := by
  have hmajor := hc.add (hl.mul_left (L^rho))
  have hbound (i : ι) := coefficient_max_weight_bound (A i) (N i) L rho (hN i) hL hrho
  have hs : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) :=
    hmajor.of_nonneg_of_le (fun i => by have := hN i; positivity) hbound
  refine ⟨hs, ?_⟩
  have hm := hs.tsum_le_tsum hbound hmajor
  rw [hc.tsum_add (hl.mul_left _),tsum_mul_left] at hm
  linarith

theorem error_packet_damped_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho L : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho)
    (hleft : -(1 / 100 : ℝ) ≤ 1 / 2 - rho)
    (hmargin : 1 + firsteps ≤ x.re + (1 / 2 - rho))
    (hL : 0 ≤ L) (hcap : L * errorProductDeficit u T ≤ 1) :
    Summable (fun e : ErrorPacketIndex S u T => ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) *
      max 1 (L * (errorPacketScale S u T e : ℝ))^rho) ∧
    (∑' e : ErrorPacketIndex S u T, ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) *
      max 1 (L * (errorPacketScale S u T e : ℝ))^rho) ≤
      2 * (579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) *
        errorProductSize u T) := by
  obtain ⟨hl,hlm⟩ := error_packet_coefficient_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps rho hQ halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
  obtain ⟨hc,hcm⟩ := error_packet_coefficient_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps 0 hQ halpha halpha1 heps heps1 hx hz (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by linarith)
  simp only [sub_zero,Real.rpow_zero,mul_one] at hc hcm
  have hB : 0 ≤ 579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) *
      errorProductSize u T := mul_nonneg (by positivity) (errorProductSize_nonneg u T)
  apply two_line_coefficient_mass _ _
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e))
    L rho _ hL hrho hc hl hcm
  exact mass_deficit_absorption _ _ _ _ _ hB
    (le_trans zero_le_one (errorProductDeficit_one_le u T)) hL hrho hlm hcap

theorem actual_conductor_packet_cap (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (C Cu : ℝ) (hC : 0 < C)
    (hCu : Cu ≤ C * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ)) :
    (Cu / (C * (Ideal.span {u.val} : Ideal O).absNorm)) * errorProductDeficit u T ≤ 1 := by
  have hN : (0 : ℝ) < (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hh := conductor_repeated_deficit u T hT C Cu hC.le hCu
  rw [div_mul_eq_mul_div]
  exact (div_le_one (mul_pos hC hN)).mpr hh

/-- The coefficient-series prefactor costs arbitrarily little row norm,
uniformly in the finite exclusions and selected labels. -/
theorem coefficient_prefactor_subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (u : FreeRow),
      2 * (579 ^ (ramifiedPrimes S u).card * Real.exp (1 / 2)) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound
    579 epsilon (by norm_num) hepsilon
  refine ⟨2 * C * Real.exp (1 / 2),by positivity,?_⟩
  intro S u
  have hc : (579 : ℝ)^(ramifiedPrimes S u).card ≤
      C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon := by
    apply le_trans _ (hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
    apply pow_le_pow_right₀ (by norm_num)
    rw [←HeckeDeletionBounds.primeSet_card]
    exact Finset.card_filter_le _ _
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hc (Real.exp_pos (1 / 2)).le) (by norm_num : (0 : ℝ) ≤ 2)
  exact hh.trans_eq (by ring)

end WeightedQRH.Numerator
