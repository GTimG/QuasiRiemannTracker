/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Reuses the actual weighted finite Hölder kernel in DirectWeightedKernel, with
its inherited OpenAI/Collet/Levy/Gao attribution. -/
import Candidate.C092.transport.DirectWeightedKernel
import Candidate.C092.Intake.QRH.MixedWitness

/-! Same-subclass count selection for Q's finite same-zero bank.  All count
bounds below apply to one fixed physical row set; no independent cardinalities
or source moments are multiplied. The genuine individual inverse/ordinary
counts remain premises, rather than being inferred from scalar prices. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace QRH.Cycle092.ActualMixedPriceCount

def deficit (G₀ G₁ G₂ : ℝ) : ℝ := max G₀ (max G₁ G₂)

/-- Select the strongest genuine bound on the same physical subclass. -/
theorem strongest_three_count {ι : Type*} (s : Finset ι)
    (U R C G₀ G₁ G₂ : ℝ)
    (h₀ : (s.card : ℝ)≤C*U^(R-G₀))
    (h₁ : (s.card : ℝ)≤C*U^(R-G₁))
    (h₂ : (s.card : ℝ)≤C*U^(R-G₂)) :
    (s.card : ℝ)≤C*U^(R-deficit G₀ G₁ G₂) := by
  by_cases h₁₂ : G₁≤G₂
  · by_cases h₀₂ : G₀≤G₂
    · simpa only [deficit,max_eq_right h₁₂,max_eq_right h₀₂] using h₂
    · simpa only [deficit,max_eq_right h₁₂,max_eq_left (le_of_not_ge h₀₂)] using h₀
  · by_cases h₀₁ : G₀≤G₁
    · simpa only [deficit,max_eq_left (le_of_not_ge h₁₂),max_eq_right h₀₁] using h₁
    · simpa only [deficit,max_eq_left (le_of_not_ge h₁₂),max_eq_left (le_of_not_ge h₀₁)] using h₀

/-- Restrict three genuine witness classes to the same physical row subclass
before selecting their strongest cardinality estimate. -/
theorem strongest_three_witness_count {ι : Type*}
    (s t₀ t₁ t₂ : Finset ι) (U R C G₀ G₁ G₂ : ℝ)
    (hs₀ : s⊆t₀) (hs₁ : s⊆t₁) (hs₂ : s⊆t₂)
    (h₀ : (t₀.card : ℝ)≤C*U^(R-G₀))
    (h₁ : (t₁.card : ℝ)≤C*U^(R-G₁))
    (h₂ : (t₂.card : ℝ)≤C*U^(R-G₂)) :
    (s.card : ℝ)≤C*U^(R-deficit G₀ G₁ G₂) := by
  exact strongest_three_count s U R C G₀ G₁ G₂
    ((Nat.cast_le.mpr (Finset.card_le_card hs₀)).trans h₀)
    ((Nat.cast_le.mpr (Finset.card_le_card hs₁)).trans h₁)
    ((Nat.cast_le.mpr (Finset.card_le_card hs₂)).trans h₂)

/-- The displayed max of three actual faces is exactly Q2's penalty. -/
theorem three_faces_eq (kLower kUpper F H M z : ℝ) :
    deficit F
      (QRH.Cycle090.witnessSignedCoefficient kLower kUpper (z-M)*(z-M)+H)
      (QRH.Cycle090.witnessSignedCoefficient kLower kUpper (z-M)*(z-M)+
        2*kLower*max 0 (z-M)) =
      QRH.Cycle090.witnessPenalty kLower kUpper F H M z := by
  unfold deficit QRH.Cycle090.witnessPenalty
  rw [max_add_add_left]

/-- Three same-subclass counts give the literal Q2 maximum, with each face's
sign and the ordinary positive part retained. -/
theorem three_face_count {ι : Type*} (s : Finset ι)
    (U R C kLower kUpper F H M z : ℝ)
    (hF : (s.card : ℝ)≤C*U^(R-F))
    (hH : (s.card : ℝ)≤C*U^(R-
      (QRH.Cycle090.witnessSignedCoefficient kLower kUpper (z-M)*(z-M)+H)))
    (hO : (s.card : ℝ)≤C*U^(R-
      (QRH.Cycle090.witnessSignedCoefficient kLower kUpper (z-M)*(z-M)+
        2*kLower*max 0 (z-M)))) :
    (s.card : ℝ)≤C*U^(R-QRH.Cycle090.witnessPenalty kLower kUpper F H M z) := by
  simpa only [three_faces_eq] using strongest_three_count s U R C F _ _ hF hH hO

/-- The original physical polynomial and selected/full prime factors are kept
inside their own sums. A genuine same-subclass count deficit saves exactly
three quarters of its maximum in the marked-numerator first moment. -/
theorem weighted_three_count_amplitude {ι : Type*} (s : Finset ι) (S Q P : ι→ℂ)
    (U R total selected epsilon Ccount Cmoment G₀ G₁ G₂ : ℝ)
    (hU : 0<U) (hc : 1≤Ccount) (hm : 1≤Cmoment)
    (h₀ : (s.card : ℝ)≤Ccount*U^(R-G₀))
    (h₁ : (s.card : ℝ)≤Ccount*U^(R-G₁))
    (h₂ : (s.card : ℝ)≤Ccount*U^(R-G₂))
    (hselected : ∀ i∈s, U^selected≤‖Q i‖)
    (hfull : ∀ i∈s, ‖P i‖≤U^total)
    (henergy : (∑ i∈s, ‖S i‖^4*‖Q i‖^2)≤Cmoment*U^(1+epsilon)) :
    (∑ i∈s, ‖S i*P i‖) ≤ Ccount*Cmoment*
      U^(total-selected/2+(3*R+1+epsilon)/4-3*deficit G₀ G₁ G₂/4) := by
  have hcard := strongest_three_count s U R Ccount G₀ G₁ G₂ h₀ h₁ h₂
  have h := DirectEnergy.Packet.weighted_amplitude_bin s S Q P U
    (R-deficit G₀ G₁ G₂) total selected epsilon Ccount Cmoment
    hU hc hm hcard hselected hfull henergy
  have he : total-selected/2+(3*(R-deficit G₀ G₁ G₂)+1+epsilon)/4 =
      total-selected/2+(3*R+1+epsilon)/4-3*deficit G₀ G₁ G₂/4 := by ring
  simpa only [he] using h

/-- The large-deficit sector pays the normalized Q1 debit using only the
original marked fourth. No mixed inverse-ordinary energy is introduced. -/
theorem deficit_sector_pays {U R q G C : ℝ} (hU : 1≤U) (hC : 0≤C)
    (hpaid : q≤3*G/4) : C*U^(R+q-3*G/4)≤C*U^R := by
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU (by linarith)) hC

end QRH.Cycle092.ActualMixedPriceCount
#print axioms QRH.Cycle092.ActualMixedPriceCount.three_face_count
#print axioms QRH.Cycle092.ActualMixedPriceCount.weighted_three_count_amplitude
