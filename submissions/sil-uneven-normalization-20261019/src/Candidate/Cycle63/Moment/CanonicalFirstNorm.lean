import Candidate.Cycle63.Moment.CanonicalFirstSigned

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion ActualEisensteinCubic CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentActive
local notation "O" => HeckeFamily.O

theorem powered_numerator_norm {ι : Type*} (S : Finset ι) (p : ι → O) (t : ι → ℕ) :
    (Ideal.span {∏ i ∈ S, p i^(t i)}).absNorm =
      ∏ i ∈ S, (Ideal.span {p i}).absNorm^(t i) := by
  change Ideal.absNorm (principalIdealHom (∏ i ∈ S, p i^(t i))) = _
  rw [map_prod]
  simp only [map_prod, map_pow]
  rfl

theorem powered_numerator_norm_bound {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (k : ℕ)
    (hp : ∀ i ∈ S, Supported (Ideal.span {p i})) (ht : ∀ i ∈ S, t i ≤ k) :
    (Ideal.span {∏ i ∈ S, p i^(t i)}).absNorm ≤
      (∏ i ∈ S, (Ideal.span {p i}).absNorm)^k := by
  rw [powered_numerator_norm, ← Finset.prod_pow]
  apply Finset.prod_le_prod
  intro i hi
  exact pow_le_pow_right'
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i hi).1))
    (ht i hi)

def firstLeftRadical (C D : Ideal O) : Ideal O :=
  ∏ P ∈ Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6), activePrime C D P

def firstRightRadical (C D : Ideal O) : Ideal O :=
  ∏ P ∈ Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6), activePrime C D P

def firstLeftCancelledRadical (C D : Ideal O) : Ideal O :=
  ∏ P ∈ firstLeftCancelled C D, activePrime C D P

def firstRightCancelledRadical (C D : Ideal O) : Ideal O :=
  ∏ P ∈ firstRightCancelled C D, activePrime C D P

theorem actual_first_left_norm (C D : Ideal O) (hC : Supported C) :
    (Ideal.span {firstLeftUncancelled C D}).absNorm ≤ (firstLeftRadical C D).absNorm^5 := by
  have hh := powered_numerator_norm_bound
    (Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6))
    (firstSignedPrime C D) (fun P => 1+activeExponent C D P) 5
    (fun P _ => firstSignedPrime_supported C D hC P) (by
      intro P hP
      have he := (Finset.mem_filter.mp hP).2
      have h6 : activeExponent C D P < 6 := netExponent_lt_six _ _
      omega)
  simpa only [firstLeftUncancelled, firstLeftRadical, map_prod,
    firstSignedPrime_span C D hC] using hh

theorem actual_first_right_norm (C D : Ideal O) (hC : Supported C) :
    (Ideal.span {firstRightUncancelled C D}).absNorm ≤ (firstRightRadical C D).absNorm^5 := by
  have hh := powered_numerator_norm_bound
    (Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6))
    (firstSignedPrime C D) (fun P => 7-activeExponent C D P) 5
    (fun P _ => firstSignedPrime_supported C D hC P) (by
      intro P hP
      have he := (Finset.mem_filter.mp hP).2
      have hp : 0 < activeExponent C D P := Nat.pos_of_ne_zero (netExponent_ne_zero _ _ _ P)
      omega)
  simpa only [firstRightUncancelled, firstRightRadical, map_prod,
    firstSignedPrime_span C D hC] using hh

theorem actual_first_left_radical_split (C D : Ideal O) :
    Ideal.span {activeConductor C D} =
      firstLeftCancelledRadical C D * firstLeftRadical C D := by
  rw [activeConductor, span_finitePrimeModulus]
  exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun P => 1+activeExponent C D P = 6) (activePrime C D)).symm

theorem actual_first_right_radical_split (C D : Ideal O) :
    Ideal.span {activeConductor C D} =
      firstRightCancelledRadical C D * firstRightRadical C D := by
  rw [activeConductor, span_finitePrimeModulus]
  exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun P => 7-activeExponent C D P = 6) (activePrime C D)).symm

theorem firstSubsetNorm_pos (C D : Ideal O) (hC : Supported C)
    (S : Finset (ActiveIndex C D)) :
    0 < (∏ P ∈ S, activePrime C D P).absNorm := by
  rw [map_prod]
  apply Finset.prod_pos
  intro P _
  rw [← firstSignedPrime_span C D hC P]
  exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (firstSignedPrime_supported C D hC P).1)

theorem powered_numerator_norm_pos {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (hp : ∀ i ∈ S, Supported (Ideal.span {p i})) :
    0 < (Ideal.span {∏ i ∈ S, p i^(t i)}).absNorm := by
  rw [powered_numerator_norm]
  apply Finset.prod_pos
  intro i hi
  exact pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i hi).1)) _

theorem norm_log_defect (Z : ℝ) (hZ : 1 < Z) (N F K U : ℕ)
    (hF : 0 < F) (hK : 0 < K) (hU : 0 < U)
    (hN : N = K*U) (hFU : F ≤ U^5) :
    Real.logb Z F ≤ 5*(Real.logb Z N-Real.logb Z K) := by
  have hh := Real.logb_le_logb_of_le hZ (by exact_mod_cast hF)
    (show (F:ℝ) ≤ (U:ℝ)^5 by exact_mod_cast hFU)
  rw [Real.logb_pow] at hh
  have he : Real.logb Z (N:ℝ) = Real.logb Z (K:ℝ)+Real.logb Z (U:ℝ) := by
    rw [hN, Nat.cast_mul, Real.logb_mul (by exact_mod_cast hK.ne')
      (by exact_mod_cast hU.ne')]
  rw [he]
  simpa only [add_sub_cancel_left, Nat.cast_ofNat] using hh

theorem actual_first_left_log_bound (C D : Ideal O) (hC : Supported C)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.span {firstLeftUncancelled C D}).absNorm ≤
      5*(Real.logb Z (Ideal.span {activeConductor C D}).absNorm-
        Real.logb Z (firstLeftCancelledRadical C D).absNorm) := by
  apply norm_log_defect Z hZ
    (Ideal.span {activeConductor C D}).absNorm
    (Ideal.span {firstLeftUncancelled C D}).absNorm
    (firstLeftCancelledRadical C D).absNorm (firstLeftRadical C D).absNorm
  · exact powered_numerator_norm_pos _ _ _ (fun P _ => firstSignedPrime_supported C D hC P)
  · exact firstSubsetNorm_pos C D hC _
  · exact firstSubsetNorm_pos C D hC _
  · rw [actual_first_left_radical_split, map_mul]
  · exact actual_first_left_norm C D hC

theorem actual_first_right_log_bound (C D : Ideal O) (hC : Supported C)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.span {firstRightUncancelled C D}).absNorm ≤
      5*(Real.logb Z (Ideal.span {activeConductor C D}).absNorm-
        Real.logb Z (firstRightCancelledRadical C D).absNorm) := by
  apply norm_log_defect Z hZ
    (Ideal.span {activeConductor C D}).absNorm
    (Ideal.span {firstRightUncancelled C D}).absNorm
    (firstRightCancelledRadical C D).absNorm (firstRightRadical C D).absNorm
  · exact powered_numerator_norm_pos _ _ _ (fun P _ => firstSignedPrime_supported C D hC P)
  · exact firstSubsetNorm_pos C D hC _
  · exact firstSubsetNorm_pos C D hC _
  · rw [actual_first_right_radical_split, map_mul]
  · exact actual_first_right_norm C D hC

#print axioms actual_first_left_norm
#print axioms actual_first_right_norm
#print axioms actual_first_left_radical_split
#print axioms actual_first_right_radical_split
#print axioms actual_first_left_log_bound
#print axioms actual_first_right_log_bound
end
end OAI.SevenEighths.Cycle63Moment
