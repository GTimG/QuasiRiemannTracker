/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The true PairAt common-mark norm presentations supply the native spike on
the original arbitrary long base and initial keep. -/
import Candidate.C092.transport.SourceInverseP6CloseNormTransport

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6GeneralPairNorm_df10b2cbf32187e6_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

/-- This is exactly the pair of norm presentations already required by
PairAt, specialized to its surviving finite slot subtype. -/
theorem pair_at_native_presentation (rows : Finset FreeRow) (η η₀ ηLong baseLong : Character)
    (W : ℝ→ℂ) (Z : ℝ) (θ θLong : Slot→RayQuotient.Characters M H)
    (w σ σLong v vLong : Slot→ℝ) (tShort tLong : ℝ) (mark : Slot→FreeRow→ℂ)
    (hσ : ∀ j,σ j=33/50) (hσLong : ∀ j,σLong j=33/50)
    (hShort : ∀ u∈rows,∀ j,‖mark j u‖=‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val
      (originalPools M H 2 Z w j) (originalCoefficients M H hH η₀ θ W Z w σ v j) tShort (Z^(w j))‖)
    (hLong : ∀ u∈rows,∀ j,‖mark j u‖=‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val
      (originalPools M H 2 Z w j) (originalCoefficients M H hH baseLong θLong W Z w σLong vLong j) tLong (Z^(w j))‖) :
    ∀ u∈rows,∀ j,‖descriptor M H hH η η₀ W Z θ w v tShort u j‖=
      ‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M H 2 (Z^(w j)))
        (fun I=>idealCoeff (relativeCharacter M H hH baseLong (θLong j)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖ := by
  intro u hu j
  rw [descriptor_short_anchor M H hH η η₀ W Z θ w σ v tShort u j (hσ j),←hShort u hu j,hLong u hu j]
  unfold originalPools originalCoefficients
  rw [hσLong j]

/-- A lower measured endpoint gives a native spike through the actual
PairAt presentation. No anchored-base substitution or keep transport occurs. -/
theorem pair_native_spike (rows : Finset FreeRow) (η η₀ ηLong baseLong : Character)
    (W : ℝ→ℂ) {Z pay b el : ℝ} (hZ : 1 < Z) (hpay : 1 ≤ pay)
    (θ θLong : Slot→RayQuotient.Characters M H) (w v vLong : Slot→ℝ)
    (tShort tLong : ℝ) (jd : Slot) (hw : 0 ≤ w jd)
    (hNorm : ∀ u∈rows,∀ j,‖descriptor M H hH η η₀ W Z θ w v tShort u j‖=
      ‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M H 2 (Z^(w j)))
        (fun I=>idealCoeff (relativeCharacter M H hH baseLong (θLong j)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖)
    (hel : ∀ u∈descriptorRows M H hH rows η η₀ W Z pay b θ w v tShort jd,
      el ≤ measured M H hH η η₀ W Z pay θ w v tShort u) :
    ∀ u∈descriptorRows M H hH rows η η₀ W Z pay b θ w v tShort jd,
      Z^(el*w jd) ≤ ‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val
        (primePool M H 2 (Z^(w jd)))
        (fun I=>idealCoeff (relativeCharacter M H hH baseLong (θLong jd)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w jd)) (33/50) (vLong jd) I) tLong (Z^(w jd))‖^2 := by
  intro u hu
  rw [←hNorm u (Finset.mem_filter.mp hu).1 jd,(Finset.mem_filter.mp hu).2.2]
  exact (Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right (hel u hu) hw)).trans
    (le_mul_of_one_le_left (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hpay)

#print axioms pair_at_native_presentation
#print axioms pair_native_spike
end
end QRH.Cycle092.SourceInverseP6
