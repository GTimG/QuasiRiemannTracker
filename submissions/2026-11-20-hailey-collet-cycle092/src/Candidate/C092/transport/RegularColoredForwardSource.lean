/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Direct binding of the actual TwistedRawSource sourceColumn to the original
punctured centered forward source, including its inherited normPowerProfiles. -/
import Candidate.C092.transport.RegularColoredForwardCanonical
import Candidate.C092.transport.TwistedRawSourceColumns

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentSourceRectangle CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentLattice
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedCommonRestriction MixedCommonCoefficient MixedTupleRows MixedCompletedRows
open QRH.Cycle092.TwistedRawSource
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_RegularColoredForwardSource_682714a152df013f_001 : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- The seed-completed original coefficient is exactly the independently
colored canonical source, with no change of profile, puncture or prefix. -/
theorem sourceColumn_eq_canonical (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ) :
    (∑ I ∈ MixedPrincipalWindow.sourceColumns s, sourceColumn s ha ω₁ ω₂ 1 I * idealCoeff χ I) =
      coloredCanonicalSource χ ω₁ ω₂ s.S s.H s.R s.pool s.ν s.Wslot s.P
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
        b s.X₁ s.X₂ s.Y₁ s.Y₂ s.d := by
  rw [←source_root_eq_columns s ha ω₁ ω₂ 1 (idealCoeff χ)]
  unfold coloredCanonicalSource TwistedRawSource.canonicalSource
  have hpool : MixedPrincipalAllocations.tuplePools s =
      pools s.pool (plainSupportPool b (s.X₁/s.d.1.absNorm) (s.Y₁/s.d.1.absNorm))
        (plainSupportPool b (s.X₂/s.d.2.absNorm) (s.Y₂/s.d.2.absNorm)) := by
    unfold MixedPrincipalAllocations.tuplePools MixedLiteralAllocation.sourcePools
    rw [residual_plain_pool,residual_plain_pool]
  rw [hpool]
  apply Finset.sum_congr rfl
  intro v hv
  unfold MixedOriginalSecondZero.originalTuple
  ring

/-- Centralization of the actual Poisson sourceColumn, with every original
mark, the two independent heights and the complete original source masks.
The only extra premise is the native geometric OriginalEnclosure. -/
theorem sourceColumn_centered (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : MixedPrincipalAllocations.OriginalEnclosure s)
    (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0) :
    MixedLiveNormalization.normalization (s.X₁*s.X₂) s.P *
      (∑ I ∈ MixedPrincipalWindow.sourceColumns s, sourceColumn s ha ω₁ ω₂ 1 I * idealCoeff χ I) =
      coloredCenteredRow
        (χ.excludePrimes (primeSupport s.R) (fun _ h => IdealMobiusDivisorSum.support_prime h))
        ω₁ ω₂ s.S s.H s.pool (fun i I => s.ν i I * s.Wslot i (I.absNorm/s.P i)) s.P
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
        b s.X₁ s.X₂ s.Y₁ s.Y₂ s.d := by
  rw [sourceColumn_eq_canonical]
  apply colored_source_centered χ ω₁ ω₂ s.S s.H s.R s.hR s.pool s.hpool
    s.ν s.Wslot s.P _ _ b s.X₁ s.X₂ s.Y₁ s.Y₂ s.d
    (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂) (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂)
    (s.hpX.trans s.hpY.symm) s.hd
    ((CenteredMomentTwist.normPowerProfile_support _ _ _ _ _ _ _).trans (fun _ h => (s.hs₁ h).2))
    ((CenteredMomentTwist.normPowerProfile_support _ _ _ _ _ _ _).trans (fun _ h => (s.hs₂ h).2)) hoff
  intro I hI hlen
  apply cover I hI
  rcases hlen with (h|h)|(h|h)
  · exact Or.inl (h.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right s.hXU₁ (Nat.cast_nonneg _)) hb))
  · exact Or.inr (h.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right s.hXU₂ (Nat.cast_nonneg _)) hb))
  · exact Or.inl (h.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right s.hYU₁ (Nat.cast_nonneg _)) hb))
  · exact Or.inr (h.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right s.hYU₂ (Nat.cast_nonneg _)) hb))

/-- The actual source's rowwise comparison summand. Both original scale
arms retain the same complete mark product and full source punctures, with
the exact 1/(Nd₁ Nd₂) factor. This is an upper bound on sourceColumn itself. -/
theorem sourceColumn_row_sq_le (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : MixedPrincipalAllocations.OriginalEnclosure s)
    (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0) :
    let χR := χ.excludePrimes (primeSupport s.R) (fun _ h => IdealMobiusDivisorSum.support_prime h)
    let β := fun i I => s.ν i I * s.Wslot i (I.absNorm/s.P i)
    let V₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
    let V₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
    ‖MixedLiveNormalization.normalization (s.X₁*s.X₂) s.P *
      (∑ I ∈ MixedPrincipalWindow.sourceColumns s, sourceColumn s ha ω₁ ω₂ 1 I * idealCoeff χ I)‖^2 ≤
      2 / pairNorm s.d *
        (‖coloredPuncturedRow χR ω₁ ω₂ s.S s.H s.pool β s.P V₁ V₂ b
            (s.X₁/s.d.1.absNorm) (s.X₂/s.d.2.absNorm)‖^2 +
         ‖coloredPuncturedRow χR ω₁ ω₂ s.S s.H s.pool β s.P V₁ V₂ b
            (s.Y₁/s.d.1.absNorm) (s.Y₂/s.d.2.absNorm)‖^2) := by
  dsimp only
  rw [sourceColumn_centered s ha hb cover χ ω₁ ω₂ hoff]
  exact colored_centered_row_sq_le _ ω₁ ω₂ s.S s.H s.pool _ s.P _ _ b
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d s.hd

#print axioms sourceColumn_eq_canonical
#print axioms sourceColumn_centered
#print axioms sourceColumn_row_sq_le
end
end QRH.Cycle092.RegularColoredForward
