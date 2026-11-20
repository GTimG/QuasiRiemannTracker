/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Fixed one-sided source energy and its genuine packed twin on native labels.
The keep is the actual inducing classifier, never the regular complement. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerActual
import Candidate.C092.transport.ColoredGaussFrameProviderActual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open CenteredMomentSecondMaskedWindow CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentSecondSectorColumns CenteredMomentRowNorm
open QRH.Cycle092.FixedFourierH15 QRH.Cycle092.SignedCenter
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily CenteredMomentChildRows CenteredMomentFirstPhysicalSource
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentNaturalFixedRaySource
open QRH.SilDensitySplit.CubeFree
open CenteredMomentRestrictedSourceNormalization CenteredExceptionalProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.TwistedRawSource QRH.Cycle092.RegularColoredForward
namespace QRH.Cycle092.FixedPhysicalClassLedger
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

/-- The completion mask in H15 is the source's genuine puncture mask.
Changing to it preserves the original fixed selector on every nonzero row. -/
lemma fixedKeep_native_source_mask (s : Source (Fin θ.N) θ.a θ.b) (ψ : Character)
    (χ : RayFourExpansion.RayCharacter) (Q : Id) (m A : O) (hm : m≠0) (hA : A≠0)
    (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m) :
    fixedKeep ψ χ Q m A=fixedKeep ψ χ Q (QRH.Cycle092.FixedCubeGauss.nativeSourceMask s) A := by
  have hn : QRH.Cycle092.FixedCubeGauss.nativeSourceMask s≠0 :=
    mul_ne_zero fixedBadMask_ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero s.R s.hR)
  have hlmask : ConcretePrimeRowBridge.goodLambda∣QRH.Cycle092.FixedCubeGauss.nativeSourceMask s :=
    (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  have ht : (2:O)∣QRH.Cycle092.FixedCubeGauss.nativeSourceMask s :=
    (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  funext z
  apply propext
  by_cases hz:z=0
  · simp [fixedKeep,hz]
  · exact and_congr Iff.rfl (CenteredMomentSecondReducedPredicate.fixed_mask_change
      (childCharacter ψ χ) Q m _ A z hm hn hA hz hl h2 hlmask ht)

/-- The actual fixed source energy is the literal squared H15 polynomial,
with its true moving frequency, original colored coefficient and ball profile.
No numerical energy hypothesis or artificial coefficient identification occurs. -/
theorem source_energy_eq_native_polynomial (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ ψ τ : Character) (χ : RayFourExpansion.RayCharacter) (Q : Id) (m A : O)
    (hQ : Q≠0) (hm : m≠0) (hA : A≠0)
    (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m)
    (G : Id) (hG : Supported G) (D : Id)
    (hτ : ∀I : Id,Supported I → IsCoprime G I → ∀t,
      heightCoeff τ t I=heightCoeff ψ t I*CanonicalRowCompletion.idealRowHom A I*
        RayFourExpansion.rayCharacter χ (primaryGenerator I)) (v H : ℝ) :
    sourceRestrictedEnergy (fixedKeep ψ χ Q m A) (residualPool G hG.1 (sourceColumns s))
      (fun I=>if IsCoprime G I ∧ D∣I then sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)
      (heightCoeff τ v) ballProfile H =
    ∑'z : O,if hz:fixedKeep ψ χ Q m A z then
      ‖nativeRowPolynomial s ha
        (fixedDatum (childCharacter ψ χ) Q m A z hQ hm hA hz.1 hl h2 hz.2)
        ω₁ ω₂ ψ χ G hG D v‖^2*(ballProfile (‖eisEmbedding z‖^2/H)).re else 0 := by
  rw [←masked_child_energy ψ τ χ A G hG hτ (sourceColumns s)
    (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) D v (fixedKeep ψ χ Q m A) ballProfile H]
  unfold restrictedEnergy
  apply tsum_congr
  intro z
  split_ifs with hz
  · rfl
  · rfl

/-- This is the single packed row injection used by native H17. Class-image
multiplicity is paid separately by frame_mult, without another row count. -/
lemma packed_row_injective (η : Character) (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (hf : Fits η rs x) : Function.Injective (fun z : O=>(rs.V₀*x.twist)*z) :=
  mul_right_injective₀ (mul_ne_zero rs.hV₀ hf.twist_ne)

lemma packed_fixed_row (η : Character) (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (hf : Fits η rs x) (Q : Id) (z : O) (hz : initialFixed (x.char rs) Q z) :
    initialFixed (anchors η (x.anchor rs)) Q ((rs.V₀*x.twist)*z) := by
  refine ⟨mul_ne_zero (mul_ne_zero rs.hV₀ hf.twist_ne) hz.1,?_⟩
  exact (fixedInducingRow_transfer _ _ Q fixedBadMask _ _ z fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _) hf.mask_ne (mul_ne_zero rs.hV₀ hf.twist_ne) hz.1 hf.coef).mp hz.2

#print axioms fixedKeep_native_source_mask
#print axioms source_energy_eq_native_polynomial
#print axioms packed_row_injective
#print axioms packed_fixed_row
end QRH.Cycle092.FixedPhysicalClassLedger
