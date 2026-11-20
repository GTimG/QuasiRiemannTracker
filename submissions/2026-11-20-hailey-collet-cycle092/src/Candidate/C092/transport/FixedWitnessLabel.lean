/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Every possible ordinary witness in the regular-core detector dictionary
is a fixed character times the original moving sextic feature. -/
import Candidate.C092.transport.MediumReplaceSourceRadius

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckePrimeRay HeckeRowClosure
open HeckeDyadic HeckeDetectorSupportedWitness HeckeInverseAmplification
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary CanonicalRowCompletion
namespace QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_FixedWitnessLabel_5c20a2c77daf07d2_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The ordinary base depends on its label and the fixed input characters
alone, so it can be selected before row norms, zeros and heights. -/
def witnessBase (η η₀ : Character) :
    Option (RayQuotient.Characters M H × RayQuotient.Characters M H) → Character
  | none => η
  | some pair => (η.product (relativeCharacter M H hH η₀ pair.1).inverse.inverse).product
      (HeckeRayQuotient.character M H hH pair.2)

theorem witness_row {Z K bΦ : ℝ} (s : NaturalState Z K bΦ) (η₀ : Character)
    {z : O} (F : NaturalRow s.character z) (j) :
    ∀ n, elementCoeff (family M H hH s η₀ F j) n =
      rowTwist (elementHom (witnessBase M H hH s.character η₀ j)) s.mask 1 (1*z) n := by
  have h : ∀ n, elementCoeff (excluded F.character s.puncture) n =
      rowTwist (elementHom s.character) s.mask 1 (1*z) n := by
    simpa only [one_mul,NaturalState.mask] using F.masked_element s.puncture s.puncture_ne_zero
  cases j with
  | none => exact h
  | some pair =>
    let ψ := (relativeCharacter M H hH η₀ pair.1).inverse.inverse
    exact product_row_presentation (s.character.product ψ) ((excluded F.character s.puncture).product ψ)
      (HeckeRayQuotient.character M H hH pair.2) s.mask 1 z
      (product_row_presentation s.character _ ψ s.mask 1 z h)

theorem actual_witness_original {Z K bΦ : ℝ} (s : NaturalState Z K bΦ) (η₀ : Character)
    {z : O} (F : NaturalRow s.character z) {d a ε cutoff T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness (family M H hH s η₀ F) (Z^d) a ε cutoff T allowance i) (hZ : 0 < Z) :
    QRH.Cycle092.SignedEnergy.actualPlain w =
      QRH.Cycle092.OrdinaryColumn.original (witnessBase M H hH s.character η₀ w.label) s.mask 1 z
        (twistProfile HeckeDetectorDyadicProfiles.positiveAnnular w.zero.re (2*Real.pi*w.nu-w.zero.im))
        0 ((Z^d)^w.m) :=
  plain_polynomial_eq_row _ _ _ _ _ (witness_row M H hH s η₀ F w.label)
    _ _ _ _ (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZ _) _)

#print axioms actual_witness_original
end QRH.Cycle092.MediumReplace.Source
