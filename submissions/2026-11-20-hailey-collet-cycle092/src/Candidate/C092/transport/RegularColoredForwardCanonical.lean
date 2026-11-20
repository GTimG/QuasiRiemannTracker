/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual inherited independently colored canonical source, through literal
profile centralization and the two original signed ordinary rectangles. -/
import Candidate.C092.transport.RegularColoredForwardPuncture
import Candidate.C092.transport.TwistedRawSourceCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentSourceRectangle CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower.KernelAssignmentReindex
open KernelRowExpansion KernelRowProfiles KernelRowPools KernelMarkedRows
open MixedCommonRestriction MixedCommonCoefficient MixedTupleRows MixedCompletedRows
open QRH.Cycle092.TwistedRawSource
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance c092LocalInst_Candidate_C092_transport_RegularColoredForwardCanonical_59bfb4161fcc678b_001 : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def coloredPuncturedRow (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  weightedSum (naturalCoefficients χ S pool β P)
    (fun slot => row χ ω₁ ω₂ (supportedRectangle S b X₁ X₂)
      (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
      W₁ W₂ X₁ X₂)

def coloredCenteredRow (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id) : ℂ :=
  (Real.sqrt (pairNorm d) : ℂ)⁻¹ *
    (coloredPuncturedRow χ ω₁ ω₂ S H pool β P W₁ W₂ b (X₁/d.1.absNorm) (X₂/d.2.absNorm) -
      coloredPuncturedRow χ ω₁ ω₂ S H pool β P W₁ W₂ b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm))

/-- This is precisely the colored native canonical finite source: actual
plainSupportPool unions, original profileCoefficient and full puncture R. -/
abbrev coloredCanonicalSource (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (R : Id) (pool : ι → Finset Id) (ν : ι → Id → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id) : ℂ :=
  TwistedRawSource.canonicalSource ω₁ ω₂ χ S H R pool ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ d

/-- Explicit finite column binding to the original colored aggregate. -/
theorem coloredCanonicalSource_eq_columns (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (R : Id) (pool : ι → Finset Id) (ν : ι → Id → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id) :
    let V := Fintype.piFinset (pools pool
      (plainSupportPool b (X₁/d.1.absNorm) (Y₁/d.1.absNorm))
      (plainSupportPool b (X₂/d.2.absNorm) (Y₂/d.2.absNorm)))
    coloredCanonicalSource χ ω₁ ω₂ S H R pool ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ d =
      ∑ I ∈ finiteColumns V, coloredColumn V (punctureProduct S H) ω₁ ω₂
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1) I * idealCoeff χ I := by
  dsimp only [coloredCanonicalSource,TwistedRawSource.canonicalSource]
  exact colored_root_eq_columns _ _ _ _ _ _

/-- The actual signed full rectangle is completed on exactly the original
support unions, with no coefficientwise comparison of cancelling sums. -/
theorem colored_centered_tuple_complete (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (A B : Finset Id)
    (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b) (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (hDX : rectangle b (X₁/d.1.absNorm) (X₂/d.2.absNorm) ⊆ A ×ˢ B)
    (hDY : rectangle b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) ⊆ A ×ˢ B)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (hS : ∀ I, Supported I →
      (((I.absNorm : ℝ) ≤ b*(X₁/d.1.absNorm) ∨ (I.absNorm : ℝ) ≤ b*(X₂/d.2.absNorm)) ∨
       ((I.absNorm : ℝ) ≤ b*(Y₁/d.1.absNorm) ∨ (I.absNorm : ℝ) ≤ b*(Y₂/d.2.absNorm))) →
      primeSupport I ⊆ primeValues S) :
    (∑ v ∈ Fintype.piFinset (pools (fun _ : ι => primeValues S) A B),
      coloredTuple (punctureProduct S H) ω₁ ω₂
        (centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d) v * idealCoeff χ (finiteTupleProduct v)) =
      coloredCenteredRow χ ω₁ ω₂ S H pool β P W₁ W₂ b X₁ X₂ Y₁ Y₂ d := by
  rw [centered_colored_tuple_sum χ ω₁ ω₂ S H pool A B β P W₁ W₂ X₁ X₂ Y₁ Y₂ d
    (mul_pos hX₁ hX₂) hXY hd]
  unfold coloredCenteredRow coloredPuncturedRow
  apply congrArg (fun z : ℂ => (Real.sqrt (pairNorm d) : ℂ)⁻¹*z)
  apply congrArg₂ (fun x y : ℂ => x-y)
  · apply congrArg (weightedSum (naturalCoefficients χ S pool β P))
    funext slot
    exact colored_row_complete χ ω₁ ω₂ S (A ×ˢ B) _ W₁ W₂ b _ _
      (shortened_positive_le hX₁ hd.1).1 (shortened_positive_le hX₂ hd.2).1 hs₁ hs₂ hDX hoff
      (fun I hI hh => hS I hI (Or.inl hh))
  · apply congrArg (weightedSum (naturalCoefficients χ S pool β P))
    funext slot
    exact colored_row_complete χ ω₁ ω₂ S (A ×ˢ B) _ W₁ W₂ b _ _
      (shortened_positive_le hY₁ hd.1).1 (shortened_positive_le hY₂ hd.2).1 hs₁ hs₂ hDY hoff
      (fun I hI hh => hS I hI (Or.inr hh))

/-- Original inherited profile to exact colored centered source. The actual
full R puncture, mark profiles, independent colors and artificial prefixes d
are all retained. Only original support/enclosure geometry is required. -/
theorem colored_source_centered (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (R : Id) (hR : R ≠ 0)
    (pool : ι → Finset Id) (hp : ∀ i, pool i ⊆ primeValues S)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b) (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (hS : ∀ I, Supported I →
      (((I.absNorm : ℝ) ≤ b*(X₁/d.1.absNorm) ∨ (I.absNorm : ℝ) ≤ b*(X₂/d.2.absNorm)) ∨
       ((I.absNorm : ℝ) ≤ b*(Y₁/d.1.absNorm) ∨ (I.absNorm : ℝ) ≤ b*(Y₂/d.2.absNorm))) →
      primeSupport I ⊆ primeValues S) :
    MixedLiveNormalization.normalization (X₁*X₂) P *
      coloredCanonicalSource χ ω₁ ω₂ S H R pool ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ d =
      coloredCenteredRow (χ.excludePrimes (primeSupport R) (fun _ h => IdealMobiusDivisorSum.support_prime h))
        ω₁ ω₂ S H pool (fun i I => ν i I * Wslot i (I.absNorm/P i)) P W₁ W₂ b X₁ X₂ Y₁ Y₂ d := by
  change MixedLiveNormalization.normalization (X₁*X₂) P *
    (∑ v ∈ Fintype.piFinset (pools pool
      (plainSupportPool b (X₁/d.1.absNorm) (Y₁/d.1.absNorm))
      (plainSupportPool b (X₂/d.2.absNorm) (Y₂/d.2.absNorm))),
      coloredTuple (punctureProduct S H) ω₁ ω₂
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1) v *
        idealCoeff χ (finiteTupleProduct v)) = _
  rw [colored_punctured_pool_profile χ ω₁ ω₂ S H R hR pool hp _ _ ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d]
  have hc := source_pool_rectangles d hd b X₁ X₂ Y₁ Y₂
  dsimp only at hc
  rw [residual_plain_pool,residual_plain_pool] at hc
  apply colored_centered_tuple_complete _ ω₁ ω₂ S H _ _ _ _ _ W₁ W₂ b X₁ X₂ Y₁ Y₂ d
    hX₁ hX₂ hY₁ hY₂ hXY hd hs₁ hs₂ hc.1 hc.2 _ hS
  exact NativePuncturedInjective.deleted_off_supported χ hoff _ _

/-- Literal rowwise comparison summand used by the regular source reduction.
Both original arms are inserted before the signed difference is bounded;
the exact full paired divisor saving is 1/pairNorm d. -/
theorem colored_centered_row_sq_le (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    ‖coloredCenteredRow χ ω₁ ω₂ S H pool β P W₁ W₂ b X₁ X₂ Y₁ Y₂ d‖^2 ≤
      2 / pairNorm d *
        (‖coloredPuncturedRow χ ω₁ ω₂ S H pool β P W₁ W₂ b (X₁/d.1.absNorm) (X₂/d.2.absNorm)‖^2 +
         ‖coloredPuncturedRow χ ω₁ ω₂ S H pool β P W₁ W₂ b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm)‖^2) := by
  let f := coloredPuncturedRow χ ω₁ ω₂ S H pool β P W₁ W₂ b (X₁/d.1.absNorm) (X₂/d.2.absNorm)
  let g := coloredPuncturedRow χ ω₁ ω₂ S H pool β P W₁ W₂ b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm)
  have hn : ‖f-g‖^2 ≤ 2*(‖f‖^2+‖g‖^2) := by
    nlinarith [norm_sub_le f g,norm_nonneg (f-g),sq_nonneg (‖f‖-‖g‖)]
  unfold coloredCenteredRow
  rw [norm_mul,mul_pow,central_scalar_sq d hd]
  exact (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (pairNorm_pos hd.1 hd.2).le)).trans_eq (by ring)

#print axioms coloredCanonicalSource_eq_columns
#print axioms colored_centered_tuple_complete
#print axioms colored_source_centered
#print axioms colored_centered_row_sq_le
end
end QRH.Cycle092.RegularColoredForward
