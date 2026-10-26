import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeSourceGeometry
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeRawTransport

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109GainWholeGeometry
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentDetectorEnergyInitialState Cycle61Moment Record12518109Natural
open Record12518109GainWholeZeros Record12518109GainActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def wholeRegularBad (η η₀ : Character) (j : WholeSourceIndex M H) : Ideal O :=
  (M⊓Ideal.span {(72:O)})⊓(cleanWholeBase M H hH η η₀ j).modulus

theorem wholeRegularBad_nonzero (η η₀ : Character) (j : WholeSourceIndex M H) :
    wholeRegularBad M H hH η η₀ j≠0 := by
  exact Ideal.inf_ne_bot_of_ne_bot
    (Ideal.inf_ne_bot_of_ne_bot (NeZero.ne M)
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
    (cleanWholeBase M H hH η η₀ j).modulus_ne_bot

theorem wholeRegularBad_proper (η η₀ : Character) (j : WholeSourceIndex M H) :
    wholeRegularBad M H hH η η₀ j≠⊤ := by
  intro ht
  have h72 : (Ideal.span {(72:O)} : Ideal O)≤Ideal.span {(2:O)} :=
    Ideal.span_singleton_le_span_singleton.mpr ⟨36,by norm_num⟩
  exact CanonicalQuadraticSieve.twoIdeal_maximal.isPrime.ne_top
    (top_le_iff.mp (ht ▸ (inf_le_left.trans (inf_le_right.trans h72))))

def wholeRegularDictionary (η η₀ : Character) : FixedUnmarkedDictionary (WholeSourceIndex M H) where
  base:=cleanWholeBase M H hH η η₀
  fixedIdeal:=fun j=>internalQ (wholeRegularBad M H hH η η₀ j) (wholeSourceAnchor M H hH η₀ j)
  nonzero:=fun j=>internalQ_ne_zero _ (wholeRegularBad_nonzero M H hH η η₀ j) _
  proper:=fun j=>internalQ_ne_top _ (wholeRegularBad_proper M H hH η η₀ j) _
  divides72:=fun _=>inf_le_left.trans (inf_le_left.trans inf_le_right)
  dividesBase:=fun _=>inf_le_left.trans inf_le_right

theorem whole_regular_retained (η η₀ : Character) (rows : Finset FreeRow) :
    ∀u∈rows.filter (fun u=>¬(wholeRegularDictionary M H hH η η₀).exceptionalCore u),∀j,
      initialKeep (cleanWholeBase M H hH η η₀ j)
        (internalQ (wholeRegularBad M H hH η η₀ j) (wholeSourceAnchor M H hH η₀ j)) u.val := by
  intro u hu j
  by_contra hn
  exact (Finset.mem_filter.mp hu).2 ⟨j,hn⟩

/-- The literal source's positive nonpole zero is preserved through its
moving Euler holes and the fixed common conductor mask, with the same
whole-family label and height. -/
theorem source_zero_to_clean_dictionary (η η₀ χ : Character) (w : NonzeroFrequency)
    (R : Ideal O) (hR : R≠0)
    (hc : ∀I,idealCoeff χ I=idealCoeff (excluded (naturalRow η w.val w.property).character R) I)
    (j : WholeSourceIndex M H) (s : ℂ) (ha : 0<s.re)
    (hz : LFunction (wholeSourceFamily M H hH η₀ χ j) s=0)
    (hpole : s≠1 ∨ (wholeSourceFamily M H hH η₀ χ j).residue≠1) :
    LFunction ((momentData (cleanWholeBase M H hH η η₀ j)).character w) s=0 ∧
      (s≠1 ∨ ((momentData (cleanWholeBase M H hH η η₀ j)).character w).residue≠1) := by
  have hwhole := whole_source_family_mask M H hH η₀ η χ w.val w.property
    (naturalRow η w.val w.property) R hR hc
    (fun k=>naturalRow (wholeSourceBase M H hH η₀ η k) w.val w.property) j
  have h₁ := positive_zeros_eq_of_coefficients _ _ hwhole ha hpole
  have hmask : ∀I,idealCoeff
      (excluded (naturalRow (wholeSourceBase M H hH η₀ η j) w.val w.property).character R) I=
      if IsCoprime I (excluded (naturalRow (wholeSourceBase M H hH η₀ η j) w.val w.property).character R).modulus
      then idealCoeff (naturalRow (wholeSourceBase M H hH η₀ η j) w.val w.property).character I else 0 :=
    fun I=>excludePrimes_mask _ _ (support_prime R) I
  have h₂ := positive_zeros_eq_of_mask_nonpole _ _ hmask ha h₁.2
  have h₃ := whole_family_clean_zero M H hH η η₀ w.val w.property j ha h₂.2 (h₂.1.mp (h₁.1.mp hz))
  exact positive_zeros_eq_of_coefficients _ _ (natural_raw_coefficients _ w) ha h₃.2 |>.imp
    (fun hh=>hh.mp h₃.1) id

end
end OAI.SevenEighths.Record12518109GainWholeGeometry
