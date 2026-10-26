/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MixedBootstrapNaturalBatch
import Candidate.Cycle63.Marked.WholeFamilyMaximum

set_option autoImplicit false
namespace OAI.SevenEighths.MixedBootstrapNaturalBases
noncomputable section
open scoped Classical
open HeckeFamily HeckeFiniteDeletion HeckeDetectorZeros LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource Cycle63Moment Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The changed fixed bases preserve the buffered zero maximum exactly,
including all moving conductor deletions in the original geometric rows. -/
theorem whole_family_maximum (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀)
    (hu₀ : u₀≠0) (R₀ : Ideal O) (hR₀ : R₀≠0)
    (χ : Character) (u : O) (hu : u≠0) (R : Ideal O) (hR : R≠0)
    (hcoeff : ∀I,idealCoeff χ I=idealCoeff
      (excluded (naturalRow (excluded F₀.character R₀) u hu).character R) I)
    (hn : ∀j,(wholeSourceFamily M H hH η₀ χ j).residue≠1) :
    let family:=fun j=>(naturalRow (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u hu).character
    ∃hc : ∀j,(family j).residue≠1,∀T,
      zeroMaximum family hc T=zeroMaximum (wholeSourceFamily M H hH η₀ χ) hn T := by
  intro family
  obtain ⟨hc,hmax⟩ := whole_family_clean_maximum M H hH (excluded F₀.character R₀)
    η₀ χ u hu R hR hcoeff hn
  have heq := fun j I=>natural_coefficients M H hH ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ j u hu I
  have hf := family_nonprincipal_of_coefficients _ _ hc heq
  refine ⟨hf,?_⟩
  intro T
  exact (family_maximum_of_coefficients _ _ hc hf heq T).symm.trans (hmax T)

end
end OAI.SevenEighths.MixedBootstrapNaturalBases
