import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.WholeFamilyAnchor
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Density.NaturalMaskTransport
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily HeckeFiniteDeletion LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion Cycle63Moment

theorem natural_excluded_base_coefficients (η : Character) (R : Ideal O) (hR : R≠0)
    (u : O) (hu : u≠0) (I : Ideal O) :
    idealCoeff (naturalRow (excluded η R) u hu).character I=
      idealCoeff (excluded (naturalRow η u hu).character R) I := by
  rw [(naturalRow (excluded η R) u hu).ideal,excluded_ideal _ _ hR,
    excluded_ideal _ _ hR,(naturalRow η u hu).ideal]
  split_ifs <;> simp

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem whole_base_excluded_coefficients (η η₀ : Character) (R : Ideal O) (hR : R≠0)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceBase M H hH η₀ (excluded η R) j) I=
      idealCoeff (excluded (wholeSourceBase M H hH η₀ η j) R) I := by
  cases j with
  | inl j=>rfl
  | inr j=>
    change idealCoeff (((excluded η R).product _).product _) I=_
    simp only [idealCoeff_product,excluded_ideal _ _ hR,wholeSourceBase]
    split_ifs <;> simp [idealCoeff_product]

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
