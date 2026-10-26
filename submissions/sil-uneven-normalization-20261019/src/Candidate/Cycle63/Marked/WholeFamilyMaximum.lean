import Candidate.Cycle63.Marked.WholeFamilyZeros

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical
open HeckeFamily HeckeFiniteDeletion HeckeDetectorZeros LocalMoment
open CenteredMomentNaturalRowSource Cycle63Moment
local notation "O" => HeckeFamily.O

theorem family_nonprincipal_of_coefficients {Label : Type*}
    (χ ψ : Label→Character) (hχ : ∀j,(χ j).residue≠1)
    (hcoeff : ∀j I,idealCoeff (χ j) I=idealCoeff (ψ j) I) :
    ∀j,(ψ j).residue≠1 := by
  intro j hp
  exact hχ j ((principal_iff_of_mask _ _ (coefficient_equality_mask _ _ (hcoeff j))).mpr hp)

theorem family_maximum_of_coefficients {Label : Type*} [Fintype Label]
    (χ ψ : Label→Character) (hχ : ∀j,(χ j).residue≠1)
    (hψ : ∀j,(ψ j).residue≠1)
    (hcoeff : ∀j I,idealCoeff (χ j) I=idealCoeff (ψ j) I) (T : ℝ) :
    zeroMaximum χ hχ T=zeroMaximum ψ hψ T :=
  zeroMaximum_eq_of_mask χ ψ hχ hψ T (fun j=>coefficient_equality_mask _ _ (hcoeff j))

theorem excluded_nonprincipal_iff (χ : Character) (R : Ideal O) :
    (excluded χ R).residue≠1 ↔ χ.residue≠1 := by
  exact not_congr (principal_iff_of_mask _ _ (fun I=>excludePrimes_mask χ _ (support_prime R) I))

theorem family_maximum_excluded {Label : Type*} [Fintype Label]
    (χ : Label→Character) (R : Ideal O) (hχ : ∀j,(χ j).residue≠1)
    (hn : ∀j,(excluded (χ j) R).residue≠1) (T : ℝ) :
    zeroMaximum (fun j=>excluded (χ j) R) hn T=zeroMaximum χ hχ T :=
  zeroMaximum_eq_of_mask _ _ _ _ T (fun j I=>excludePrimes_mask (χ j) _ (support_prime R) I)

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The fixed masked dictionary has exactly the buffered maximum of the
actual geometric family. Both the large moving Euler holes and the fixed
anchor mask disappear through zero-set equality on the positive half-plane. -/
theorem whole_family_clean_maximum (η η₀ χ : Character) (u : O) (hu : u≠0)
    (R : Ideal O) (hR : R≠0)
    (hcoeff : ∀I,idealCoeff χ I=idealCoeff (excluded (naturalRow η u hu).character R) I)
    (hn : ∀j,(wholeSourceFamily M H hH η₀ χ j).residue≠1) :
    let clean:=fun j=>(naturalRow
      (wholeSourceBase M H hH η₀ (excluded η (wholeAnchorMask M H hH η₀)) j) u hu).character
    ∃hc : ∀j,(clean j).residue≠1,∀T,
      zeroMaximum clean hc T=zeroMaximum (wholeSourceFamily M H hH η₀ χ) hn T := by
  intro clean
  let raw:=fun j=>(naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character
  have hm : ∀j I,idealCoeff (wholeSourceFamily M H hH η₀ χ j) I=
      idealCoeff (excluded (raw j) R) I :=
    whole_source_family_mask M H hH η₀ η χ u hu (naturalRow η u hu) R hR hcoeff
      (fun j=>naturalRow (wholeSourceBase M H hH η₀ η j) u hu)
  have he := family_nonprincipal_of_coefficients _ _ hn hm
  have hr : ∀j,(raw j).residue≠1:=fun j=>(excluded_nonprincipal_iff _ R).mp (he j)
  let A:=wholeAnchorMask M H hH η₀
  have hA : A≠0:=wholeAnchorMask_ne_zero M H hH η₀
  have hd : ∀j,(excluded (raw j) A).residue≠1:=fun j=>(excluded_nonprincipal_iff _ A).mpr (hr j)
  have hc : ∀j I,idealCoeff (clean j) I=idealCoeff (excluded (raw j) A) I := by
    intro j I
    rw [show idealCoeff (clean j) I=
      idealCoeff (wholeSourceBase M H hH η₀ (excluded η A) j) I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondHeightFamily.fixedBadMask^6*u) I
      from (naturalRow _ u hu).ideal I]
    rw [whole_base_excluded_coefficients M H hH η η₀ A hA j I,
      excluded_ideal _ _ hA,excluded_ideal _ _ hA,(naturalRow _ u hu).ideal]
    split_ifs <;> simp
  have hnclean:=family_nonprincipal_of_coefficients _ _ hd (fun j I=>(hc j I).symm)
  refine ⟨hnclean,?_⟩
  intro T
  calc
    _=zeroMaximum (fun j=>excluded (raw j) A) hd T:=
      family_maximum_of_coefficients _ _ hnclean hd hc T
    _=zeroMaximum raw hr T:=family_maximum_excluded raw A hr hd T
    _=zeroMaximum (fun j=>excluded (raw j) R) he T:=
      (family_maximum_excluded raw R hr he T).symm
    _=_:=(family_maximum_of_coefficients _ _ hn he hm T).symm

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.whole_family_clean_maximum
