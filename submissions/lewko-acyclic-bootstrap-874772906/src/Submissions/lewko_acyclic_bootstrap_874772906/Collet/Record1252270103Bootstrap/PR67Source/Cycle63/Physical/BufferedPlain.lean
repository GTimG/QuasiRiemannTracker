import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.AllocationClipping
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! Actual normalized retained plain rows and the genuine buffered Hecke dyadic bound.
Uses OpenAI/math family003 `Hecke.DyadicSource` without modifying frozen upstream.
Apache-2.0 upstream attribution retained. -/
namespace Cycle63.Physical
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CenteredMomentHeckeHeight CenteredMomentRetainedProfile
open HeckeDetectorCoefficientTransfer
local notation "O" => HeckeFamily.O

/-- The all-ideal identity is structural; it is not a plain-row analytic bound. -/
theorem row_polynomial_phase (η χ : Character) (m z : O)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I =
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I)
    (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X) :
    (Real.sqrt X : ℂ)⁻¹*rowTwistedSum η m 1 z W t X =
      (X : ℂ)^(Complex.I*t)*polynomial χ false W X 0 t := by
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O =>
      (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I)*
        (Ideal.absNorm I : ℂ)^(Complex.I*t)*W ((Ideal.absNorm I : ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [idealCoeff_zero,zero_mul]))
  have hs : (∑' I : NonzeroIdeal, twistedCoefficient χ false 0 t I*W (norm I/X)) =
      rowTwistedSum η m 1 z W t X := by
    unfold rowTwistedSum
    rw [←he]
    apply tsum_congr
    intro I
    simp only [twistedCoefficient,coefficient,Bool.false_eq_true,ite_false,hcoeff,HeckeDyadic.norm,
      shift,Complex.ofReal_zero,zero_sub,neg_neg]
    push_cast
    simp only [mul_comm]
  rw [polynomial_eq_weighted χ false W X 0 t hX,hs,←mul_assoc,
    ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne')]
  have hexp : Complex.I*t+(shift 0 t-(1/2 : ℂ)) = -(1/2 : ℂ) := by
    unfold shift
    push_cast
    ring
  rw [hexp,Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 2
  simpa using (Complex.ofReal_cpow hX.le (1/2 : ℝ))

/-- Both whole-character orientations preserve the normalized row norm.
The frequency is `t`; the raw row's missing phase has unit modulus. -/
theorem row_polynomial_norm_oriented (η χ : Character) (m z : O) (reverse : Bool)
    (hcoeff : ∀ I : Ideal O,
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I =
        if reverse then star (idealCoeff χ I) else idealCoeff χ I)
    (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X) :
    ‖(Real.sqrt X : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖ =
      ‖polynomial χ false (orientedProfile reverse W) X 0 (orientedFrequency reverse t)‖ := by
  have hnorm (ψ : Character)
      (hc : ∀ I : Ideal O, idealCoeff ψ I =
        idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I) :
      ‖(Real.sqrt X : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖ =
        ‖polynomial ψ false W X 0 t‖ := by
    rw [row_polynomial_phase η ψ m z hc W t X hX,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp
  cases reverse
  · simpa only [orientedProfile,orientedFrequency,Bool.false_eq_true,ite_false] using
      hnorm χ (fun I => (hcoeff I).symm)
  · have hc : ∀ I : Ideal O, idealCoeff χ.inverse I =
        idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I := by
      intro I
      simpa only [idealCoeff_inverse_conj,ite_true,starRingEnd_apply] using (hcoeff I).symm
    rw [hnorm χ.inverse hc]
    exact norm_of_oriented_coefficients χ.inverse χ true
      (fun I => by simp only [idealCoeff_inverse_conj,ite_true]) false W X 0 t hX

/-- Clipping changes the profile, while the scalar normalizer still uses the literal
clipped scale. Raw scales below one are included. -/
theorem clipped_row_polynomial_norm (η χ : Character) (m z : O) (reverse : Bool)
    (hcoeff : ∀ I : Ideal O,
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I =
        if reverse then star (idealCoeff χ I) else idealCoeff χ I)
    (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X) :
    ‖(Real.sqrt (clippedScale X) : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖ =
      ‖polynomial χ false (orientedProfile reverse (dilated W (clipDilation X)))
        (clippedScale X) 0 (orientedFrequency reverse t)‖ := by
  rw [clipped_rowTwistedSum η m 1 z W t X hX]
  exact row_polynomial_norm_oriented η χ m z reverse hcoeff _ t _
    (zero_lt_one.trans_le (clippedScale_ge_one X))

/-- Uniform buffered plain estimate for actual retained rows. The constants and the
Mellin order are chosen before the finite character family, the row, its orientation,
and its profile. Consequently one pair of constants works for all four finite
Mellin derivative pairs when their two displayed profile budgets hold.

The all-ideal coefficient gate belongs to the actual natural masked character.
The buffered zero gate is on that same character family. Its transfer from a raw
family is a separate algebraic zero-transport obligation, not an analytic assumption
inside this theorem. The scale equality retains the literal clipping allocation. -/
theorem buffered_clipped_plain_bounds (R dmax τ ε e κ v : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hv : 0≤v)
    (hbudget : 12*e*(R+2)+8*κ+2*v≤ε)
    (profileBound : ℕ→ℝ) (hprofile : ∀ k, 0≤profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0<C ∧
    ∀ (Z d : ℝ), 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→ Character)
      (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ (j : ι) (η : Character) (m z : O) (reverse : Bool),
      (∀ I : Ideal O,
        idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I =
          if reverse then star (idealCoeff (χ j) I) else idealCoeff (χ j) I) →
    ∀ (W : ℝ→ℂ) (X r t A B : ℝ), 0<X →
      clippedScale X=(Z^d)^r → 0<A →
      Function.support (orientedProfile reverse (dilated W (clipDilation X)))⊆Set.Icc A B →
      ContDiff ℝ ∞ (orientedProfile reverse (dilated W (clipDilation X))) →
      (χ j).modulus.absNorm≤Z^d → 0≤ r → r≤R →
      |t|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^v →
      (∀ x ∈ Set.Icc (1-a-6*e) 2, ∀ u : ℝ,
        (1+|u|)^2*‖mellin (orientedProfile reverse (dilated W (clipDilation X)))
          ((x : ℂ)+u*Complex.I)‖≤profileBound 2) →
      (∀ x ∈ Set.Icc (1-a-6*e) 2, ∀ u : ℝ,
        (1+|u|)^(n+2)*‖mellin (orientedProfile reverse (dilated W (clipDilation X)))
          ((x : ℂ)+u*Complex.I)‖≤profileBound (n+2)) →
      ‖(Real.sqrt (clippedScale X) : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖^2
        ≤C*(Z^d)^((2*a-1)*r+ε) ∧
      ‖(Real.sqrt (clippedScale X) : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖^2
        ≤C*(Z^d)^((2*a-1)*min r (1-r)+ε) := by
  obtain ⟨n,C,hC,hsource⟩ := source_dyadic_bounds R dmax τ ε e κ v
    hR hdmax hτ hε he he' hκ hκ' hv hbudget profileBound hprofile
  refine ⟨n,C,hC,?_⟩
  intro Z d hZ hd hdmax' hT ι _ χ hχ a i ha ha' hzero j η m z reverse hcoeff
    W X r t A B hX hscale hA hsupport hsmooth hmod hr hrR hfreq hheight hm₂ hmn
  have hf : |orientedFrequency reverse t|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ := by
    simpa only [orientedFrequency_abs] using hfreq
  have hm₂' : ∀ x ∈ Set.Icc (1-a-6*e-0) (2-0), ∀ u : ℝ,
      (1+|u|)^2*‖mellin (orientedProfile reverse (dilated W (clipDilation X)))
        ((x : ℂ)+u*Complex.I)‖≤profileBound 2 := by simpa only [sub_zero] using hm₂
  have hmn' : ∀ x ∈ Set.Icc (1-a-6*e-0) (2-0), ∀ u : ℝ,
      (1+|u|)^(n+2)*‖mellin (orientedProfile reverse (dilated W (clipDilation X)))
        ((x : ℂ)+u*Complex.I)‖≤profileBound (n+2) := by simpa only [sub_zero] using hmn
  have hbound := hsource Z d hZ hd hdmax' hT χ hχ a i ha ha' hzero j false
    (orientedProfile reverse (dilated W (clipDilation X))) A B hA hsupport hsmooth
    r 0 (orientedFrequency reverse t) hmod hr hrR hf hheight hm₂' hmn'
  rw [clipped_row_polynomial_norm η (χ j) m z reverse hcoeff W t X hX,hscale]
  exact hbound

end
end Cycle63.Physical

end Record1252270103Bootstrap.PR67
