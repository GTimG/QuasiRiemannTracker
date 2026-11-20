/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original independently shortened ordinary column is the genuine detector
polynomial, with its outside unit phase explicit and exact normalization. -/
import Candidate.C092.transport.TerminalActualRowState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
set_option autoImplicit false
namespace QRH.Cycle092.TerminalActualRow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentCommonMaskEnergy CenteredMomentHeckeHeight CenteredMomentLattice CenteredMomentHeckeTwist
open ConcreteTraceCRT ConcretePrimeRowBridge
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O

theorem short_profile_exact (W : ℝ→ℂ) (A B : ℝ) (hA : 0< A)
    (hs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    (normPowerProfile W A B hA hs hW t:ℝ→ℂ)=twistProfile W 0 t := by
  funext x
  rw [normPowerProfile_apply]
  dsimp [twistProfile,HeckeDyadic.shift]
  simp only [Complex.ofReal_zero,zero_sub,neg_neg]
  rw [mul_comm Complex.I (t:ℂ)]
  ring

/-- The outside phase is not deleted from the identity. Its modulus is one,
so every terminal source energy sees the original short factor unchanged. -/
theorem original_short_phase {U Bmask bPhi : ℝ} (s : NaturalState U Bmask bPhi)
    (u : FreeRow) (hu : s.radial.keep u.val)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0< A) (hs : Function.support W⊆Icc A B)
    (hW : ContDiff ℝ ∞ W) (t X : ℝ) (hX : 0< X) :
    original s.character s.mask 1 u.val W t X=
      (X:ℂ)^(Complex.I*t)*polynomial
        (excluded (naturalRow s.character u.val (s.row_ne_zero u.val hu)).character s.puncture)
          false W X 0 t := by
  let F:=naturalRow s.character u.val (s.row_ne_zero u.val hu)
  have hrow : ∀n,elementCoeff (excluded F.character s.puncture) n=
      CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom s.character) s.mask 1 (1*u.val) n := by
    intro n
    simpa only [one_mul,NaturalState.mask] using F.masked_element s.puncture s.puncture_ne_zero n
  rw [original,rowTwistedSum_eq s.character (excluded F.character s.puncture) s.mask 1 u.val hrow]
  rw [normalized_twisted_plain _ W A B hA hs hW t X hX,short_profile_exact W A B hA hs hW t,
    polynomial_twistProfile]

 theorem original_short_norm {U Bmask bPhi : ℝ} (s : NaturalState U Bmask bPhi)
    (u : FreeRow) (hu : s.radial.keep u.val)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0< A) (hs : Function.support W⊆Icc A B)
    (hW : ContDiff ℝ ∞ W) (t X : ℝ) (hX : 0< X) :
    ‖original s.character s.mask 1 u.val W t X‖=
      ‖polynomial (excluded (naturalRow s.character u.val (s.row_ne_zero u.val hu)).character s.puncture)
        false W X 0 t‖ := by
  rw [original_short_phase s u hu W A B hA hs hW t X hX,norm_mul]
  have hp : ‖(X:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hX (Complex.I*t)
  rw [hp,one_mul]

end
end QRH.Cycle092.TerminalActualRow
#print axioms QRH.Cycle092.TerminalActualRow.original_short_phase
#print axioms QRH.Cycle092.TerminalActualRow.original_short_norm
