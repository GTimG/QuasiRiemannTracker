/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual shortened original ordinary factor enters P4 at its own length.
Its independent height is incorporated by the exact unit-phase identity.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafReindex
import Candidate.C092.transport.TerminalActualRowShort
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TerminalActualRow

/-- The short ordinary height is retained exactly as the profile twist;
only the outside phase of modulus one is omitted from the norm. -/
theorem terminal_original_short_twist {U Bmask bPhi : ℝ} (s : NaturalState U Bmask bPhi)
    (u : FreeRow) (hu : s.radial.keep u.val)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support W⊆Icc A B)
    (hW : ContDiff ℝ ∞ W) (t X : ℝ) (hX : 0<X) :
    ‖original s.character s.mask 1 u.val W t X‖=
      ‖original s.character s.mask 1 u.val (twistProfile W 0 t) 0 X‖ := by
  rw [original_short_norm s u hu W A B hA hs hW t X hX,
    original_short_norm s u hu (twistProfile W 0 t) A B hA
      ((twistProfile_support W 0 t).trans hs)
      (twistProfile_smooth W 0 t A B hA hs hW) 0 X hX,
    polynomial_twistProfile]

/-- This length belongs to the independently shortened original factor.
It is unrelated to the selected detector's inverse dyad. -/
theorem terminal_actual_short_scale {U d X : ℝ} (hUd : 1<U^d) (hX : 0<X) :
    (U^d)^(Real.logb (U^d) X)=X :=
  Real.rpow_logb (zero_lt_one.trans hUd) (ne_of_gt hUd) hX

/-- P4's literal product is the same original physical energy at the
actual shortened scale, with all other factors and marks unchanged. -/
theorem terminal_actual_short_product {U Bmask bPhi d : ℝ} (s : NaturalState U Bmask bPhi)
    (u : FreeRow) (hu : s.radial.keep u.val)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support W⊆Icc A B)
    (hW : ContDiff ℝ ∞ W) (t X : ℝ) (hX : 0<X) (hUd : 1<U^d) (long mark : ℂ) :
    ‖long*original s.character s.mask 1 u.val W t X*mark‖^2=
      ‖long*original s.character s.mask 1 u.val (twistProfile W 0 t) 0
        ((U^d)^(Real.logb (U^d) X))*mark‖^2 := by
  rw [terminal_actual_short_scale hUd hX]
  simp only [norm_mul,terminal_original_short_twist s u hu W A B hA hs hW t X hX]

#print axioms terminal_original_short_twist
#print axioms terminal_actual_short_scale
#print axioms terminal_actual_short_product
end
end QRH.Cycle092.RegularColoredForward
