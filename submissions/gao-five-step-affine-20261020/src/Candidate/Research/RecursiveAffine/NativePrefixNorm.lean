/- Literal source arithmetic controlling each finite accumulated prefix. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Cycle63.Physical.InitialMass.SecondCoarseSupport

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve IdealMobiusDivisorSum Cycle63Moment Cycle63InitialMass
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentSectorLocalization
open Cycle153Reachable

namespace NativePaidPathNode
variable {Z : ℝ} (p : NativePaidPathNode Z)

/-- Native X2 has only the actual first numerator as a positive norm term.
The first common ideal is bounded at the physical source cap 130, entirely
independently of the accumulated-prefix count cap. -/
theorem coordinate_two_source_cap
    (hfirst : (p.first.1.1.absNorm:ℝ) ≤ (Z^p.unit)^(130:ℝ))
    (hrow : p.rowWidth ≤ 2) (hamp : 0 ≤ p.amp)
    (hloss : 0 ≤ frequencyLoss (Z^p.unit) 32 p.xi+p.reserve)
    (heps : p.eps ≤ 1) : p.coordinate 2 ≤ 653*p.unit := by
  have hlog : Real.logb (Z^p.unit) (p.first.1.1.absNorm:ℝ) ≤ 130 :=
    (Real.logb_le_iff_le_rpow p.local_base
      (CenteredMomentFirstScale.norm_pos _ p.firstC.1)).mpr hfirst
  have hactive : 0 ≤ Real.logb (Z^p.unit)
      ((Ideal.span {activeConductor p.first.1.1 p.first.1.2}).absNorm:ℝ) :=
    Real.logb_nonneg p.local_base
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (activeConductor_supported _ _ p.firstC).1)))
  have hn := first_numerator_log_le (!p.reflected) p.first p.firstC p.firstD
    (Z^p.unit) p.local_base
  change Real.logb (Z^p.unit)
    ((Ideal.span {firstSourceNumerator (!p.reflected) p.first}).absNorm:ℝ) ≤ _ at hn
  have hmax : 0 ≤ max
      (Real.logb (Z^p.unit) ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ)-
       Real.logb (Z^p.unit) ((if p.reflected then p.first.1.1 else p.first.1.2).absNorm:ℝ)) 0 :=
    le_max_right _ _
  have hraw : actualHighCoordinates p.reflected (!p.reflected) p.second p.first p.C p.D
      p.inactive (Z^p.unit) p.rowWidth p.length p.amp p.xi p.reserve p.eps 2 ≤ 653 := by
    change p.rowWidth - Real.logb (Z^p.unit)
        ((Ideal.span {activeConductor p.first.1.1 p.first.1.2}).absNorm:ℝ) -
      max (Real.logb (Z^p.unit) ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ)-
           Real.logb (Z^p.unit) ((if p.reflected then p.first.1.1 else p.first.1.2).absNorm:ℝ)) 0 +
      Real.logb (Z^p.unit) ((Ideal.span {firstSourceNumerator (!p.reflected) p.first}).absNorm:ℝ)-
      6*p.amp-(frequencyLoss (Z^p.unit) 32 p.xi+p.reserve)+p.eps ≤ 653
    linarith only [hlog,hactive,hn,hmax,hrow,hamp,hloss,heps]
  dsimp only [coordinate]
  have h := mul_le_mul_of_nonneg_left hraw p.unit_pos.le
  linarith only [h]

end NativePaidPathNode

/-- The actual relative scale bridge bounds the INCREMENT of the global
prefix. The old prefix offset remains explicit, and the child row scale
is discarded only using its genuine nonnegativity. -/
theorem native_prefix_increment
    {Z : ℝ} (p : NativePaidPathNode Z)
    (hfirst : (p.first.1.1.absNorm:ℝ) ≤ (Z^p.unit)^(130:ℝ))
    (hrow : p.rowWidth ≤ 2) (hamp : 0 ≤ p.amp)
    (hloss : 0 ≤ frequencyLoss (Z^p.unit) 32 p.xi+p.reserve)
    (heps : p.eps ≤ 1) (hunit : p.unit ≤ 1)
    (mChild logChild logParent scalePad : ℝ)
    (hm : 0 ≤ mChild) (hpad : scalePad ≤ p.unit)
    (hscale : mChild+logChild-logParent ≤ p.coordinate 2+scalePad) :
    logChild-logParent ≤ 1000 := by
  have hcoord := p.coordinate_two_source_cap hfirst hrow hamp hloss heps
  linarith only [hcoord,hunit,hm,hpad,hscale]

/-- Genuine native scale data propagate the global prefix invariant to
its chronological successor. No local HIGH cap is re-assumed after
contracting the base. -/
theorem global_prefix_cap_of_native_scale
    {α : Type} [Fintype α] [DecidableEq α]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)
    (p : NativePaidPathNode C.globalBase) (hunit : p.unit=N.unit)
    (hfirst : (p.first.1.1.absNorm:ℝ) ≤ (C.globalBase^p.unit)^(130:ℝ))
    (hrow : p.rowWidth ≤ 2) (hamp : 0 ≤ p.amp)
    (hloss : 0 ≤ frequencyLoss (C.globalBase^p.unit) 32 p.xi+p.reserve)
    (heps : p.eps ≤ 1) (child : O) (hchild : child≠0)
    (mChild scalePad : ℝ) (hm : 0 ≤ mChild) (hpad : scalePad ≤ p.unit)
    (hscale : mChild+Real.logb C.globalBase ((Ideal.span {child}).absNorm:ℝ)-
        Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤
      p.coordinate 2+scalePad) :
    ((Ideal.span {child}).absNorm:ℝ) ≤ C.globalBase^prefixCap (j.val+1) := by
  have hparentpos : (0:ℝ) < ((Ideal.span {N.presentation.mult}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr N.presentation.hv))
  have hchildpos : (0:ℝ) < ((Ideal.span {child}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hchild))
  have hp := (Real.logb_le_iff_le_rpow C.globalBase_gt_one hparentpos).mpr
    N.presentation_global_norm
  have hi := native_prefix_increment p hfirst hrow hamp hloss heps
    (hunit ▸ N.unit_le_one) mChild _ _ scalePad hm hpad hscale
  apply (Real.logb_le_iff_le_rpow C.globalBase_gt_one hchildpos).mp
  rw [prefixCap_succ]
  linarith only [hp,hi]

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.global_prefix_cap_of_native_scale
