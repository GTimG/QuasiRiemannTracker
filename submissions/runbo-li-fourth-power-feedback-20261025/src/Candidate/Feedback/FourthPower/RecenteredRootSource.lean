/- Copyright (c) 2026 Sil. Apache-2.0.
Genuine root recentering before initialKeep is enlarged. Only Y1,Y2,L
change; the total, profiles, holes, canonical marked data and enclosure
remain original. No energy estimate is assumed.
-/
import Candidate.Feedback.FourthPower.MixedFirstReferenceDispatch
import Candidate.Feedback.FourthPower.RepairedRootParameters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RecenteredRootSource
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentAddedZeroUniform CenteredMomentOriginalRadialComparison
open CenteredMomentFirstSectors CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalHeights
open MixedFirstRebase MixedFirstReferenceDispatch MixedFirstActualNonexceptional MixedFirstSeededEnergy
open MixedFirstPuncturedReference MixedLiveNormalization
open MixedOriginalNormCap MixedOriginalTail
open MixedInnerExceptionalBlock
open QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α:Type u}[Fintype α]{a b:ℝ}
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _

theorem reference_second_le (s:Source α a b)(q:ℝ)(hq:0<q)(hY:s.Y₁≤q) :
    s.T/q≤s.Y₂ := by
  apply (div_le_iff₀ hq).mpr
  rw [←s.hpY]
  have hh:=mul_le_mul_of_nonneg_right hY (s.hL.trans_le s.hY₂).le
  nlinarith

def recenter (s:Source α a b)(q:ℝ)(hq:0<q)(hY:s.Y₁≤q)
    (h₁:q≤s.X₁)(h₂:q≤s.X₂) : Source α a b :=
  {s with
    Y₁:=q
    Y₂:=s.T/q
    L:=q
    hL:=hq
    hX₁:=h₁
    hX₂:=h₂
    hY₁:=le_rfl
    hY₂:=by
      apply (le_div_iff₀ hq).mpr
      exact (mul_le_mul h₁ h₂ hq.le (hq.trans_le h₁).le).trans_eq s.hpX
    hYU₁:=h₁.trans s.hXU₁
    hYU₂:=(reference_second_le s q hq hY).trans s.hYU₂
    hpY:=by field_simp [hq.ne']}

variable (s:Source α a b)(q:ℝ)(hq:0<q)(hY:s.Y₁≤q)(h₁:q≤s.X₁)(h₂:q≤s.X₂)

theorem recenter_geometry :
    (recenter s q hq hY h₁ h₂).X₁=s.X₁ ∧ (recenter s q hq hY h₁ h₂).X₂=s.X₂ ∧
    (recenter s q hq hY h₁ h₂).Y₁=q ∧ (recenter s q hq hY h₁ h₂).Y₂=s.T/q ∧
    (recenter s q hq hY h₁ h₂).L=q ∧ (recenter s q hq hY h₁ h₂).T=s.T :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem recenter_volume : sourceVolume (recenter s q hq hY h₁ h₂)=sourceVolume s := rfl

theorem recenter_normalization :
    normalization ((recenter s q hq hY h₁ h₂).X₁*(recenter s q hq hY h₁ h₂).X₂)
      (recenter s q hq hY h₁ h₂).P=normalization (s.X₁*s.X₂) s.P := rfl

theorem recenter_enclosure (cover:OriginalEnclosure s) :
    OriginalEnclosure (recenter s q hq hY h₁ h₂) := cover

theorem recenter_profileCap : profileCap (recenter s q hq hY h₁ h₂)=profileCap s := rfl

theorem recenter_normCap :
    sourceNormCap (recenter s q hq hY h₁ h₂).P b (recenter s q hq hY h₁ h₂).T
      (recenter s q hq hY h₁ h₂).d=sourceNormCap s.P b s.T s.d := rfl

/-- Even the coarse all-column cap decreases. This uses equal products,
not a false coordinatewise claim that the new Y1 is below old Y1. -/
theorem recenter_poolCap_le : poolCap (recenter s q hq hY h₁ h₂)≤poolCap s := by
  have hx₁:0<s.X₁:=s.hL.trans_le s.hX₁
  have hx₂:0<s.X₂:=s.hL.trans_le s.hX₂
  have hy₁:0<s.Y₁:=s.hL.trans_le s.hY₁
  have hy₂:s.X₂≤s.Y₂ := by
    have he:=mul_le_mul_of_nonneg_right (hY.trans h₁) hx₂.le
    rw [s.hpX,←s.hpY] at he
    nlinarith
  have hcross:q*s.X₂≤s.X₁*s.Y₂:=mul_le_mul h₁ hy₂ hx₂.le hx₁.le
  have hprod:0≤(q-s.Y₁)*(s.X₁*s.Y₂-q*s.X₂):=
    mul_nonneg (sub_nonneg.mpr hY) (sub_nonneg.mpr hcross)
  have hid:(s.X₁+s.Y₁)*(s.X₂+s.Y₂)*q-(s.X₁+q)*(s.X₂*q+s.T)=
      (q-s.Y₁)*(s.X₁*s.Y₂-q*s.X₂) := by
    calc
      _=(q-s.Y₁)*(s.X₁*s.Y₂-q*s.X₂)+(q+s.X₁)*(s.Y₁*s.Y₂-s.T):=by ring
      _=_:=by rw [s.hpY];ring
  have hrect:(s.X₁+q)*(s.X₂+s.T/q)≤(s.X₁+s.Y₁)*(s.X₂+s.Y₂) := by
    apply (mul_le_mul_iff_left₀ hq).mp
    calc
      _=(s.X₁+q)*(s.X₂*q+s.T):=by field_simp [hq.ne'] <;> ring
      _≤_:=by linarith
  have hfactor:0≤(128*b)^2/(pairNorm s.d)*(∏i,256*s.P i) := by
    have hd:0<pairNorm s.d:=pairNorm_pos s.hd.1 s.hd.2
    have hp:0≤∏i,256*s.P i:=Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
    positivity
  convert mul_le_mul_of_nonneg_left hrect hfactor using 1 <;> simp only [poolCap,recenter] <;> ring

/-- Actual new reference lengths inherit the old polynomial bounds.
The original all-column cap may be reapplied to these four bounds. -/
theorem recenter_length_caps (X:ℝ)(hX₁:s.X₁≤X)(hX₂:s.X₂≤X)(hY₂:s.Y₂≤X) :
    (recenter s q hq hY h₁ h₂).X₁≤X ∧ (recenter s q hq hY h₁ h₂).X₂≤X ∧
    (recenter s q hq hY h₁ h₂).Y₁≤X ∧ (recenter s q hq hY h₁ h₂).Y₂≤X :=
  ⟨hX₁,hX₂,h₁.trans hX₁,(reference_second_le s q hq hY).trans hY₂⟩

section Ray
variable (rayM:Id)[NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)

theorem recenter_canonical (W:ℝ→ℂ)(Cap Lcap Z:ℝ)(η₀:Character)
    (θ:α→RayQuotient.Characters rayM H)(w σ freq:α→ℝ)(t:ℝ)(R₀:α→Finset Id)
    (hc:Canonical rayM H hH W Cap Lcap Z η₀ θ w σ freq t R₀ s) :
    Canonical rayM H hH W Cap Lcap Z η₀ θ w σ freq t R₀ (recenter s q hq hY h₁ h₂) := hc

end Ray

theorem height_rectangle_recenter (ha:0<a)(χ:Character)(t A B:ℝ) :
    heightRectangle (recenter s q hq hY h₁ h₂) ha χ t A B=heightRectangle s ha χ t A B := rfl

set_option maxHeartbeats 500000 in
/-- The old comparison rectangle is zero, but the NEW reference is
retained exactly. This identity is before taking any absolute values. -/
theorem selected_row_split (ha:0<a)(hd:s.d=(1,1))(hG:s.G=1)
    (hsmall:s.Y₁≤comparisonScale b ∨ s.Y₂≤comparisonScale b)
    (η:Character)(m:O)(F:Id)(z:O)(hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (r:SelectedCharacter η m F z)(t:ℝ) :
    normalization (s.X₁*s.X₂) s.P*selectedPolynomial s ha 1 F η m 1 t z=
      normalization (s.X₁*s.X₂) s.P*selectedPolynomial (recenter s q hq hY h₁ h₂) ha 1 F η m 1 t z+
        heightRectangle s ha r.character t q (s.T/q) := by
  rw [selected_uncentered s ha hd hG hsmall η m F z hmLam hm2 r t]
  have hc:=selected_centering (recenter s q hq hY h₁ h₂) ha hd hG η m F z hmLam hm2 r t
  convert hc using 1 <;> rfl

theorem selected_row_square (ha:0<a)(hd:s.d=(1,1))(hG:s.G=1)
    (hsmall:s.Y₁≤comparisonScale b ∨ s.Y₂≤comparisonScale b)
    (η:Character)(m:O)(F:Id)(z:O)(hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (r:SelectedCharacter η m F z)(t:ℝ) :
    ‖normalization (s.X₁*s.X₂) s.P*selectedPolynomial s ha 1 F η m 1 t z‖^2≤
      2*(‖normalization (s.X₁*s.X₂) s.P*
        selectedPolynomial (recenter s q hq hY h₁ h₂) ha 1 F η m 1 t z‖^2+
        ‖heightRectangle s ha r.character t q (s.T/q)‖^2) := by
  rw [selected_row_split s q hq hY h₁ h₂ ha hd hG hsmall η m F z hmLam hm2 r t]
  have hn:=norm_add_le
    (normalization (s.X₁*s.X₂) s.P*selectedPolynomial (recenter s q hq hY h₁ h₂) ha 1 F η m 1 t z)
    (heightRectangle s ha r.character t q (s.T/q))
  have hA:=norm_nonneg
    (normalization (s.X₁*s.X₂) s.P*selectedPolynomial (recenter s q hq hY h₁ h₂) ha 1 F η m 1 t z)
  have hB:=norm_nonneg (heightRectangle s ha r.character t q (s.T/q))
  have hAB:=norm_nonneg
    (normalization (s.X₁*s.X₂) s.P*selectedPolynomial (recenter s q hq hY h₁ h₂) ha 1 F η m 1 t z+
      heightRectangle s ha r.character t q (s.T/q))
  nlinarith [sq_nonneg (‖normalization (s.X₁*s.X₂) s.P*
    selectedPolynomial (recenter s q hq hY h₁ h₂) ha 1 F η m 1 t z‖-
      ‖heightRectangle s ha r.character t q (s.T/q)‖)]

end
end Candidate.Feedback.FourthPower.RecenteredRootSource
