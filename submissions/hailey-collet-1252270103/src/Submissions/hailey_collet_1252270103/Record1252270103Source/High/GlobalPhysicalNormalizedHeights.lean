/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two unrestricted Mellin variables are paid by a larger integration
degree. The coarse bound is the literal modified finite absolute envelope. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalNormalizedAbsolute
import Submissions.hailey_collet_1252270103.Cycle61.Physical.ExternalHeight
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform

/-- A single degree is chosen before the live family, both Mellin variables
and the scale. No tail of either integral is removed. -/
theorem modified_normalized_height_extension (τ extra target:ℝ)(hτ:0<τ)(smallDegree:ℕ):
    ∃J:ℕ,∀{α Label:Type*}[Fintype α][DecidableEq α][Fintype Label]
      (reflected:Bool)(d:Label→SecondInputDatum α)(modifier:∀l,Tuple (d l).slots→ℂ)
      (w:Label→ℂ)(Z m control Csmall Ccoarse:ℝ),
    1≤Z→0≤control→0≤Csmall→0≤Ccoarse→
    (∀t u:ℝ,(1+‖t‖)*(1+‖u‖)≤Z^τ→
      modifiedSecondNormalizedSum reflected d modifier w t u≤
        Csmall*control*((1+‖t‖)*(1+‖u‖))^smallDegree*Z^(m+target))→
    secondAbsoluteBudget d modifier w≤Ccoarse*control*Z^(m+extra)→
    ∀t u:ℝ,modifiedSecondNormalizedSum reflected d modifier w t u≤
      ((Csmall+Ccoarse)*control*Z^(m+target)*(1+‖t‖)^J)*(1+‖u‖)^(2*J) := by
  obtain ⟨J,hJ⟩:=Cycle61.Physical.extend_bounded_height_bound hτ extra target smallDegree 0
  refine ⟨J,?_⟩
  intro α Label _ _ _ reflected d modifier w Z m control Csmall Ccoarse hZ hc hs hb hsmall habs t u
  have ht:1≤1+‖t‖:=by linarith [norm_nonneg t]
  have hu:1≤1+‖u‖:=by linarith [norm_nonneg u]
  have hH:1≤(1+‖t‖)*(1+‖u‖):=by nlinarith [mul_nonneg (norm_nonneg t) (norm_nonneg u)]
  have ha:= (modified_second_normalized_absolute reflected d modifier w t u).trans habs
  have hh:=hJ Z ((1+‖t‖)*(1+‖u‖)) m
    (modifiedSecondNormalizedSum reflected d modifier w t u) control Csmall Ccoarse hZ hH hc hs hb
    (hsmall t u) (by simpa only [pow_zero,mul_one] using ha)
  rw [mul_pow] at hh
  have hp: (1+‖u‖)^J≤(1+‖u‖)^(2*J):=pow_le_pow_right₀ hu (by omega)
  calc
    _≤((Csmall+Ccoarse)*control*Z^(m+target)*(1+‖t‖)^J)*(1+‖u‖)^J := by
      convert hh using 1 <;> ring
    _≤_:=mul_le_mul_of_nonneg_left hp (by positivity)

/-- The extension uses each exact ratio fiber and preserves its two balance
factors. The resulting object is the actual normalized contraction inlet. -/
theorem modified_normalized_bound_from_truncated (τ extra target:ℝ)(hτ:0<τ)(smallDegree:ℕ):
    ∃J:ℕ,∀{α Label:Type*}[Fintype α][DecidableEq α][Fintype Label]
      (W:SchwartzMap ℝ ℂ)(d:Label→SecondInputDatum α)(modifier:∀l,Tuple (d l).slots→ℂ)
      (w:Label→ℂ)(Z Csmall Ccoarse:ℝ)(E H:ℤ→ℝ),
    1≤Z→0≤Csmall→0≤Ccoarse→
    (∀r∈secondRatioBins (fun l=>modifiedDatumBlock (d l) (modifier l)),0≤E r)→
    (∀r∈secondRatioBins (fun l=>modifiedDatumBlock (d l) (modifier l)),0<H r)→
    (∀r∈secondRatioBins (fun l=>modifiedDatumBlock (d l) (modifier l)),∀reflected:Bool,
      let datum:=fun l:SecondRatioFiber (fun l=>modifiedDatumBlock (d l) (modifier l)) r=>d l.val
      let source:=fun l=>modifiedDatumBlock (datum l) (modifier l.val)
      let weight:=secondEffectiveWeight source (fun l=>w l.val) W
      (∀t u:ℝ,(1+‖t‖)*(1+‖u‖)≤Z^τ→
        modifiedSecondNormalizedSum reflected datum (fun l=>modifier l.val) weight t u≤
          Csmall*(if reflected then E r/H r else E r*H r)*
            ((1+‖t‖)*(1+‖u‖))^smallDegree*Z^target) ∧
      secondAbsoluteBudget datum (fun l=>modifier l.val) weight≤
        Ccoarse*(if reflected then E r/H r else E r*H r)*Z^extra)→
    ModifiedSecondNormalizedBound W J J d modifier w
      (fun r=>(Csmall+Ccoarse)*Z^target*E r) H := by
  obtain ⟨J,hJ⟩:=modified_normalized_height_extension τ extra target hτ smallDegree
  refine ⟨J,?_⟩
  intro α Label _ _ _ W d modifier w Z Cs Cc E H hZ hCs hCc hE hH hb
  intro r hr reflected t u datum source weight
  obtain ⟨hsmall,habs⟩:=hb r hr reflected
  have hc:0≤(if reflected then E r/H r else E r*H r):=by
    split_ifs
    · exact div_nonneg (hE r hr) (hH r hr).le
    · exact mul_nonneg (hE r hr) (hH r hr).le
  have hh:=hJ reflected datum (fun l=>modifier l.val)
    (secondEffectiveWeight source weight W) Z 0
    (if reflected then E r/H r else E r*H r) Cs Cc hZ hc hCs hCc
    (by simpa only [zero_add] using hsmall) (by simpa only [zero_add] using habs) t u
  apply hh.trans_eq
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,zero_add] <;> ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_normalized_height_extension

#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_normalized_bound_from_truncated
