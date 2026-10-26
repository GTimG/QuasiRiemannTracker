/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The LOW source is applied to each actual positive corner separately. No
simultaneous support of both corners is inferred from a centered difference. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalNewtonEnergy
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CorrectedCenteredDifference
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowPositiveCore
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open CorrectedCentered Admission.RetainedLow
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

def positiveNewtonCofactorPlain (second:Bool)(s:Input ι)(A₁ A₂ R:Ideal O)(b:ℝ)
    (S A:Finset (Ideal O))(τ:Character)(t:ℝ)(z:O):ℂ :=
  let d:=newtonDivisorPair S A
  positiveFrozenRow (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t) s.W₁ s.W₂
    (A₁*d.1) (A₂*d.2) b
    ((if second then s.Y₁ else s.X₁)/d.1.absNorm)
    ((if second then s.Y₂ else s.X₂)/d.2.absNorm)
    ((s.X₁*s.X₂)/pairNorm d)

lemma positive_newton_corner_normalization (second:Bool)(s:Input ι)(A₁ A₂ R:Ideal O)(b:ℝ)
    (S A:Finset (Ideal O))(τ:Character)(t:ℝ)(z:O):
    positiveNewtonCofactorPlain second s A₁ A₂ R b S A τ t z=
      let d:=newtonDivisorPair S A
      let X₁:=(if second then s.Y₁ else s.X₁)/d.1.absNorm
      let X₂:=(if second then s.Y₂ else s.X₂)/d.2.absNorm
      positiveFrozenRow (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t) s.W₁ s.W₂
        (A₁*d.1) (A₂*d.2) b X₁ X₂ (X₁*X₂) := by
  cases second <;> simp only [positiveNewtonCofactorPlain,Bool.false_eq_true,ite_false,ite_true]
  · rw [div_mul_div_comm];rfl
  · rw [div_mul_div_comm,s.same_product];rfl

lemma newton_cofactor_positive_difference (s:Input ι)(A₁ A₂ R:Ideal O)(b:ℝ)
    (S A:Finset (Ideal O))(τ:Character)(t:ℝ)(z:O)
    (hb:0≤b)(hb₁:s.b₁≤b)(hb₂:s.b₂≤b)(hd:GoodPair (newtonDivisorPair S A)):
    newtonCofactorPlain s A₁ A₂ R b S A τ t z=
      positiveNewtonCofactorPlain false s A₁ A₂ R b S A τ t z-
      positiveNewtonCofactorPlain true s A₁ A₂ R b S A τ t z := by
  have h₁:(0:ℝ)<(newtonDivisorPair S A).1.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd.1)
  have h₂:(0:ℝ)<(newtonDivisorPair S A).2.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd.2.1)
  unfold newtonCofactorPlain
  rw [frozenCenteredRow_eq_difference _ _ _ _ _ _ _ _ _ _ _ hb
    (div_pos s.X₁_pos h₁) (div_pos s.X₂_pos h₂) (div_pos s.Y₁_pos h₁) (div_pos s.Y₂_pos h₂)
    (fun x hx=>(s.support₁ hx).trans hb₁) (fun x hx=>(s.support₂ hx).trans hb₂)]
  simp only [positiveNewtonCofactorPlain,positiveFrozenRow,Bool.false_eq_true,ite_false,ite_true]
  ring

/-- Each corner retains its own literal nonzero-row subset. The source
may therefore use only that corner's supported clipped-length budget. -/
theorem centered_newton_positive_corner_family {Row:Type*}(rows:Finset Row)
    (ι:Row→Type*)[∀r,Fintype (ι r)](s:∀r,Input (ι r))
    (A₁ A₂ R:Row→Ideal O)(b:Row→ℝ)(S A:Finset (Ideal O))
    (τ:Row→Character)(t:Row→ℝ)(z:Row→O)(slots:Row→ℂ)(weight:Row→ℝ)
    (hw:∀r∈rows,0≤weight r)(hb:∀r∈rows,0≤b r)
    (hb₁:∀r∈rows,(s r).b₁≤b r)(hb₂:∀r∈rows,(s r).b₂≤b r)
    (hd:GoodPair (newtonDivisorPair S A)):
    let corner:=fun second r=>positiveNewtonCofactorPlain second (s r) (A₁ r) (A₂ r) (R r) (b r) S A (τ r) (t r) (z r)*slots r
    (∑r∈rows,‖newtonCofactorPlain (s r) (A₁ r) (A₂ r) (R r) (b r) S A (τ r) (t r) (z r)*slots r‖^2*weight r)≤
      2*((∑r∈rows.filter (fun r=>corner false r≠0),‖corner false r‖^2*weight r)+
        (∑r∈rows.filter (fun r=>corner true r≠0),‖corner true r‖^2*weight r)) := by
  classical
  intro corner
  have hfilter (second:Bool):
      (∑r∈rows.filter (fun r=>corner second r≠0),‖corner second r‖^2*weight r)=
        ∑r∈rows,‖corner second r‖^2*weight r := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h:corner second r=0 <;> simp [h]
  rw [hfilter false,hfilter true,←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  rw [newton_cofactor_positive_difference (s r) (A₁ r) (A₂ r) (R r) (b r) S A (τ r) (t r) (z r)
    (hb r hr) (hb₁ r hr) (hb₂ r hr) hd,sub_mul]
  have hnorm:=norm_sub_le (corner false r) (corner true r)
  have hsq:‖corner false r-corner true r‖^2≤2*(‖corner false r‖^2+‖corner true r‖^2) := by
    nlinarith [norm_nonneg (corner false r),norm_nonneg (corner true r),norm_nonneg (corner false r-corner true r),
      sq_nonneg (‖corner false r‖-‖corner true r‖)]
  have hh:=mul_le_mul_of_nonneg_right hsq (hw r hr)
  convert hh using 1 <;> (try rfl) <;> ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.positive_newton_corner_normalization
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.newton_cofactor_positive_difference
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.centered_newton_positive_corner_family
