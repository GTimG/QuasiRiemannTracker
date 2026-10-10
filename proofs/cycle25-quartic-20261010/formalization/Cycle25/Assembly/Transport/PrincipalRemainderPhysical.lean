/- Adapted from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Cycle25.Assembly.Transport.GeometryFacts
import Cycle25.Assembly.Transport.PrincipalRemainderTransport
import OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace Cycle25.Transport.PrincipalPhysical
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds CanonicalQuadraticSieve
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours
open Cycle25.Transport.PrincipalFiniteProduct Cycle25.Transport.PrincipalFiniteProductX Cycle25.Transport.PrincipalContours Cycle25.Transport.PrincipalTransport
local notation "Id" => Ideal HeckeFamily.O

lemma slotMultiplier_as_tuples {K : ℕ} (η : Character) (T : Fin K→Finset PrimeIdeal)
    (b : Fin K→PrimeIdeal→ℂ) (s w z : ℂ) :
    slotMultiplier η Finset.univ T b s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        slotMultiplier η Finset.univ (fun i=>{(P i).val}) (fun _ _=>1) s w z := by
  simp only [slotMultiplier,Finset.sum_singleton,one_mul]
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i (p : T i)=>b i p.val*localMultiplier η p.val s w z)]
  congr 1
  funext i
  exact (Finset.sum_coe_sort (T i) (fun p=>b i p*localMultiplier η p s w z)).symm

lemma principalPoolKernel_as_tuples {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (b : Fin K→PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    principalPoolKernel η S hS T b W0 W1 X Y Z s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z s w z := by
  unfold principalPoolKernel sourceMultiplier
  rw [slotMultiplier_as_tuples]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  ring

theorem principal_physical_pool_initial {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        principalPoolKernel η S hS T b W0 W1 X Y Z
          ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I) ∂heightMeasure := by
  let F (P : ∀i,T i) (t : HeightSpace) :=
    principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)
  have hF (P : ∀i,T i) : Integrable (F P) heightMeasure := by
    apply Cycle25.Transport.PrincipalContours.source_joint_integrable η S hS Finset.univ (fun i=>{(P i).val}) (fun _ _=>1)
      (by intro i hi p hp;simp only [Finset.mem_singleton] at hp;subst p;exact hT i _ (P i).property)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z 3 2 3 3 hX hY hZ
      (by first | (solve | norm_num) | (linarith [Cycle25.Transport.theta_bounds])) (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp_rw [principalPoolKernel_as_tuples η S hS T b W0 W1 X Y Z]
  rw [integral_finsetSum Finset.univ (fun P _=>(hF P).const_mul (∏i,b i (P i).val)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [principalRowIntegral_eq_sourceMultiplier η S hS (fun i=>(P i).val) (hdis P)
    (fun i=>hT i _ (P i).property) W0 W1 X Y Z,integral_const_mul]
  dsimp only [F,principalPoolKernel]
  ring

theorem principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta <a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e ≤ 11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact Cycle25.Transport.PrincipalTransport.source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

end Cycle25.Transport.PrincipalPhysical
end

