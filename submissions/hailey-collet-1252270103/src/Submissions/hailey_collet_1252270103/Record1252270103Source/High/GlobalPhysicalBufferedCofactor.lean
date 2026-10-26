/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two genuine source branches act on the same buffered original family. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalCofactorPartition
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open Cycle61InitialMass LocalMoment
local notation "O"=>HeckeFamily.O

theorem centered_buffered_joint_family {Row:Type*}(rows:Finset Row)
    (ι:Row→Type*)[∀r,Fintype (ι r)](s:∀r,Input (ι r))
    (A₁ A₂ R:Row→Ideal O)(b:Row→ℝ)(S A:Finset (Ideal O))
    (τ:Row→Character)(t:Row→ℝ)(z:Row→O)(slots:Row→ℂ)(weight:Row→ℝ)
    (hw:∀r∈rows,0≤weight r)(hb:∀r∈rows,0≤b r)
    (hb₁:∀r∈rows,(s r).b₁≤b r)(hb₂:∀r∈rows,(s r).b₂≤b r)
    (hd:GoodPair (newtonDivisorPair S A))(e q:ℝ)(select:Row→BufferIndex e):
    let low:=rows.filter (fun r=>bufferValue e (select r)<(q+1)/2)
    let high:=rows.filter (fun r=>(q+1)/2≤bufferValue e (select r))
    let energy:=fun r=>‖newtonCofactorPlain (s r) (A₁ r) (A₂ r) (R r) (b r) S A
      (τ r) (t r) (z r)*slots r‖^2*weight r
    let corner:=fun side r=>‖positiveNewtonCofactorPlain side (s r) (A₁ r) (A₂ r) (R r)
      (b r) S A (τ r) (t r) (z r)*slots r‖^2*weight r
    ∀E₀ E₁ EH:ℝ,(∑r∈low,corner false r)≤E₀→(∑r∈low,corner true r)≤E₁→
      (∑r∈high,energy r)≤EH→(∑r∈rows,energy r)≤2*(E₀+E₁)+EH := by
  classical
  intro low high energy corner E₀ E₁ EH h₀ h₁ hH
  have hL:=centered_newton_positive_corner_family low ι s A₁ A₂ R b S A τ t z slots weight
    (fun r hr=>hw r (Finset.mem_filter.mp hr).1)
    (fun r hr=>hb r (Finset.mem_filter.mp hr).1)
    (fun r hr=>hb₁ r (Finset.mem_filter.mp hr).1)
    (fun r hr=>hb₂ r (Finset.mem_filter.mp hr).1) hd
  have hfilter (side:Bool):
      (∑r∈low.filter (fun r=>positiveNewtonCofactorPlain side (s r) (A₁ r) (A₂ r) (R r)
        (b r) S A (τ r) (t r) (z r)*slots r≠0),corner side r)=∑r∈low,corner side r := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hn
    have hz:positiveNewtonCofactorPlain side (s r) (A₁ r) (A₂ r) (R r)
      (b r) S A (τ r) (t r) (z r)*slots r=0 := by
      by_contra hne
      exact hn (Finset.mem_filter.mpr ⟨hr,hne⟩)
    simp only [corner,hz,norm_zero,zero_pow (by decide:2≠0),zero_mul]
  change (∑r∈low,energy r)≤2*((∑r∈low.filter _,corner false r)+(∑r∈low.filter _,corner true r)) at hL
  rw [hfilter false,hfilter true] at hL
  have heq:(∑r∈rows,energy r)=(∑r∈low,energy r)+(∑r∈high,energy r):=by
    simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not
      (s:=rows) (p:=fun r=>bufferValue e (select r)<(q+1)/2) (f:=energy)).symm
  rw [heq]
  linarith only [hL,h₀,h₁,hH]
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.centered_buffered_joint_family
