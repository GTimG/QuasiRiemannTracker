/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One buffered partition of the original selected rows serves both source
branches. Positive corners are split only within LOW; HIGH keeps the exact
centered cofactor and its original singleton product. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalPositiveCornerSplit
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularRetainedNaturalBins
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState Cycle61Moment.LowBranch
open Cycle61InitialMass LocalMoment Record1252270103Source
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

/-- The actual buffered selector supplies genuine LOW and HIGH guards on
one original finite family. The final two inlets are joint source estimates,
not individual row bounds. -/
theorem actual_buffered_cofactor_partition {Row:Type*}(rows:Finset Row)
    (ι:Row→Type*)[∀r,Fintype (ι r)](s:∀r,Input (ι r))
    (A₁ A₂ R:Row→Ideal O)(b:Row→ℝ)(S A:Finset (Ideal O))
    (τ:Row→Character)(height:Row→ℝ)(z:Row→O)(slots:Row→ℂ)(weight:Row→ℝ)
    (hw:∀r∈rows,0≤weight r)(hb:∀r∈rows,0≤b r)
    (hb₁:∀r∈rows,(s r).b₁≤b r)(hb₂:∀r∈rows,(s r).b₂≤b r)
    (hd:GoodPair (newtonDivisorPair S A))
    (M:Ideal O)[NeZero M][Finite (O⧸M)](H:Subgroup (O⧸M)ˣ)
    (hH:RayOrthogonality.globalUnits M≤H)(Z Bmask bΦ:ℝ)
    (st:Row→NaturalState Z Bmask bΦ)(η₀:Character)
    (hQM:∀r,(st r).fixedModulus≤M)(hQη:∀r,(st r).fixedModulus≤η₀.modulus)
    (keep:∀r,(st r).radial.keep (z r))
    (hsupport:∀r,(st r).radial.profile (‖eisEmbedding (z r)‖^2/(st r).radial.scale)≠0)
    (e T q:ℝ)(he:0<e)(hT:2<T)(hq:1/2≤q)
    (hβlo:51/100≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8):
    let energy:=fun r=>‖newtonCofactorPlain (s r) (A₁ r) (A₂ r) (R r) (b r) S A
      (τ r) (height r) (z r)*slots r‖^2*weight r
    let corner:=fun side r=>positiveNewtonCofactorPlain side (s r) (A₁ r) (A₂ r) (R r) (b r) S A
      (τ r) (height r) (z r)*slots r
    ∃select:Row→BufferIndex e,
      (∀r,RetainedZeroBin M H hH (st r) η₀ (hQM r) (hQη r) (z r) (keep r) e T (select r)) ∧
    let lowRows:=rows.filter (fun r=>bufferValue e (select r)<(q+1)/2)
    let highBins:=Finset.univ.filter (fun p:BufferIndex e=>(q+1)/2≤bufferValue e p)
    (∀r∈lowRows,ActualLow M H hH (st r) η₀ (hQM r) (hQη r) ((q+1)/2) e
      (3*((select r).1.val+1:ℕ)*T) (z r)) ∧
    (∀p∈highBins,∀r∈rows.filter (fun r=>select r=p),
      3/4≤bufferValue e p ∧ bufferValue e p≤7/8 ∧ q≤2*bufferValue e p-1 ∧
      2*bufferValue e p-1≤3/4 ∧ 2*bufferValue e p-1≤2*HeckeZeroSupremum.beta-1) ∧
    ∀Elow Ehigh:ℝ,
      (∀side:Bool,(∑r∈lowRows.filter (fun r=>corner side r≠0),‖corner side r‖^2*weight r)≤Elow)→
      (∀p∈highBins,(∑r∈rows.filter (fun r=>select r=p),energy r)≤Ehigh)→
      (∑r∈rows,energy r)≤4*Elow+(highBins.card:ℝ)*Ehigh := by
  intro energy corner
  have hex (r:Row):∃p:BufferIndex e,RetainedZeroBin M H hH (st r) η₀
      (hQM r) (hQη r) (z r) (keep r) e T p:=
    actual_retained_zero_partition M H hH (st r) η₀ (hQM r) (hQη r) (z r) (keep r)
      e T he hT hβlo hβhi
  choose select hselect using hex
  refine ⟨select,hselect,?_⟩
  intro lowRows highBins
  refine ⟨?_,?_,?_⟩
  · intro r hr
    exact retained_zero_bin_low M H hH (st r) η₀ (hQM r) (hQη r) (z r) (keep r)
      e T q (select r) (hselect r) (Finset.mem_filter.mp hr).2 (hsupport r)
  · intro p hp r hr
    have hp':(q+1)/2≤bufferValue e (select r):=by
      rw [(Finset.mem_filter.mp hr).2]
      exact (Finset.mem_filter.mp hp).2
    simpa only [(Finset.mem_filter.mp hr).2] using
      retained_zero_bin_high M H hH (st r) η₀ (hQM r) (hQη r) (z r) (keep r)
        e T q (select r) (hselect r) hq hp'
  · intro Elow Ehigh hlow hhigh
    have hl:(∑r∈lowRows,energy r)≤4*Elow:=by
      have h:=centered_newton_positive_corner_family lowRows ι s A₁ A₂ R b S A τ height z slots weight
        (fun r hr=>hw r (Finset.mem_filter.mp hr).1)
        (fun r hr=>hb r (Finset.mem_filter.mp hr).1)
        (fun r hr=>hb₁ r (Finset.mem_filter.mp hr).1)
        (fun r hr=>hb₂ r (Finset.mem_filter.mp hr).1) hd
      exact h.trans (by linarith only [hlow false,hlow true])
    let highRows:=rows.filter (fun r=>(q+1)/2≤bufferValue e (select r))
    have he:(∑r∈highRows,energy r)=∑p∈highBins,∑r∈rows.filter (fun r=>select r=p),energy r:=by
      rw [←Finset.sum_fiberwise_of_maps_to
        (s:=highRows) (t:=highBins) (g:=select)
        (fun r hr=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2⟩) energy]
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      ext r
      simp only [highRows,Finset.mem_filter]
      constructor
      · rintro ⟨⟨hr,_⟩,he⟩;exact ⟨hr,he⟩
      · rintro ⟨hr,he⟩
        exact ⟨⟨hr,by rw [he];exact (Finset.mem_filter.mp hp).2⟩,he⟩
    have hh:(∑r∈highRows,energy r)≤(highBins.card:ℝ)*Ehigh:=by
      rw [he]
      calc
        _≤∑p∈highBins,Ehigh:=Finset.sum_le_sum hhigh
        _=_:=by simp
    have heq:(∑r∈rows,energy r)=(∑r∈lowRows,energy r)+(∑r∈highRows,energy r):=by
      simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not
        (s:=rows) (p:=fun r=>bufferValue e (select r)<(q+1)/2) (f:=energy)).symm
    rw [heq]
    exact add_le_add hl hh
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_buffered_cofactor_partition
