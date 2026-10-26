/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Both complete allocation counts are paid from the actual squarefree-column
radical reserve before summing the original second common labels and dyads. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalRadicalPhysical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.Projector
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockRadicalHarmonicMass

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount CenteredMomentSourceRow
open CenteredMomentSourceMass
open CenteredMomentSecondRetainedAggregate
open Record1252270103CommonGeometry
local notation "O" => ActualEisensteinCubic.O

theorem common_norm_fourth_radical (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (hc : ∀P : CommonIndex C D,leftExponent C D P≤2)
    (hd : ∀P : CommonIndex C D,rightExponent C D P≤2) :
    (C.absNorm:ℝ)*(D.absNorm:ℝ)≤(Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^4 := by
  have hleft:=congrArg (fun I:Ideal O=>(I.absNorm:ℝ)) (left_ideal_product C D hC hCD)
  have hright:=congrArg (fun I:Ideal O=>(I.absNorm:ℝ)) (right_ideal_product C D hC hD hCD)
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow,commonPrime_span C D hC] at hleft hright
  rw [←hleft,←hright,←Finset.prod_mul_distrib,map_prod,Nat.cast_prod,←Finset.prod_pow]
  apply Finset.prod_le_prod₀ (fun P _=>by positivity)
  intro P hP
  rw [←pow_add]
  apply pow_le_pow_right₀
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1)
  · have hcl:=hc P
    have hdr:=hd P
    omega

theorem bounded_column_norm_fourth_radical (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (hc : ValuationAtMostTwo C) (hd : ValuationAtMostTwo D) :
    (C.absNorm:ℝ)*(D.absNorm:ℝ)≤(Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^4 := by
  apply common_norm_fourth_radical C D hC hD hCD
  · intro P
    exact hc P.val (UniqueFactorizationMonoid.prime_of_normalized_factor P.val
      (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))
  · intro P
    exact hd P.val (UniqueFactorizationMonoid.prime_of_normalized_factor P.val
      (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))

theorem actual_allocation_radical_payment (N : ℕ) :
    ∃A : ℝ,0<A ∧ ∀{ι : Type*}[Fintype ι],Fintype.card ι≤N→
      ∀s : Input ι,∀C D : Ideal O,∀hC : Supported C,∀hD : Supported D,
      primeSupport C=primeSupport D→ValuationAtMostTwo C→ValuationAtMostTwo D→
      ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
        (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(2*(499/1000:ℝ)-2)≤
        A/(Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ) := by
  obtain ⟨A,hA,hcard⟩:=CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (1/10000) (by norm_num)
  refine ⟨A^2,by positivity,?_⟩
  intro ι inst hι s C D hC hD hCD hc hd
  have hn : Fintype.card (ι⊕Fin 2)≤N+2 := by
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  have hNC : (0:ℝ)<C.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hND : (0:ℝ)<D.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hR : (1:ℝ)≤Ideal.absNorm (∏P : CommonIndex C D,P.val) := by
    have hh:=CenteredMomentSecondPhysicalLedger.common_product_pos C D hC Finset.univ
    exact_mod_cast (show 1≤Ideal.absNorm (∏P : CommonIndex C D,P.val) by exact_mod_cast hh)
  have hp:=mul_le_mul (hcard hn s.pools C hC.1) (hcard hn s.pools D hD.1)
    (Nat.cast_nonneg _) (by positivity)
  have hp' : ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)≤
      A^2*((C.absNorm:ℝ)*(D.absNorm:ℝ))^(1/10000:ℝ) := by
    rw [Real.mul_rpow hNC.le hND.le]
    convert hp using 1 <;> ring
  apply (mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg (zero_le_one.trans hR) _)).trans
  exact allocation_radical_payment _ _ (A^2) (499/1000) (1/10000) hR
    (mul_nonneg hNC.le hND.le) (sq_nonneg _) (by norm_num)
    (bounded_column_norm_fourth_radical C D hC hD hCD hc hd) selected_allocation_margin

/-- All original second common labels, inactive subsets and dyadic blocks
are summed. Both full allocation cardinalities stay inside the sum until
the preceding radical estimate pays them. -/
theorem actual_allocation_block_radical_mass (N : ℕ) (B L Cr ε : ℝ)
    (hB : 0≤B) (hL : 0≤L) (hCr : 0<Cr) (hε : 0<ε) :
    ∃A : ℝ,0<A ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      ∀{ι : Type*}[Fintype ι],Fintype.card ι≤N→∀s : Input ι,
      ∀seed : Ideal O,Squarefree seed→seed≠0→
      ∀(S : Finset (Ideal O))(β : Ideal O→ℂ),
      (∀I∈S,β I≠0→seed∣I)→
      (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B)→
      (∀p : ActiveLabel S β,ValuationAtMostTwo p.val.1 ∧ ValuationAtMostTwo p.val.2)→
      ∀K R H : ℝ,0<K→R≤Cr*Z^L→H≤Z^B→
      (∑q : ActiveBlocks S β K R H,
        ((actualAllocations s.pools q.1.1.val.1).card:ℝ)*
        ((actualAllocations s.pools q.1.1.val.2).card:ℝ)*
        (Ideal.absNorm (∏P : CommonIndex q.1.1.val.1 q.1.1.val.2,P.val):ℝ)^
          (2*(499/1000:ℝ)-2))≤A*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨A,hA,hcard⟩:=actual_allocation_radical_payment N
  obtain ⟨C,hC,hmass⟩:=actual_block_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨A*C,mul_pos hA hC,?_⟩
  filter_upwards [hmass] with Z hz
  intro ι inst hι s seed hseed hs0 S β hseedcol hcap hval K R H hK hR hH
  have hp (q : ActiveBlocks S β K R H) :
      ((actualAllocations s.pools q.1.1.val.1).card:ℝ)*
        ((actualAllocations s.pools q.1.1.val.2).card:ℝ)*
        (Ideal.absNorm (∏P : CommonIndex q.1.1.val.1 q.1.1.val.2,P.val):ℝ)^
          (2*(499/1000:ℝ)-2)≤A*radicalWeight q.1.1.val.1 q.1.1.val.2 := by
    have hs:=commonLabels_supported (activeSource S β) _ _ q.1.1.property
    have heq:=(commonLabels_data (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β)) _ _ q.1.1.property).2.2
    have hh:=hcard hι s q.1.1.val.1 q.1.1.val.2 hs.1 hs.2 heq (hval q.1.1).1 (hval q.1.1).2
    have he : (∏P : CommonIndex q.1.1.val.1 q.1.1.val.2,P.val)=
        CenteredMomentRankinRadical.commonRadical q.1.1.val.1 q.1.1.val.2 := by
      exact Finset.prod_coe_sort (s:=CenteredMomentCompleteCommon.commonSupport
        q.1.1.val.1 q.1.1.val.2) (f:=fun I:Ideal O=>I)
    simpa only [he,radicalWeight,div_eq_mul_inv,one_mul] using hh
  calc
    _≤∑q : ActiveBlocks S β K R H,A*radicalWeight q.1.1.val.1 q.1.1.val.2 :=
      Finset.sum_le_sum (fun q _=>hp q)
    _=A*(∑q : ActiveBlocks S β K R H,radicalWeight q.1.1.val.1 q.1.1.val.2) := by
      rw [Finset.mul_sum]
    _≤A*(C*Z^ε/(seed.absNorm:ℝ)) := mul_le_mul_of_nonneg_left
      (hz seed hseed hs0 S β hseedcol hcap K R H hK hR hH) hA.le
    _=(A*C)*Z^ε/(seed.absNorm:ℝ) := by ring

end
end OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.common_norm_fourth_radical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.bounded_column_norm_fourth_radical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.actual_allocation_radical_payment
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.actual_allocation_block_radical_mass
