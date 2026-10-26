/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual marked balanced first budget enters corrected MAIN with all labels,
actual allocation counts and original frozen coefficients retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBalancedMain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstAllocationSelectionColumns
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalAllocationMain
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentFirstAnnularMajorant CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstAmplificationChoice
open CenteredMomentPrimePool CenteredMomentLogDyadic Cycle61InitialMass
open Record1252270103Source.Collision GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.FirstAllocationSelection
open Filter
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

set_option linter.constructorNameAsVariable false in
/-- Complete-cost column selection is performed before choosing an actual
first allocation. The original MAIN Cauchy card and the maximizing card both
remain, and the arithmetic first key is genuinely injective. -/
theorem actual_selected_marked_main (Amax Dmax Bsource ξ ε : ℝ)
    (hAmax : 0≤Amax)(hDmax : 0≤Dmax)(hBsource : 0≤Bsource)(hξ : 0≤ξ)(hε : 0<ε) :
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(reflected : Bool) (s : Input ι) (A₁ A₂ D Kmark R seed : Ideal O)
      (F : Ideal O→ℂ) (K M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ)),
    Squarefree seed→s.W₁ 0=0→s.W₂ 0=0→
    0<sourceRadius s→sourceRadius s≤Z^Bsource→volume s≤Z^Amax→K⁻¹≤Z^Dmax→
    ∀(weight : SourceCoordinate s (markedSourceModifier A₁ A₂ D Kmark F) R seed K Z ξ→ℂ)
      (t ell upper Bcap : ℝ)
      (P : Finset (Ideal O)), P.Nonempty→
    (∀Q∈P,Prime Q)→(∀Q∈P,Q∉fixedBadPrimes)→
    (∀Q∈P,∀i,∀J∈s.pools (Sum.inl i),¬Q∣J)→
    0<ell→(∀Q∈P,Z^ell≤(Q.absNorm:ℝ))→
    (∀Q∈P,(Q.absNorm:ℝ)≤Z^upper)→2*(Bcap/ell)≤(P.card:ℝ)→
    let modifier:=markedSourceModifier A₁ A₂ D Kmark F
    let src:=geometryFirstSource s modifier R seed K Z ξ hK key
    let C:=geometryColumnIdeal reflected s modifier R seed K Z ξ hK key
    let τ:=geometryColumnCharacter reflected s modifier R seed K Z ξ hK key
    ∀radius : FirstColumnIndex src→ℝ,
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),0≤radius j+6*upper)→
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),∀n∈bands (src j.1).H0,
      dyadicScale n≤Z^(radius j))→
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),∀B:actualAllocations s.pools (C j),
      frozenCoefficient B.val (C j) R s.ν s.W s.P≠0→
      sourceRadius (child s (C j) R B (τ j) t)≤Z^Bcap)→
    let cost:=fun j (B:actualAllocations s.pools (C j))=>(P.card:ℝ)⁻¹*((radius j+6*upper)/ell)*
      correctedChildGaussEnergy s A₁ A₂ D Kmark (C j) R j.2.1.val F P B
        (τ j) t (volume s) (Z^(radius j+6*upper))
    let total:=fun j=>∑B:actualAllocations s.pools (C j),‖frozenCoefficient B.val (C j) R s.ν s.W s.P‖^2*cost j B
    let outer:=fun j=>‖balancedColumnScalar reflected s modifier R seed K Z ξ M A hK key weight j‖^2*
      ((bands (src j.1).H0).card:ℝ)*((actualAllocations s.pools (C j)).card:ℝ)
    let live:=(firstLiveColumns src (fun _=>logAnnulus)).filter (fun j=>total j≠0)
    let arith:=fun j:live=>columnKey s modifier R seed K Z ξ hK key j.val
    ∃column:(k:Finset.univ.image arith)→live,
      (∀k,arith (column k)=k.val) ∧ Function.Injective (fun k=>arith (column k)) ∧
    ∃alloc:∀k:Finset.univ.image arith,actualAllocations s.pools (C (column k)),
      (∀k,frozenCoefficient (alloc k).val (C (column k)) R s.ν s.W s.P≠0 ∧ 0<cost (column k) (alloc k)) ∧
      balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key weight t≤
        (C₀*Z^ε)*∑k:Finset.univ.image arith,outer (column k)*
          ((actualAllocations s.pools (C (column k))).card:ℝ)*
          ‖frozenCoefficient (alloc k).val (C (column k)) R s.ν s.W s.P‖^2*cost (column k) (alloc k) := by
  classical
  obtain ⟨C₀,hC₀,hselect⟩:=actual_first_full_cost_selection Amax Dmax Bsource ξ ε hAmax hDmax hBsource hξ hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hselect,eventually_gt_atTop (1:ℝ)] with Z hs hZ
  refine ⟨hZ,?_⟩
  intro reflected s A₁ A₂ D Kmark R seed F K M A hK key hseed hz₁ hz₂ hpos hsource hvolume hKi
    weight t ell upper Bcap P hP hp hbad hmarked hell hlower hupper hsize modifier src C τ
    radius hscale hband hchild cost total outer live arith
  have hcost (j:FirstColumnIndex src)(hj:j∈firstLiveColumns src (fun _=>logAnnulus))
      (B:actualAllocations s.pools (C j)):0≤cost j B := by
    have he:0≤correctedChildGaussEnergy s A₁ A₂ D Kmark (C j) R j.2.1.val F P B
        (τ j) t (volume s) (Z^(radius j+6*upper)) := by
      unfold correctedChildGaussEnergy
      exact gaussEnergy_ball_nonneg _ _ _ _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (div_nonneg (hscale j hj) hell.le)) he
  have houter (j:FirstColumnIndex src):0≤outer j := by dsimp only [outer];positivity
  have htotal (j:FirstColumnIndex src)(hj:j∈firstLiveColumns src (fun _=>logAnnulus)):0≤total j :=
    Finset.sum_nonneg (fun B _=>mul_nonneg (sq_nonneg _) (hcost j hj B))
  obtain ⟨column,hkey,hinj,hcolumns⟩:=hs.2 s modifier R seed K hK key hseed hz₁ hz₂ hpos hsource hvolume hKi
    live (fun j=>outer j*total j)
    (fun j=>mul_nonneg (houter j) (htotal j (Finset.mem_filter.mp j.property).1))
  have hex (k:Finset.univ.image arith):=
    weighted_full_cost_max (fun B:actualAllocations s.pools (C (column k))=>
      frozenCoefficient B.val (C (column k)) R s.ν s.W s.P)
      (cost (column k)) (hcost (column k) (Finset.mem_filter.mp (column k).property).1)
      (Finset.mem_filter.mp (column k).property).2
  choose alloc hf hc hmax hbound using hex
  refine ⟨column,hkey,hinj,alloc,(fun k=>⟨hf k,hc k⟩),?_⟩
  have hm:=actual_balanced_marked_main reflected s A₁ A₂ D Kmark R seed F K Z ξ M A hK key weight
    t ell upper Bcap P hP hp hbad hmarked hZ hell hlower hupper hsize hz₁ hz₂ radius hscale hband hchild
  have he:(∑j∈firstLiveColumns src (fun _=>logAnnulus),outer j*total j)=∑j:live,outer j*total j := by
    rw [Finset.sum_coe_sort live (fun j=>outer j*total j)]
    simp only [live,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h:total j=0 <;> simp [h]
  have hm':balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key weight t≤∑j:live,outer j*total j := by
    rw [←he]
    apply hm.trans_eq
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [outer,total,cost,modifier,src,C,τ]
    simp only [mul_assoc]
  apply (hm'.trans hcolumns).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₀.le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  apply Finset.sum_le_sum
  intro k hk
  have hb:total (column k)≤((actualAllocations s.pools (C (column k))).card:ℝ)*
      (‖frozenCoefficient (alloc k).val (C (column k)) R s.ν s.W s.P‖^2*cost (column k) (alloc k)):=by
    simpa only [weightedTotal,total,Fintype.card_coe] using hbound k
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (houter (column k))

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_selected_marked_main
