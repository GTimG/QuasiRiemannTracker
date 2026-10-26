/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual first MAIN selection returns one injective arithmetic family.
Both allocation cards, the original scalar and frozen coefficient remain. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedMain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedContract

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstAnnularMajorant CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentPrimePool CenteredMomentLogDyadic Cycle61InitialMass
open CenteredMomentCanonicalFirst
open CenteredMomentOriginalCommonHarmonic Cycle61Moment
open High.CoupledFirst High.GlobalPhysical Admission.FirstFamily
open Admission.FirstAllocationSelection ExceptionalPrice
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
local notation "source"=>High.CoupledFirst.geometryFirstSource
local instance initialMainSelectionDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

theorem eventual_selected_main {α:Type}[Fintype α] (ξ ε:ℝ)(hξ:0≤ξ)(hε:0<ε):
    ∃Csel:ℝ,0<Csel ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀(s:Input α)(R:Ideal O),
    s.W₁ 0=0→s.W₂ 0=0→0<sourceRadius s→sourceRadius s≤Z^(2:ℝ)→volume s≤Z→
    ∀(W:𝓢(ℝ,ℂ))(ht ell amp reserve:ℝ)(P:Finset (Ideal O)),
    P.Nonempty→(∀p∈P,Prime p)→(∀p∈P,p∉fixedBadPrimes)→
    (∀p∈P,∀i,∀J∈s.pools (Sum.inl i),¬p∣J)→
    0<ell→(∀p∈P,Z^ell≤(p.absNorm:ℝ))→(∀p∈P,(p.absNorm:ℝ)≤Z^amp)→
    2*((2:ℝ)/ell)≤(P.card:ℝ)→
    let modifier:=markedSourceModifier 1 1 1 1 (fun _=>1)
    ∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ)),
    let src:=source s modifier R 1 Z Z ξ (zero_lt_one.trans hZ) bin
    let common:=columnIdeal reflected s modifier R 1 Z Z ξ (zero_lt_one.trans hZ) bin
    let chars:=columnCharacter reflected s modifier R 1 Z Z ξ (zero_lt_one.trans hZ) bin
    let label:=firstLabel s modifier R 1 Z Z ξ (zero_lt_one.trans hZ) bin
    let radius:=fun j=>literalFirstRadius reflected Z (volume s) Z ξ reserve (label j)
    let Hmain:=fun j=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (label j)
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),0≤radius j+6*amp)→
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),∀n∈bands (src j.1).H0,dyadicScale n≤Z^(radius j))→
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),∀B:actualAllocations s.pools (common j),
      frozenCoefficient B.val (common j) R s.ν s.W s.P≠0→
      sourceRadius (CenteredMomentAmplificationChildInput.child s (common j) R B (chars j) ht)≤Z^(2:ℝ))→
    let scalar:=balancedColumnScalar reflected s modifier R 1 Z Z ξ 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) bin (fun q=>normPhase (coordinateBlock s modifier R 1 W Z Z ξ q))
    ∃labels:Finset (FirstSourceLabel×Ideal O),∃column:labels→FirstColumnIndex src,
      Function.Injective (fun l=>(label (column l),(column l).2.1.val)) ∧
      (∀l,column l∈firstLiveColumns src (fun _=>logAnnulus)) ∧
    ∃alloc:∀l,actualAllocations s.pools (common (column l)),
      (∀l,frozenCoefficient (alloc l).val (common (column l)) R s.ν s.W s.P≠0) ∧
    let extra:=fun l=>((bands (src (column l).1).H0).card:ℝ)*
      ((actualAllocations s.pools (common (column l))).card:ℝ)^2/(P.card:ℝ)*
        ((radius (column l)+6*amp)/ell)
    let amplitude:=fun l=>‖scalar (column l)‖^2*extra l*
      ‖frozenCoefficient (alloc l).val (common (column l)) R s.ν s.W s.P‖^2
    balancedLiveBudget reflected s modifier R 1 Z Z ξ 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) bin (fun q=>normPhase (coordinateBlock s modifier R 1 W Z Z ξ q)) ht≤
      (Csel*Z^ε)*∑l,amplitude l*correctedChildGaussEnergy s 1 1 1 1
        (common (column l)) R (column l).2.1.val (fun _=>1) P (alloc l) (chars (column l)) ht
        (volume s) (Hmain (column l)) := by
  obtain ⟨Csel,hCsel,hmain⟩:=actual_selected_marked_main (ι:=α) 1 0 2 ξ ε
    (by norm_num) (by norm_num) (by norm_num) hξ hε
  refine ⟨Csel,hCsel,hmain.mono ?_⟩
  intro Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s R hz₁ hz₂ hsource0 hsource hvolume W ht ell amp reserve P hP hp hbad havoid
    hell hlower hupper hsize modifier reflected bin src common chars label radius Hmain hscale hbands hchild scalar
  have hKi:Z⁻¹≤Z^(0:ℝ):=by
    rw [Real.rpow_zero]
    exact inv_le_one_of_one_le₀ hZ.le
  have hv:volume s≤Z^(1:ℝ):=by simpa only [Real.rpow_one] using hvolume
  obtain ⟨column,hkey,hinj,alloc,halloc,hbound⟩:=hz.2 reflected s 1 1 1 1 R 1 (fun _=>1)
    Z 1 (Real.logb Z (volume s)) (zero_lt_one.trans hZ) bin squarefree_one hz₁ hz₂
    hsource0 hsource hv hKi (fun q=>normPhase (coordinateBlock s modifier R 1 W Z Z ξ q))
    ht ell amp 2 P hP hp hbad havoid hell hlower hupper hsize radius hscale hbands hchild
  refine ⟨_,fun l=>(column l).val,hinj,fun l=>(Finset.mem_filter.mp (column l).property).1,
    alloc,fun l=>(halloc l).1,?_⟩
  intro extra amplitude
  apply hbound.trans_eq
  apply congrArg (fun x:ℝ=>(Csel*Z^ε)*x)
  apply Finset.sum_congr rfl
  intro l _
  dsimp only
  rw [literal_first_main_radius]
  dsimp only [extra,amplitude,scalar,Hmain,radius,label,chars,common,modifier,src]
  dsimp only [columnIdeal,columnCharacter,columnPair,High.CoupledFirst.geometryColumnIdeal,High.CoupledFirst.geometryColumnCharacter]
  ring

end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.eventual_selected_main
