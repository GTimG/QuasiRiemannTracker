import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryAdmission
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondEnvelopeBudget
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.FinalRadius

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily Cycle61Moment CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationChildInput
open CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- First-stage arithmetic label after fixing the dyad/geometry bin. -/
def geometryFirstLabel {ι : Type*} [Fintype ι] (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : FirstSourceLabel :=
  ⟨j.1.val.1.val,j.1.val.2.1⟩

/-- Recording the arithmetic label and four dyads recovers the entire
original first-source coordinate, including its dependent interval data. -/
theorem first_coordinate_code_injective {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) :
    Function.Injective (fun q : FirstSourceCoordinate s R seed K Z ξ=>
      ((⟨q.1.val,q.2.1⟩ : FirstSourceLabel),fun i=>(q.2.2 i:ℤ))) := by
  rintro ⟨p,E,n⟩ ⟨p',E',n'⟩ h
  have hp : p.val=p'.val := congrArg (fun x=>x.1.1) h
  have hp' : p=p' := Subtype.ext hp
  cases hp'
  have hE : E=E' := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst h)).2
  cases hE
  have hn : n=n' := funext (fun i=>Subtype.ext (congrFun (congrArg Prod.snd h) i))
  cases hn
  rfl

/-- The first projector alone does not identify a source column: its four
first-stage dyads and two ray characters must also be retained or selected. -/
theorem geometry_first_column_code_injective {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ)) :
    Function.Injective (fun j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)=>
      (geometryFirstLabel s R seed K Z ξ hK key j,j.2.1.val,
        (fun i=>(j.1.val.2.2 i:ℤ)),j.2.2.1,j.2.2.2)) := by
  rintro ⟨q,L,χ,ψ⟩ ⟨q',L',χ',ψ'⟩ h
  have hq : q=q' := by
    apply Subtype.ext
    apply first_coordinate_code_injective s R seed K Z ξ
    change ((⟨q.val.1.val,q.val.2.1⟩ : FirstSourceLabel),fun i=>(q.val.2.2 i:ℤ))=
      ((⟨q'.val.1.val,q'.val.2.1⟩ : FirstSourceLabel),fun i=>(q'.val.2.2 i:ℤ))
    exact congrArg (fun x=>(x.1,x.2.2.1)) h
  cases hq
  have hL : L=L' := Subtype.ext (congrArg (fun x=>x.2.1) h)
  cases hL
  have hχ : χ=χ' := congrArg (fun x=>x.2.2.2.1) h
  have hψ : ψ=ψ' := congrArg (fun x=>x.2.2.2.2) h
  cases hχ
  cases hψ
  rfl

def firstMainRadius (reflected : Bool) (K V Z ξ sigma reserve : ℝ)
    (l : FirstSourceLabel) : ℝ :=
  mainCommonRadius Z (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
    (nominalLog l.1.1 l.1.2
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val}) K V Z)
    (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) sigma
    (frequencyLoss Z 32 ξ) reserve

def firstMainFourierScale (reflected : Bool) (K V Z ξ sigma reserve b : ℝ) (N : ℕ)
    (l : FirstSourceLabel) : ℝ :=
  (b^N*V/((if reflected then l.1.2 else l.1.1).absNorm:ℝ))^2/
    firstMainRadius reflected K V Z ξ sigma reserve l

theorem first_main_radius_pos (reflected : Bool) (K V Z ξ sigma reserve : ℝ)
    (hZ : 0<Z) (l : FirstSourceLabel) : 0<firstMainRadius reflected K V Z ξ sigma reserve l := by
  unfold firstMainRadius mainCommonRadius
  positivity

/-- The literal main source has a radius depending only on the first
arithmetic label, not the first projector or either common allocation. -/
theorem actual_geometry_main_source_radius {ι : Type*} [Fintype ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K Z ξ sigma reserve : ℝ)
    (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))
    (t : ℝ) :
    actualMainSource
      (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R B
        (geometryColumnCharacter reflected s R seed K Z ξ hK key j) t)
      (geometryBranch reflected s R seed K Z ξ hK key j) Z sigma 1 ξ reserve =
    normalizedGaussSource
      (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R B
        (geometryColumnCharacter reflected s R seed K Z ξ hK key j) t)
      (R*geometryColumnIdeal reflected s R seed K Z ξ hK key j) j.2.1.val ballProfile
      (firstMainRadius reflected K (volume s) Z ξ sigma reserve
        (geometryFirstLabel s R seed K Z ξ hK key j)) := by
  simp only [actualMainSource,geometryBranch,firstMainRadius,geometryFirstLabel,mul_one]
  rfl

/-- A declared Fourier scale depending only on that same label dominates
the actual common child's squared volume divided by its main radius. -/
theorem actual_geometry_main_fourier_admissible {ι : Type*} [Fintype ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K Z ξ sigma reserve b : ℝ)
    (N : ℕ) (hK : 0<K) (hZ : 0<Z) (hb : 1≤b) (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))
    (t : ℝ)
    (hne : frozenCoefficient B.val (geometryColumnIdeal reflected s R seed K Z ξ hK key j)
      R s.ν s.W s.P≠0) :
    let l := geometryFirstLabel s R seed K Z ξ hK key j
    (volume (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R B
      (geometryColumnCharacter reflected s R seed K Z ξ hK key j) t))^2/
        firstMainRadius reflected K (volume s) Z ξ sigma reserve l≤
      firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N l := by
  dsimp only
  exact Cycle61FinalRadius.actual_second_radius_admissible N b hb s hcard hs _ R B _ t _
    (first_main_radius_pos reflected K (volume s) Z ξ sigma reserve hZ _) hne

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_main_radius_pos
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_source_radius
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_fourier_admissible

#print axioms OAI.SevenEighths.Cycle61InitialMass.first_coordinate_code_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_first_column_code_injective
