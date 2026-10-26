import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLowFamily
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighAdmission
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLow
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option quotPrecheck false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSourceLiveColumn CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily
open Cycle63FinalLow CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocatedRayDictionary CenteredMomentCommonHeightEnvelope CenteredMomentCommonRawScale
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance geometryLowAdmissionDecidableEq : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- Both allocations are literal; the first coordinate retains its live column. -/
def geometryLowChain (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ)) (t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q).pools E₂) :
    Chain s :=
  {C₁:=geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val,
    R₁:=R,B₁:=q.2,
    η₁:=geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val,t₁:=t,
    E₂:=E₂,R₂:=R₂,B₂:=B₂}

abbrev GeometryLowSecondIndex (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin) :=
  ActualSecondBlockIndex
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) q.1.val.2.1.val
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)) Z ξ

/-- The second datum comes from the actual retained-energy expansion, with
its original character family, rows and physical cutoff. -/
def geometryLowSecondDatum (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q) :
    SecondInputDatum α :=
  actualSecondBlockDatum (liveIndices q.2.val)
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin) (fun _=>logAnnulus) q.1.val q.1.property)
    hw₁ hw₂
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)) Z ξ
    (first_main_radius_pos reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) _) n

section Actual
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
  (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
  (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
local notation "datum" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
local notation "src" => geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
local notation "firstIdeal" => geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val

/-- The selected second ideal and puncture are the literal block fields. -/
def geometryLowActualChain (second : Bool)
    (B₂ : actualAllocations (src).pools (if second then (datum).D else (datum).C)) : Chain s :=
  geometryLowChain reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    bin t q (if second then (datum).D else (datum).C) (datum).R B₂

/-- Admission uses an actual live row once for geometry; it does not select
an allocation separately at each frequency in the low energy sum. -/
def geometryLowActualGeometry (second : Bool)
    (B₂ : actualAllocations (src).pools (if second then (datum).D else (datum).C))
    (r : secondLiveRows (fun _:Unit=>(datum).block))
    (hf₁ : frozenCoefficient q.2.val firstIdeal R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val (if second then (datum).D else (datum).C) (datum).R (src).ν (src).W (src).P≠0) :
    LiveMainGeometry s
      (geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂)
      Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b N :=
  actualGeometryLow reflected s
    (geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂)
    R seed Z Mrow amp ξ reserve b N hZ bin q.1.val rfl rfl datum r rfl rfl
    (by
      cases second
      · exact Or.inl rfl
      · exact Or.inr rfl) hf₁ hf₂

theorem actual_geometry_low_admission_fields (second : Bool)
    (B₂ : actualAllocations (src).pools (if second then (datum).D else (datum).C))
    (r : secondLiveRows (fun _:Unit=>(datum).block))
    (hf₁ : frozenCoefficient q.2.val firstIdeal R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val (if second then (datum).D else (datum).C) (datum).R (src).ν (src).W (src).P≠0) :
    let chain:=geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
    let g:=geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂ r hf₁ hf₂
    chain.C₁=firstIdeal ∧ chain.R₁=R ∧ HEq chain.B₁ q.2 ∧
      chain.η₁=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val ∧
      chain.t₁=t ∧ chain.first=src ∧
      g.reflected=reflected ∧
      g.C₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1).C ∧
      g.D₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1).D ∧
      HEq g.E₀ (geometryFirstSource s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1).inactive ∧
      g.datum=datum ∧ g.row=r ∧
      g.datum.radius=frequencyRadius
        (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
          (geometryFirstLabel s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)) Z ξ :=
  ⟨rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩

lemma actual_geometry_low_second_puncture (hR : R≠0) (second : Bool) :
    (datum).R*(if second then (datum).D else (datum).C)≠0 := by
  have hp : (datum).R≠0 := actual_geometry_child_puncture_ne_zero reflected s R seed hR
    (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  apply mul_ne_zero hp
  cases second
  · exact (datum).hC.1
  · exact (datum).hD.1

end Actual

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
