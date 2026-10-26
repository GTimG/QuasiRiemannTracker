import Candidate.Cycle63.Physical.InitialMass.GeometryLowFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryHighAdmission
import Candidate.Cycle63.Physical.InitialMass.SecondRetainedAssembly

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryLowAdmission. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option quotPrecheck false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSourceLiveColumn CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily
open Cycle63FinalLow CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocatedRayDictionary CenteredMomentCommonHeightEnvelope CenteredMomentCommonRawScale
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

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

omit [DecidableEq α] in
theorem actual_geometry_low_chain_fields (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ)) (t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q).pools E₂) :
    let chain:=geometryLowChain reflected s R seed K Z ξ hK bin t q E₂ R₂ B₂
    chain.C₁=geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val ∧
      chain.R₁=R ∧ HEq chain.B₁ q.2 ∧
      chain.η₁=geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val ∧
      chain.t₁=t ∧ chain.first=geometryLowFirstChild reflected s R seed K Z ξ hK bin t q :=
  ⟨rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩

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

/-- The constructor's literal first child inherits Matches, original plain
profiles, both plain caps and the fixed two-allocation control. -/
theorem actual_geometry_low_chain_profile_admission
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
    (N : ℕ)(Cs bs : ℝ)(hCs : 1≤Cs)(hbs : 1≤bs)
    (s : Input α)(hcard : Fintype.card α≤N)(hM : ∀j,s.M j≤Cs)
    (hb₁ : s.b₁≤bs)(hb₂ : s.b₂≤bs)
    (η₀ : Character)(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)
    (W : ℝ→ℂ)(B₀ Z cap : ℝ)(hm : Matches M H hH s η₀ θ w σ v W B₀ Z)
    {ap bp : ℝ}(p : Profiles ap bp)
    (hW₁ : s.W₁=(p.profile 0:ℝ→ℂ))(hW₂ : s.W₂=(p.profile 1:ℝ→ℂ))
    (hb₁p : s.b₁=bp)(hb₂p : s.b₂=bp)
    (hscale : ∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap)
    (reflected : Bool)(R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (E₂ R₂ : Ideal O)(B₂ : actualAllocations
      (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q).pools E₂) :
    let chain:=geometryLowChain reflected s R seed K Z ξ hK bin t q E₂ R₂ B₂
    Matches M H hH chain.first η₀ (fun j=>θ j.val) (fun j=>w j.val) (fun j=>σ j.val)
      (fun j=>v j.val) W B₀ Z ∧
      chain.first.W₁=(p.profile 0:ℝ→ℂ) ∧ chain.first.W₂=(p.profile 1:ℝ→ℂ) ∧
      chain.first.b₁=bp ∧ chain.first.b₂=bp ∧
      (∀second j,Cycle63.Physical.sourcePlainScales chain.first.toData.toSource second j≤Z^cap) ∧
      ∀(χ : Character)(height : ℝ),
        Cycle63HighResidual.wholeControl (chain.final χ height)≤2*bs*Cs^N := by
  intro chain
  obtain ⟨hmatch,hp₁,hp₂,hb₁',hb₂',hcaps,hcontrol⟩ := actual_geometry_child_profile_admission
    M H hH N Cs bs hCs hbs s hcard hM hb₁ hb₂ η₀ θ w σ v W B₀ Z cap hm p
    hW₁ hW₂ hb₁p hb₂p hscale reflected R seed K ξ hK bin q.1.val q.2 t
  exact ⟨hmatch,hp₁,hp₂,hb₁',hb₂',hcaps,fun χ height=>hcontrol E₂ R₂ B₂ χ height⟩


end
end OAI.SevenEighths.Cycle63InitialMass

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometryLowChain
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_low_chain_fields
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometryLowSecondDatum
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometryLowActualChain
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometryLowActualGeometry
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_low_admission_fields
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_low_second_puncture
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_low_chain_profile_admission
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryLowColumn. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
local notation "O" => HeckeFamily.O
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _



/-- The first projector divides both ideals in the literal second block. -/
theorem actual_geometry_low_column_seed (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
    d.seed∣d.C ∧ d.seed∣d.D := by
  exact (actual_retained_block_gates (liveIndices q.2.val)
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
      (zero_lt_one.trans hZ) _) n) |>.imp_right (fun h=>h.1)

section Column
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
set_option quotPrecheck false in
local notation "d" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
set_option quotPrecheck false in
local notation "firstChild" => geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
variable (second : Bool)
/-- A literal child identification rewrites the complete low column sum.
It leaves the common allocation fixed and imposes no energy hypothesis. -/
theorem actual_geometry_low_column_sum (χ : RayFourExpansion.RayCharacter) (v : ℝ)
    (actualChild : Input (liveIndices q.2.val))
    (hchild : actualChild=withHeight firstChild ((d).τ χ) v)
    (Ds : Finset (Ideal O)) (zs : Finset O) (weight : O→ℝ)
    (hE : Supported (if second then (d).D else (d).C)) :
    (∑D∈Ds,∑z∈zs,weight z*
      ‖normalizedColumn actualChild (if second then (d).D else (d).C) hE (d).R (d).seed D z‖^2)=
    (∑D∈Ds,∑z∈zs,weight z*
      ‖normalizedColumn (withHeight firstChild ((d).τ χ) v)
        (if second then (d).D else (d).C) hE (d).R (d).seed D z‖^2) := by
  rw [hchild]


end Column
end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_low_column_seed
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_low_column_sum
end
