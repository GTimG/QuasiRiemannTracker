import Candidate.Cycle62.Physical.InitialMass.GeometryLowFamily
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorSecondSplit
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorCoprime
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorModulus
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorRetained
import Candidate.Cycle62.Physical.FinalError.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstMixedRightTransport
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondCanonical CenteredMomentCompleteCommon
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentChildRows CenteredMomentAmplificationRadicalFamily RayFourExpansion
open CenteredMomentCommonRawScale CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildSourceCaps CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance {β : Type*} : DecidableEq β := Classical.decEq _

section First
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (K Z ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
  (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
local notation "src" => geometryFirstSource s R seed K Z ξ hK bin j.1

def geometryErrorOtherIdeal : Ideal O := if reflected then (src).C else (src).D

/-- Reflection transports the actual subset, preserving its prime labels. -/
def geometryErrorInactive : Finset (CommonIndex
    (geometryColumnIdeal reflected s R seed K Z ξ hK bin j)
    (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j)) :=
  match reflected with
  | false => (src).inactive
  | true => swapSubset (src).C (src).D (src).inactive

omit [DecidableEq α] in
theorem actual_geometry_error_first_support :
    Supported (geometryColumnIdeal reflected s R seed K Z ξ hK bin j) ∧
    Supported (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j) ∧
    primeSupport (geometryColumnIdeal reflected s R seed K Z ξ hK bin j)=
      primeSupport (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j) := by
  cases reflected
  · exact ⟨(src).hC,(src).hD,(src).sameSupport⟩
  · exact ⟨(src).hD,(src).hC,(src).sameSupport.symm⟩

omit [DecidableEq α] in
theorem actual_geometry_error_first_modulus :
    (geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus=
      s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator
        (fun P : CommonIndex (geometryColumnIdeal reflected s R seed K Z ξ hK bin j)
          (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j)=>P.val)
        (geometryErrorInactive reflected s R seed K Z ξ hK bin j)*
          activeConductor (geometryColumnIdeal reflected s R seed K Z ξ hK bin j)
            (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j)} := by
  have hm := actual_geometry_column_modulus reflected s R seed K Z ξ hK bin j
  cases reflected
  · exact hm
  · change _=_*Ideal.span {primeSubsetGenerator (fun P : CommonIndex (src).D (src).C=>P.val)
      (swapSubset (src).C (src).D (src).inactive)*activeConductor (src).D (src).C}
    rw [swapped_modulus_factor]
    exact hm

end First

/-- Full padded-pool coprimality is obtained before extraction. This
gate includes every stored slot, including zero smooth-profile entries. -/
theorem actual_geometry_error_child_coprime
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (s : Input α) (η₀ : Character) (θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z eta ell : ℝ) (hZ : 1≤Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z) (hw : ∀j,w j≤eta)
    (p : O) (hprime : Prime (Ideal.span {p}))
    (hpn : Z^ell≤((Ideal.span {p}).absNorm:ℝ))
    (hgap : max 1 bslot*Z^eta<Z^ell)
    (reflected : Bool) (R seed : Ideal O) (K ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ)) (t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    ∀j I,I∈(geometryLowFirstChild reflected s R seed K Z ξ hK bin t q).slots j→
      IsCoprime (Ideal.span {p}) I :=
  actual_child_full_slot_coprime s (Ideal.span {p})
    (actual_full_slot_coprime M H hH s η₀ θ w σ freq W bslot Z eta ell hZ hm hw
      (Ideal.span {p}) hprime hpn hgap)
    (geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val) R q.2
    (geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val) t

/-- Literal Chain constructor, with the active extracted allocation lifted
once and the final allocation typed in that exact unpruned dictionary. -/
def errorAdmissionChain (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (η : Character) (t : ℝ)
    (p : O) (hp : p≠0) (i : Fin 3)
    (hc : ∀j I,I∈(child s C R B η t).slots j→IsCoprime (Ideal.span {p}) I)
    (Bp : actualAllocations (activeInput (child s C R B η t)).pools
      ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations
      (twiceChild s C R B η t (Ideal.span {p}) (errorIndex i+1)
        (errorActiveAllocation (child s C R B η t) _ Bp) υ v).pools E₂) :
    Cycle62FinalError.Chain s :=
  {C₁:=C,R₁:=R,B₁:=B,η₁:=η,t₁:=t,p:=p,hp:=hp,k:=errorIndex i+1,
    hk:=Nat.succ_le_succ (Nat.zero_le (errorIndex i)),coprime:=hc,
    Bp:=errorActiveAllocation (child s C R B η t) _ Bp,υ:=υ,t₂:=v,
    E₂:=E₂,R₂:=R₂,B₂:=B₂}

section Extracted
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
  (p : O) (i : Fin 3)
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
local notation "firstIdeal" => geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK bin q.1.val
local notation "firstEta" => geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK bin q.1.val
local notation "firstSrc" => geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ hK bin t q
local notation "Qp" => Ideal.span {p}
local notation "errorPower" => errorIndex i+1
variable (Bp : actualAllocations (activeInput
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1)))
  (υ : Character) (v : ℝ)

/-- The extracted child uses the active allocation lifted to the original
first child; it retains the exact prime and one of the three error indices. -/
def geometryErrorChild (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow ξ t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) :
    Input (liveIndices (errorActiveAllocation
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val) :=
  twiceChild s
    (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R q.2
    (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) t (Ideal.span {p}) (errorIndex i+1)
    (errorActiveAllocation
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp) υ v

/-- The literal source radius from the amplification error sum. -/
def geometryErrorSourceRadius : ℝ :=
  let g := geometryBranch reflected s R seed (Z^Mrow) Z ξ hK bin q.1.val
  errorCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z)
    g.cLog (3*amp) (frequencyLoss Z 32 ξ) reserve p errorPower

def geometryErrorFourierScale : ℝ :=
  (b^N*volume s/(((firstIdeal).absNorm:ℝ)*(normValue p)^errorPower))^2/
    geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i

local notation "extracted" => geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v
local notation "rad" => geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
local notation "fourier" => geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i

omit [DecidableEq α] in
theorem actual_geometry_error_source_radius_pos : 0<rad :=
  Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _


/-- All three allocations are the actual tuples. The error extraction
never enlarges the active allocation summation domain. -/
def geometryErrorChain (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow ξ t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) (hp : p≠0)
    (hc : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I)
    (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations
      (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v).pools E₂) :
    Cycle62FinalError.Chain s :=
  errorAdmissionChain s
    (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R q.2
    (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) t p hp i hc Bp υ v E₂ R₂ B₂

omit [DecidableEq α] in
theorem actual_geometry_error_chain_fields (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow ξ t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I) (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools E₂) :
    let chain:=geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop E₂ R₂ B₂
    chain.C₁=(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ∧ chain.R₁=R ∧ HEq chain.B₁ q.2 ∧ chain.η₁=(geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ∧
      chain.t₁=t ∧ chain.first=(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) ∧ chain.p=p ∧ chain.k=(errorIndex i+1) ∧
      HEq chain.Bp (errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp) ∧ chain.υ=υ ∧ chain.t₂=v ∧
      HEq chain.extracted (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ∧ chain.E₂=E₂ ∧ chain.R₂=R₂ ∧ HEq chain.B₂ B₂ :=
  ⟨rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,HEq.rfl,rfl,rfl,HEq.rfl⟩

/-- The original actual error-source summand equals the exact unpruned
extracted dictionary used by the geometry constructor. -/
theorem actual_geometry_error_active_source (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) :
    childNormalizedGaussSource (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)) ((Ideal.span {p})^(errorIndex i+1)) (R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))
      q.1.val.2.1.val Bp υ v ballProfile (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)=
      normalizedGaussSource (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val ballProfile (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) := by
  exact error_active_twice_source s (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R q.1.val.2.1.val q.2 (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) t
    p i Bp υ v ballProfile (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)

omit [DecidableEq α] in
theorem actual_geometry_error_radius (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I) (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools E₂) :
    Cycle62FinalError.errorRadius
      (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop E₂ R₂ B₂)
      (geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val)
      (geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val)
      Z Mrow amp (frequencyLoss Z 32 ξ) reserve ξ b N=frequencyRadius (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ := by
  cases reflected
  · rfl
  · let src := geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1
    let A := (b^N*volume s/((src.D.absNorm:ℝ)*(normValue p)^(errorIndex i+1)))^2
    change frequencyRadius (A/errorCommonRadius Z (Real.logb Z (src.C.absNorm:ℝ))
      (nominalLog src.D src.C
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex src.D src.C=>P.val)
          (swapSubset src.C src.D src.inactive)}) (Z^Mrow) (volume s) Z)
      (Real.logb Z (src.D.absNorm:ℝ)) (3*amp) (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1)) Z ξ=
      frequencyRadius (A/errorCommonRadius Z (Real.logb Z (src.C.absNorm:ℝ))
        (nominalLog src.C src.D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex src.C src.D=>P.val) src.inactive})
          (Z^Mrow) (volume s) Z)
        (Real.logb Z (src.D.absNorm:ℝ)) (3*amp) (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1)) Z ξ
    rw [swapSubset_generator,nominalLog_swap]

abbrev GeometryErrorSecondIndex (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) :=
  ActualSecondBlockIndex (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ

/-- Actual retained second-transform datum, with its finite character
family, original polynomial and exact extracted cutoff. -/
def geometryErrorSecondDatum (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v) :
    SecondInputDatum (liveIndices q.2.val) :=
  actualSecondBlockDatum (liveIndices (errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val)
    (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property) hw₁ hw₂ (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) n


/-- Blocks canceled by the actual sum are removed before absolute values. -/
def geometryErrorNonzeroBlocks (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0) : Finset
    (GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v) :=
  Finset.univ.filter (fun n=>((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂) n).block.value ballProfile≠0)

set_option linter.defProp false in
/-- Literal specialization of the proved nonzero-block filter identity.
The inferred result retains the original dependent finite sum. -/
def actual_geometry_error_nonzero_retained_assembly (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0) :=
  actual_nonzero_retained_assembly
    (liveIndices (errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val) (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property) hw₁ hw₂ ballProfile (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)


def geometryErrorActualChain (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂) (second : Bool)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C)) : Cycle62FinalError.Chain s :=
  geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
    (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C) ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).R B₂

/-- The admitted geometry is assembled from one actual nonzero physical
block, two supported allocations and the amplification conductor receipt. -/
def geometryErrorActualGeometry (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂) (second : Bool)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C))
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤radicalBound (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ) fixedBadMask p
      (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C) ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).R ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).ν ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).W ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).P≠0) :
    Cycle62FinalError.Geometry s
      (geometryErrorActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hp hcop hw₁ hw₂ n second B₂)
      Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b (fixedFactor:ℝ) N :=
  let datum := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val
  {D₁:=geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val,
    hC₁:=(actual_geometry_error_first_support reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val).1,
    hD₁:=(actual_geometry_error_first_support reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val).2.1,
    heq₁:=(actual_geometry_error_first_support reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val).2.2,
    E:=geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val,
    hmod:=actual_geometry_error_first_modulus reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val,
    moving_modulus:=actual_error_moving_modulus (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) υ ψ p hp Z hZ i hυ,
    δ:=frequencyLoss Z 32 ξ,reserve:=reserve,homega:=rfl,
    C:=datum.C,D:=datum.D,hC:=datum.hC,hD:=datum.hD,heq:=datum.sameSupport,U:=datum.inactive,
    τ:=datum.τ,family:=datum.family,label:=by
      cases second
      · exact Or.inl rfl
      · exact Or.inr rfl,
    first_nonzero:=hf₁,second_nonzero:=hf₂,
    cols:=datum.block.pool,coefficient:=datum.block.beta,frequencies:=datum.rows,
    profile:=ballProfile,scale:=datum.K,scale_pos:=datum.K_pos,bin:=datum.dyad,
    block_nonzero:=by
      change physicalBlock υ v datum.block.pool datum.block.beta datum.C datum.D
        datum.hC datum.hD datum.inactive
        (Cycle62FinalError.errorRadius
          (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
            (if second then datum.D else datum.C) datum.R B₂)
          (geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
          (geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
          Z Mrow amp (frequencyLoss Z 32 ξ) reserve ξ b N)
        datum.rows ballProfile datum.K datum.dyad≠0
      rw [actual_geometry_error_radius reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hp hcop
        (if second then datum.D else datum.C) datum.R B₂]
      exact (Finset.mem_filter.mp n.property).2}

end Extracted
end
end OAI.SevenEighths.Cycle62InitialMass

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_first_support
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_first_modulus
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_child_coprime
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometryErrorChild
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometryErrorChain
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_chain_fields
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_active_source
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_radius
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometryErrorSecondDatum
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_nonzero_retained_assembly
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometryErrorActualChain
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometryErrorActualGeometry

#print axioms OAI.SevenEighths.Cycle62InitialMass.errorAdmissionChain
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometryErrorNonzeroBlocks
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometryErrorSourceRadius
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometryErrorFourierScale
