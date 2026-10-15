/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryMainOrdinaryContraction
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorNormalizedFullFamily
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorRemainder
import Candidate.Cycle62.Physical.InitialMass.SecondDatumReindex

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationErrorEnergy CenteredMomentPrimeElements
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSourceMass CenteredMomentCommonHeightEnvelope CenteredMomentHeckeColumnWindow
open CenteredMomentCommonPairedSource
local notation "O" => HeckeFamily.O
local instance geometryErrorOrdinaryContractionDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _
universe u
variable {α : Type u} [Fintype α]

private def errorCanonicalDatum {ι : Type*} [Fintype ι] (eqι : DecidableEq ι)
    (d : @SecondInputDatum ι _ eqι) : @SecondInputDatum ι _ (Classical.decEq ι) :=
  cast (congrArg (fun e=>@SecondInputDatum ι _ e)
    (Subsingleton.elim eqι (Classical.decEq ι))) d

private theorem error_canonical_block {ι : Type*} [Fintype ι] (eqι : DecidableEq ι)
    (d : @SecondInputDatum ι _ eqι) :
    (letI := Classical.decEq ι; (errorCanonicalDatum eqι d).block)=
      (letI := eqι; d.block) := by
  have he : eqι=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  rfl

private theorem error_canonical_source_rows {ι : Type*} [Fintype ι] (eqι : DecidableEq ι)
    (d : @SecondInputDatum ι _ eqι)
    (hr : letI := eqι; d.rows=sourceRows d.C d.D d.inactive d.radius) :
    letI := Classical.decEq ι
    (errorCanonicalDatum eqι d).rows=sourceRows (errorCanonicalDatum eqι d).C
      (errorCanonicalDatum eqι d).D (errorCanonicalDatum eqι d).inactive (errorCanonicalDatum eqι d).radius := by
  have he : eqι=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  exact hr

private theorem error_image_source_rows {ι β : Type*} [Fintype ι] [Fintype β]
    (e : ι↪β) (d : SecondInputDatum ι)
    (hr : d.rows=sourceRows d.C d.D d.inactive d.radius) :
    (d.image e).rows=sourceRows (d.image e).C (d.image e).D
      (d.image e).inactive (d.image e).radius := hr

private theorem error_canonical_exceptional_block {ι : Type*} [Fintype ι]
    (eqι : DecidableEq ι) (d : @SecondInputDatum ι _ eqι)
    (χ : RayCharacter) (Q : Ideal O) (m : O) :
    (letI := Classical.decEq ι; (mainExceptionalDatum (errorCanonicalDatum eqι d) χ Q m).block)=
      (letI := eqι; (mainExceptionalDatum d χ Q m).block) := by
  have he : eqι=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  rfl

private theorem error_image_exceptional_block {ι β : Type*} [Fintype ι] [Fintype β]
    (e : ι↪β) (d : SecondInputDatum ι) (χ : RayCharacter) (Q : Ideal O) (m : O) :
    (mainExceptionalDatum (d.image e) χ Q m).block=(mainExceptionalDatum d χ Q m).block := by
  change ((mainExceptionalDatum d χ Q m).image e).block=_
  exact second_datum_image_block e (mainExceptionalDatum d χ Q m)

private theorem error_canonical_column {ι : Type*} [Fintype ι]
    (eqι : DecidableEq ι) (d : @SecondInputDatum ι _ eqι)
    (η : Character) (t : ℝ) (C : Ideal O) (hC : Supported C) (L : Ideal O) (z : O) :
    (letI := Classical.decEq ι;
      normalizedColumn (withHeight (errorCanonicalDatum eqι d).input η t) C hC
        (errorCanonicalDatum eqι d).R (errorCanonicalDatum eqι d).seed L z)=
    (letI := eqι; normalizedColumn (withHeight d.input η t) C hC d.R d.seed L z) := by
  have he : eqι=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  rfl

private theorem error_canonical_ordinary_block {ι : Type*} [Fintype ι]
    (eqι : DecidableEq ι) (d : @SecondInputDatum ι _ eqι)
    (χ : RayCharacter) (Q : Ideal O) (m : O) :
    (letI := Classical.decEq ι; (ordinarySecondDatum (errorCanonicalDatum eqι d) χ Q m).block)=
      (letI := eqι; (ordinarySecondDatum d χ Q m).block) := by
  have he : eqι=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  rfl

private theorem error_image_ordinary_block {ι β : Type*} [Fintype ι] [Fintype β]
    (e : ι↪β) (d : SecondInputDatum ι) (χ : RayCharacter) (Q : Ideal O) (m : O) :
    (ordinarySecondDatum (d.image e) χ Q m).block=(ordinarySecondDatum d χ Q m).block := by
  change ((ordinarySecondDatum d χ Q m).image e).block=_
  exact second_datum_image_block e (ordinarySecondDatum d χ Q m)

private theorem error_canonical_fields {ι : Type*} [Fintype ι]
    (eqι : DecidableEq ι) (d : @SecondInputDatum ι _ eqι) :
    (letI := Classical.decEq ι; (errorCanonicalDatum eqι d).C)=(letI := eqι; d.C) ∧
    (letI := Classical.decEq ι; (errorCanonicalDatum eqι d).D)=(letI := eqι; d.D) ∧
    (letI := Classical.decEq ι; (errorCanonicalDatum eqι d).τ)=(letI := eqι; d.τ) ∧
    (letI := Classical.decEq ι; (errorCanonicalDatum eqι d).input.t)=(letI := eqι; d.input.t) := by
  have he : eqι=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem error_image_fields {ι β : Type*} [Fintype ι] [Fintype β]
    (e : ι↪β) (d : SecondInputDatum ι) :
    (d.image e).C=d.C ∧ (d.image e).D=d.D ∧
      (d.image e).τ=d.τ ∧ (d.image e).input.t=d.input.t :=
  ⟨rfl,rfl,rfl,rfl⟩

private theorem error_fields_trans {a b c d e f : Ideal O}
    {τ υ ν : RayCharacter→Character} {t u v : ℝ}
    (h : a=b ∧ d=e ∧ τ=υ ∧ t=u) (g : b=c ∧ e=f ∧ υ=ν ∧ u=v) :
    a=c ∧ d=f ∧ τ=ν ∧ t=v :=
  ⟨h.1.trans g.1,h.2.1.trans g.2.1,h.2.2.1.trans g.2.2.1,h.2.2.2.trans g.2.2.2⟩

set_option maxHeartbeats 10000 in
private theorem error_coefficient_cast_core (a w n l V : ℝ) :
    (a:ℂ)*((w*(16*n*l)/V:ℝ):ℂ)=((a*w*16*n*l/V:ℝ):ℂ) := by
  push_cast
  ring

private theorem error_normalized_coefficient_cast (P : Finset (Ideal O))
    (w V : ℝ) (p : O) (i : Fin 3) :
    ((56/(P.card:ℝ):ℝ):ℂ)*((w*(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))/V:ℝ):ℂ)=
      (errorNormalizedCoefficient P w V p i:ℂ) :=
  error_coefficient_cast_core (56/(P.card:ℝ)) w (errorIndex i+2:ℝ)
    (localErrorCost p (errorIndex i)) V

private theorem error_normalized_sigma {A : Type*} [Fintype A]
    {B : A→Type*} [∀a,Fintype (B a)] (c : ℂ) (g q r : A→ℂ)
    (w v v' : (a : A)→B a→ℂ)
    (hc : ∀a,c*g a=q a) (hr : ∀a,r a=∑b,w a b*v a b)
    (hv : ∀a b,v' a b=v a b) :
    c*(∑a,g a*r a)=∑j : (a : A) × B a,(q j.1*w j.1 j.2)*v' j.1 j.2 := by
  rw [Finset.mul_sum,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [←mul_assoc,hc a,hr a,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [hv a b]
  exact (mul_assoc _ _ _).symm

private theorem error_normalized_sigma_receipt {A : Type*} [Fintype A]
    {B : A→Type*} [∀a,Fintype (B a)] {r : A→ℂ}
    {w v : (a : A)→B a→ℂ}
    (hr : ∀a,r a=∑b,w a b*v a b)
    (c : ℂ) (g q : A→ℂ) (v' : (a : A)→B a→ℂ)
    (hc : ∀a,c*g a=q a) (hv : ∀a b,v' a b=v a b) :
    c*(∑a,g a*r a)=∑j : (a : A) × B a,(q j.1*w j.1 j.2)*v' j.1 j.2 :=
  error_normalized_sigma c g q r w v v' hc hr hv

attribute [local irreducible] geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild

set_option maxHeartbeats 100000 in
set_option linter.defProp false in
private def error_geometry_source_receipt (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0) :=
  actual_geometry_error_nonzero_retained_assembly (α:=α)
    reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂


section ReceiptConversion
attribute [local semireducible] geometryErrorSecondDatum geometryErrorNonzeroBlocks
set_option maxHeartbeats 100000 in
set_option linter.defProp false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 20000 in
private def error_geometry_filtered_receipt (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0) :=
  let src:=geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v
  let blocks:=geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂
  let f:=fun n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v=>
    (heightCoeff src.η src.t n.1.val.val.1*star (heightCoeff src.η src.t n.1.val.val.2))*
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile
  (error_geometry_source_receipt (α:=α) reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂).trans
    (Finset.sum_coe_sort blocks f)
set_option maxHeartbeats 20000 in
set_option linter.defProp false in
set_option backward.isDefEq.respectTransparency false in
private def error_geometry_subtype_receipt (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0) :=
  let src:=geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v
  let blocks:=geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂
  let f:=fun n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v=>
    (heightCoeff src.η src.t n.1.val.val.1*star (heightCoeff src.η src.t n.1.val.val.2))*
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile
  (error_geometry_filtered_receipt (α:=α) reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂).trans
    (Finset.sum_coe_sort blocks f).symm
end ReceiptConversion



section Actual
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
local notation "N" => Fintype.card α
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
local notation "First" => GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ hK key
variable (P : Finset (Ideal O)) (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)

/-- The extraction menu is unchanged from the literal retained remainder. -/
abbrev GeometryJointErrorSourceIndex :=
  (q : First) × (p : elementPool P) × (i : Fin 3) × (_ψ : RayCharacter) ×
    actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK key t q)).pools
        ((Ideal.span {p.val})^(errorIndex i+1))
local notation "Sources" => GeometryJointErrorSourceIndex (reflected:=reflected) (s:=s) (R:=R) (seed:=seed) (Z:=Z) (M:=M) (ξ:=ξ) (t:=t) (hZ:=hZ) (key:=key) (P:=P)


abbrev GeometryJointErrorSelectedIndex (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) :=
  (l : Sources) × geometryErrorNonzeroBlocks reflected s R seed Z M amp ξ reserve b t N hZ key
    l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂

/-- Ambient embedding changes no physical block or original Fourier scale. -/
def geometryJointErrorDatum (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) :
    @SecondInputDatum α _ (Classical.decEq α) :=
  (errorCanonicalDatum _ (geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
    j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
    (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t hz₁ hz₂ j.2.val)).image
      ⟨Subtype.val,Subtype.val_injective⟩

set_option linter.defProp false in
def geometry_joint_error_datum_block (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) :=
  let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
    j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
    (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t hz₁ hz₂ j.2.val
  (second_datum_image_block (⟨Subtype.val,Subtype.val_injective⟩ :
      ↥(liveIndices j.1.1.2.val)↪α) (errorCanonicalDatum _ d)).trans
    (error_canonical_block _ d)

set_option linter.defProp false in
def geometry_joint_error_exceptional_datum_block (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
    (χ : RayCharacter) (Q : Ideal O) (m : O) :=
  let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
    j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
    (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t hz₁ hz₂ j.2.val
  (error_image_exceptional_block (⟨Subtype.val,Subtype.val_injective⟩ :
    ↥(liveIndices j.1.1.2.val)↪α) (errorCanonicalDatum _ d) χ Q m).trans
      (error_canonical_exceptional_block _ d χ Q m)

set_option linter.defProp false in
def geometry_joint_error_ordinary_datum_block (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
    (χ : RayCharacter) (Q : Ideal O) (m : O) :=
  let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
    j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
    (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t hz₁ hz₂ j.2.val
  (error_image_ordinary_block (⟨Subtype.val,Subtype.val_injective⟩ :
    ↥(liveIndices j.1.1.2.val)↪α) (errorCanonicalDatum _ d) χ Q m).trans
      (error_canonical_ordinary_block _ d χ Q m)

set_option linter.defProp false in
def geometry_joint_error_datum_column (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
    (η : Character) (v : ℝ) (C : Ideal O) (hC : Supported C) (L : Ideal O) (z : O) :=
  let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
    j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
    (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t hz₁ hz₂ j.2.val
  (second_datum_image_column (⟨Subtype.val,Subtype.val_injective⟩ :
    ↥(liveIndices j.1.1.2.val)↪α) (errorCanonicalDatum _ d) η v C hC L z).trans
      (error_canonical_column _ d η v C hC L z)

set_option linter.defProp false in
def geometry_joint_error_datum_fields (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
    :=
  let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
    j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
    (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t hz₁ hz₂ j.2.val
  error_fields_trans
    (error_image_fields (⟨Subtype.val,Subtype.val_injective⟩ :
      ↥(liveIndices j.1.1.2.val)↪α) (errorCanonicalDatum _ d))
    (error_canonical_fields _ d)

set_option linter.defProp false in
private def error_geometry_source_rows (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) :=
  let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
    j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
    (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t hz₁ hz₂ j.2.val
  error_image_source_rows (⟨Subtype.val,Subtype.val_injective⟩ : ↥(liveIndices j.1.1.2.val)↪α)
    (errorCanonicalDatum _ d)
    (error_canonical_source_rows _ d (by
      unfold d geometryErrorSecondDatum actualSecondBlockDatum actualSecondInputDatum
      rfl))

variable (Mprice Aprice : ℝ)
    (weight : Cycle62JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ)

def geometryJointErrorWeight (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) : ℂ :=
  let firstWeight:=geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice hK key weight N b j.1.1.1.val j.1.1.2
  let src:=geometryErrorChild reflected s R seed Z M ξ t hZ key j.1.1 j.1.2.1.val
    j.1.2.2.1 j.1.2.2.2.2 (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t
  (errorNormalizedCoefficient P firstWeight (volume src) j.1.2.1.val j.1.2.2.1:ℂ)*
    actualSecondBlockWeight src
      ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.1.1.1.val)*
        (Ideal.span {j.1.2.1.val})^(errorIndex j.1.2.2.1+1)) j.1.1.1.val.2.1.val
      (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ key j.1.1 j.1.2.1.val j.1.2.2.1)
      (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b N hZ key j.1.1 j.1.2.1.val j.1.2.2.1)
      Z ξ j.2.val

attribute [local irreducible] geometryJointErrorDatum geometryJointErrorWeight


set_option maxHeartbeats 100000 in
set_option linter.defProp false in
private def error_geometry_raw_nonzero_sum (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) :=
  let source:=fun l : Sources=>geometryErrorChild reflected s R seed Z M ξ t hZ key l.1 l.2.1.val l.2.2.1 l.2.2.2.2
    (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t
  let first:=fun l : Sources=>geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice hK key weight N b l.1.1.val l.1.2
  let g:=fun l : Sources=>(((first l*(16*(errorIndex l.2.2.1+2:ℝ)*localErrorCost l.2.1.val (errorIndex l.2.2.1)))/volume (source l):ℝ):ℂ)
  let q:=fun l : Sources=>(errorNormalizedCoefficient P (first l) (volume (source l)) l.2.1.val l.2.2.1:ℂ)
  let B:=fun l : Sources=>↥(geometryErrorNonzeroBlocks reflected s R seed Z M amp ξ reserve b t N hZ key
    l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂)
  let raw:=fun (l : Sources)(n : B l)=>geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
    l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂ n.val
  let hr:=fun l : Sources=>error_geometry_subtype_receipt (α:=α) reflected s R seed Z M amp ξ reserve b t N hZ key
    l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂
  error_normalized_sigma_receipt hr ((56/(P.card:ℝ):ℝ):ℂ) g q
    (fun l n=>((errorCanonicalDatum _ (raw l n)).image
      (⟨Subtype.val,Subtype.val_injective⟩ : ↥(liveIndices l.1.2.val)↪α)).block.value ballProfile)
    (fun l=>error_normalized_coefficient_cast P (first l) (volume (source l)) l.2.1.val l.2.2.1)
    (fun l n=>congrArg (fun block=>block.value ballProfile)
      ((second_datum_image_block (⟨Subtype.val,Subtype.val_injective⟩ :
        ↥(liveIndices l.1.2.val)↪α) (errorCanonicalDatum _ (raw l n))).trans
          (error_canonical_block _ (raw l n))))


section LiteralReceipt
attribute [local semireducible] geometryErrorChild geometryLowFirstChild

set_option maxHeartbeats 100000 in
set_option linter.defProp false in
/-- The full physical filter is imposed before the two row restrictions. -/
def actual_geometry_error_retained_nonzero_sum (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) :=
  let h:=error_geometry_raw_nonzero_sum reflected s R seed Z M amp ξ reserve b t hZ key
    P υ Mprice Aprice weight hz₁ hz₂
  show ((56/(P.card:ℝ):ℝ):ℂ)*jointErrorRetained
    (fun q : First=>liveIndices q.2.val)
    (fun q=>geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK key t q)
    (fun q=>geometryBranch reflected s R seed (Z^M) Z ξ hK key q.1.val)
    (fun q=>geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
      hK key weight N b q.1.val q.2)
    ballProfile Z (3*amp) ξ reserve P υ
    (fun q p i=>geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b N hZ key q p.val i)=_ from h
end LiteralReceipt

end Actual

private theorem error_uniform_map {p q : ℝ→Prop}
    (h : ∃C,p C) (f : ∀C,p C→q C) : ∃C,q C := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C,f C hC⟩

private theorem error_pair_receipt {p q : Prop} (hp : p) (hq : q) : p∧q := ⟨hp,hq⟩

private theorem error_retained_receipt {Label : Type u} [Fintype Label]
    {c : ℝ} {a : ℂ} {w v : Label→ℂ}
    (he : (c:ℂ)*a=∑j,w j*v j) (hc : 0≤c)
    (A degree windowDegree : ℕ) (C : ℝ)
    (hbound : ∀{Label : Type u}[Fintype Label]
      (d : Label→SecondInputDatum α) (w : Label→ℂ) (χ : Label→RayCharacter)
      (Q : Ideal O) (m : O) (E H : ℤ→ℝ),
      (∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0<H r) →
      SecondNormalizedBound ballProfile degree windowDegree
        (fun l=>ordinarySecondDatum (d l) (χ l) Q m) w E H →
      ‖∑l,w l*(d l).block.value ballProfile‖ ≤
        (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value ballProfile‖)+
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A)
    (d : Label→SecondInputDatum α)
    (hrows : ∀j,(d j).rows=sourceRows (d j).C (d j).D (d j).inactive (d j).radius)
    (hv : ∀j,v j=(d j).block.value ballProfile) :
    ∀(χ : Label→RayCharacter)(Q : Ideal O)(m : O)(E H : ℤ→ℝ),
    (∀r∈secondRatioBins (fun j=>(d j).block),0≤E r) →
    (∀r∈secondRatioBins (fun j=>(d j).block),0<H r) →
    SecondNormalizedBound ballProfile degree windowDegree
      (fun j=>ordinarySecondDatum (d j) (χ j) Q m) w E H →
    c*‖a‖≤(∑j,‖w j*(mainExceptionalDatum (d j) (χ j) Q m).block.value ballProfile‖)+
      C*∑r∈secondRatioBins (fun j=>(d j).block),E r/(1+dyadicScale r)^A := by
  intro χ Q m E H hE hH hnorm
  have h:=hbound d w χ Q m E H hrows hE hH hnorm
  have he':(c:ℂ)*a=∑j,w j*(d j).block.value ballProfile := by
    simpa only [hv] using he
  rw [←he'] at h
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc] using h

set_option maxHeartbeats 100000 in
set_option linter.defProp false in
private def error_geometry_contraction_point (A degree windowDegree : ℕ) (C : ℝ)
    (hbound : ∀{Label : Type u}[Fintype Label]
      (d : Label→SecondInputDatum α) (w : Label→ℂ) (χ : Label→RayCharacter)
      (Q : Ideal O) (m : O) (E H : ℤ→ℝ),
      (∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0<H r) →
      SecondNormalizedBound ballProfile degree windowDegree
        (fun l=>ordinarySecondDatum (d l) (χ l) Q m) w E H →
      ‖∑l,w l*(d l).block.value ballProfile‖ ≤
        (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value ballProfile‖)+
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A)
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (Mprice Aprice : ℝ)
    (weight : Cycle62JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ) :=
  error_retained_receipt
    (actual_geometry_error_retained_nonzero_sum reflected s R seed Z M amp ξ reserve b t hZ key
      P υ Mprice Aprice weight hz₁ hz₂)
    (div_nonneg (by norm_num : (0:ℝ)≤56) (Nat.cast_nonneg P.card))
    A degree windowDegree C hbound
    (geometryJointErrorDatum reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
    (error_geometry_source_rows reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
    (by intro j; unfold geometryJointErrorDatum; rfl)

set_option linter.defProp false in
/-- Constants precede every moving source. The normalized input and the
exceptional remainder retain the original full nonzero filter. -/
def actual_geometry_error_ordinary_contraction (A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :=
  error_uniform_map (main_original_from_normalized.{u,u} (α:=α) ballProfile
    A degree windowDegree hc hs) (fun C hbound=>
      error_pair_receipt hbound.1
        (error_geometry_contraction_point A degree windowDegree C hbound.2))

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_retained_nonzero_sum
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_ordinary_contraction
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_joint_error_datum_block

#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_joint_error_exceptional_datum_block

#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_joint_error_datum_column
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_joint_error_ordinary_datum_block

#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_joint_error_datum_fields

#check @OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_ordinary_contraction
