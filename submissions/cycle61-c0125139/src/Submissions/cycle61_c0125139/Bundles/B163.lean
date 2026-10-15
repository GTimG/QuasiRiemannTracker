/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B117
import Submissions.cycle61_c0125139.Bundles.B145
import Submissions.cycle61_c0125139.Bundles.B148
import Submissions.cycle61_c0125139.Bundles.B154
import Submissions.cycle61_c0125139.Bundles.B155
import Submissions.cycle61_c0125139.Bundles.B156
import Submissions.cycle61_c0125139.Bundles.B158
import Submissions.cycle61_c0125139.Bundles.B160
import Submissions.cycle61_c0125139.Bundles.B161
import Submissions.cycle61_c0125139.Bundles.B162
import Lean

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorOrdinaryContraction; sha256 b4bed9a8f841a5220bfebbd4b4d7cfe505ae672e00d7eeb662258f3ce47e1b79 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                   
                                                                     
                                                          
                                                      

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
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
    {τ υ ν : RayCharacter→ Character} {t u v : ℝ}
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
    {B : A→ Type*} [∀a,Fintype (B a)] (c : ℂ) (g q r : A→ℂ)
    (w v v' : (a : A)→ B a→ℂ)
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
    {B : A→ Type*} [∀a,Fintype (B a)] {r : A→ℂ}
    {w v : (a : A)→ B a→ℂ}
    (hr : ∀a,r a=∑b,w a b*v a b)
    (c : ℂ) (g q : A→ℂ) (v' : (a : A)→ B a→ℂ)
    (hc : ∀a,c*g a=q a) (hv : ∀a b,v' a b=v a b) :
    c*(∑a,g a*r a)=∑j : (a : A) × B a,(q j.1*w j.1 j.2)*v' j.1 j.2 :=
  error_normalized_sigma c g q r w v v' hc hr hv

attribute [local irreducible] geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild

set_option maxHeartbeats 100000 in
set_option linter.defProp false in
private def error_geometry_source_receipt (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
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
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
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
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
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
  (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
local notation "N" => Fintype.card α
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
local notation "First" => GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ hK key
variable (P : Finset (Ideal O)) (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)

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
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ)

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

private theorem error_uniform_map {p q : ℝ→ Prop}
    (h : ∃C,p C) (f : ∀C,p C→ q C) : ∃C,q C := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C,f C hC⟩

private theorem error_pair_receipt {p q : Prop} (hp : p) (hq : q) : p∧q := ⟨hp,hq⟩

private theorem error_retained_receipt {Label : Type u} [Fintype Label]
    {c : ℝ} {a : ℂ} {w v : Label→ℂ}
    (he : (c:ℂ)*a=∑j,w j*v j) (hc : 0≤ c)
    (A degree windowDegree : ℕ) (C : ℝ)
    (hbound : ∀{Label : Type u}[Fintype Label]
      (d : Label→ SecondInputDatum α) (w : Label→ℂ) (χ : Label→ RayCharacter)
      (Q : Ideal O) (m : O) (E H : ℤ→ℝ),
      (∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤ E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0< H r) →
      SecondNormalizedBound ballProfile degree windowDegree
        (fun l=>ordinarySecondDatum (d l) (χ l) Q m) w E H →
      ‖∑l,w l*(d l).block.value ballProfile‖ ≤
        (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value ballProfile‖)+
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A)
    (d : Label→ SecondInputDatum α)
    (hrows : ∀j,(d j).rows=sourceRows (d j).C (d j).D (d j).inactive (d j).radius)
    (hv : ∀j,v j=(d j).block.value ballProfile) :
    ∀(χ : Label→ RayCharacter)(Q : Ideal O)(m : O)(E H : ℤ→ℝ),
    (∀r∈secondRatioBins (fun j=>(d j).block),0≤ E r) →
    (∀r∈secondRatioBins (fun j=>(d j).block),0< H r) →
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
      (d : Label→ SecondInputDatum α) (w : Label→ℂ) (χ : Label→ RayCharacter)
      (Q : Ideal O) (m : O) (E H : ℤ→ℝ),
      (∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤ E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0< H r) →
      SecondNormalizedBound ballProfile degree windowDegree
        (fun l=>ordinarySecondDatum (d l) (χ l) Q m) w E H →
      ‖∑l,w l*(d l).block.value ballProfile‖ ≤
        (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value ballProfile‖)+
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A)
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ) :=
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_retained_nonzero_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_ordinary_contraction
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_datum_block

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_exceptional_datum_block

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_datum_column
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_ordinary_datum_block

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_error_datum_fields

#check @OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_ordinary_contraction

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorOrdinaryContraction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorContraction; sha256 83946ce41c2483257e7373757111773a1f7bc51ba04089471cca15cf61438207 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                    
                                                                    
                                                                
           

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true

namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle61InitialSource
open CenteredMomentCommonProfile CenteredMomentAmplificationRadicalFamily
open CenteredMomentChildRows CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentAllocatedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable

private theorem affine_error_plain_zero (p : Profiles (1/4) (9/4)) (i : Fin 2) :
    p.profile i 0=0 := by
  by_contra h
  have hh:=(p.support i h).1
  norm_num at hh

private theorem affine_error_sum_transport {Label : Type*} [Fintype Label]
    {f : Label→ℝ} {r : ℝ} (h : ∑j,f j≤ r)
    (g : Label→ℝ) (hg : ∀j,g j=f j) : ∑j,g j≤ r := by
  simpa only [hg] using h

private theorem affine_error_rhs_transport {a b c : ℝ} (h : a≤ b) (he : b=c) : a≤ c :=
  h.trans_eq he

private theorem affine_error_combine {a exceptional mass cap ordinary : ℝ}
    (h : a≤ exceptional+ordinary)(hp : exceptional≤ mass)(hc : mass≤ cap) :
    a≤ cap+ordinary := by
  linarith only [h,hp,hc]

private theorem affine_error_distribute {Label : Type*} [Fintype Label]
    {a c : ℝ} {f : Label→ℝ} (h : a≤ c*∑j,f j) : a≤∑j,c*f j := by
  simpa only [Finset.mul_sum] using h

private theorem affine_error_sigma_ray_payment {Label : Type*} [Fintype Label]
    {Rows : Label→ Type*} [∀l,Fintype (Rows l)]
    {f : (l : Label)→(Rows l→ RayCharacter)→ Rows l→ℝ} {g : Label→ℝ}
    (h : ∀l χ,∑n,f l χ n≤ g l) (χ : ((l : Label)×Rows l)→ RayCharacter) :
    (∑j : (l : Label)×Rows l,f j.1 (fun n=>χ ⟨j.1,n⟩) j.2)≤∑l,g l := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum (fun l _=>h l (fun n=>χ ⟨l,n⟩))

local syntax (name := affineErrorSource) "affine_error_source " term ", " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorSource] private def elabAffineErrorSource : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let q ← elabTerm stx[3] none
  let m ← elabTerm stx[5] none
  let ht ← inferType h
  forallBoundedTelescope ht (some 1) fun xs _=>do
    unless xs.size=1 do throwError "expected a raw-character binder"
    let paid:=mkAppN h #[xs[0]!,q,m]
    let result ← mkAppM ``affine_error_distribute #[paid]
    mkLambdaFVars xs result

local syntax (name := affineErrorCollect) "affine_error_collect " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorCollect] private def elabAffineErrorCollect : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let h ← instantiateMVars h
  let ht ← inferType h
  forallTelescope ht fun xs body=>do
    unless xs.size=2 do throwError "expected source and raw-character binders"
    let l:=xs[0]!
    let chi:=xs[1]!
    let chiType ← inferType chi
    let .forallE _ _ _ _:=chiType | throwError "expected raw character function"
    let leArgs:=body.getAppArgs
    unless body.getAppFn.isConstOf ``LE.le && leArgs.size≥2 do
      throwError "expected a real inequality"
    let lhs:=leArgs[leArgs.size-2]!
    let rhs:=leArgs[leArgs.size-1]!
    let sumArgs:=lhs.getAppArgs
    unless lhs.getAppFn.isConstOf ``Finset.sum && sumArgs.size≥2 do
      throwError "expected a finite raw row sum"
    let univ:=sumArgs[sumArgs.size-2]!
    let univArgs:=univ.getAppArgs
    unless univ.getAppFn.isConstOf ``Finset.univ && univArgs.size=2 do
      throwError "expected the complete raw finite carrier"
    if rhs.containsFVar chi.fvarId! then throwError "source cap depends on inducing ray"
    let label ← inferType l
    let labelClass ← mkAppM ``Fintype #[label]
    let labelInst ← synthInstance labelClass
    let rows ← mkLambdaFVars #[l] univArgs[0]!
    let rowsInst ← mkLambdaFVars #[l] univArgs[1]!
    let f ← mkLambdaFVars #[l,chi] sumArgs[sumArgs.size-1]!
    let g ← mkLambdaFVars #[l] rhs
    let u ← getDecLevel label
    let v ← getDecLevel univArgs[0]!
    pure (mkAppN (mkConst ``affine_error_sigma_ray_payment [u,v])
      #[label,labelInst,rows,rowsInst,f,g,h])

local syntax (name := affineErrorApply) "affine_error_apply " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorApply] private def elabAffineErrorApply : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let x ← elabTerm stx[3] none
  pure (mkApp h x)

local syntax (name := affineErrorCall) "affine_error_call " term "," "[" term,* "]" : term
open Lean Meta Elab Term in
@[term_elab affineErrorCall] private def elabAffineErrorCall : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let mut args:=#[]
  for i in [:stx[4].getSepArgs.size] do
    let a ← elabTerm stx[4].getSepArgs[i]! none
    args:=args.push a
  pure (mkAppN h args)

/- The final bridge term is fully specified. Skip only the elaborator's
repeated expected-type search; the declaration's kernel check remains mandatory. -/
local syntax (name := affineErrorExact) "affine_error_exact " term : tactic
open Lean Meta Elab Tactic in
@[tactic affineErrorExact] private def elabAffineErrorExact : Tactic := fun stx=>withMainContext do
  let proof ← Term.elabTerm stx[1] none
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar then throwError "the exact source bridge contains unresolved metavariables"
  let goal ← getMainGoal
  goal.assign proof
  replaceMainGoal []

local syntax (name := affineErrorTransport) "affine_error_transport " term ", " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorTransport] private def elabAffineErrorTransport : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let g ← elabTerm stx[3] none
  let he ← elabTerm stx[5] none
  let ht ← inferType h
  let args:=ht.getAppArgs
  unless ht.getAppFn.isConstOf ``LE.le && args.size≥2 do throwError "expected an inequality"
  let lhs:=args[args.size-2]!
  let rhs:=args[args.size-1]!
  let sa:=lhs.getAppArgs
  unless lhs.getAppFn.isConstOf ``Finset.sum && sa.size≥2 do throwError "expected a raw sum"
  let ua:=sa[sa.size-2]!.getAppArgs
  let u ← getDecLevel ua[0]!
  pure (mkAppN (mkConst ``affine_error_sum_transport [u])
    #[ua[0]!,ua[1]!,sa[sa.size-1]!,rhs,h,g,he])

local syntax (name := affineErrorCap) "affine_error_cap " term ", " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorCap] private def elabAffineErrorCap : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let c ← elabTerm stx[3] none
  let ht ← inferType h
  let args:=ht.getAppArgs
  unless ht.getAppFn.isConstOf ``LE.le && args.size≥2 do throwError "expected a paid inequality"
  let a:=args[args.size-2]!
  let b:=args[args.size-1]!
  let he ← elabTerm stx[5] none
  pure (mkAppN (mkConst ``affine_error_rhs_transport) #[a,b,c,h,he])

/- Avoid unfolding the frozen pointwise geometry predicate while selecting
its ordinary constant. These are plain Classical.choose and And projections. -/
local syntax (name := affineErrorChoice) "affine_error_choice " term ", " num : term
open Lean Meta Elab Term in
@[term_elab affineErrorChoice] private def elabAffineErrorChoice : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let ht ← instantiateMVars (← inferType h)
  let ht:=ht.headBeta
  unless ht.getAppFn.isConstOf ``Exists do throwError "expected a checked existential; head is {ht.getAppFn}"
  let ea:=ht.getAppArgs
  let carrier:=ea[ea.size-2]!
  let pred:=ea[ea.size-1]!
  let u ← getLevel carrier
  let chosen:=mkAppN (mkConst ``Classical.choose [u]) #[carrier,pred,h]
  let some mode:=stx[3].isNatLit? | throwError "expected an explicit selector"
  if mode=0 then return chosen
  let body:=(mkApp pred chosen).headBeta
  unless body.getAppFn.isConstOf ``And do throwError "expected a conjunction after the witness"
  let ba:=body.getAppArgs
  let spec:=mkAppN (mkConst ``Classical.choose_spec [u]) #[carrier,pred,h]
  if mode=1 then return mkAppN (mkConst ``And.left) #[ba[0]!,ba[1]!,spec]
  if mode=2 then return mkAppN (mkConst ``And.right) #[ba[0]!,ba[1]!,spec]
  throwError "expected witness, positive projection, or endpoint projection"

/- Read only the exact endpoint predicate of the frozen existential. -/
local syntax (name := affineErrorFrozenSpec) "affine_error_frozen_spec " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorFrozenSpec] private def elabAffineErrorFrozenSpec : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let c ← elabTerm stx[3] none
  let ht ← instantiateMVars (←inferType h)
  unless ht.getAppFn.isConstOf ``Exists do throwError "expected the frozen ordinary existential"
  let ea:=ht.getAppArgs
  lambdaTelescope ea[ea.size-1]! fun cs body=>do
    unless cs.size=1 && body.getAppFn.isConstOf ``And do throwError "expected positivity and the frozen endpoint"
    let ba:=body.getAppArgs
    let pred ← mkLambdaFVars cs ba[ba.size-1]!
    pure ((mkApp pred c).headBeta)

local syntax (name := affineErrorJoin) "affine_error_join " term ", " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorJoin] private def elabAffineErrorJoin : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let hp ← elabTerm stx[3] none
  let hc ← elabTerm stx[5] none
  let ht ← instantiateMVars (←inferType h)
  let pt ← instantiateMVars (←inferType hp)
  let ct ← instantiateMVars (←inferType hc)
  unless ht.getAppFn.isConstOf ``LE.le && pt.getAppFn.isConstOf ``LE.le &&
      ct.getAppFn.isConstOf ``LE.le do throwError "expected the three exact paid inequalities"
  let ha:=ht.getAppArgs
  let pa:=pt.getAppArgs
  let ca:=ct.getAppArgs
  let rhs:=ha[ha.size-1]!
  unless rhs.getAppFn.isConstOf ``HAdd.hAdd do throwError "expected exceptional plus ordinary"
  let ra:=rhs.getAppArgs
  pure (mkAppN (mkConst ``affine_error_combine)
    #[ha[ha.size-2]!,ra[ra.size-2]!,pa[pa.size-1]!,ca[ca.size-1]!,ra[ra.size-1]!,h,hp,hc])

variable {ι : Type*} [Fintype ι]

/-- The exact unchanged endpoint of the frozen ordinary contraction. -/
def GeometryErrorOrdinaryFrozenSpec
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)
    (hs : ContDiff ℝ ∞ logAnnulus)(C : ℝ) : Prop :=
  affine_error_frozen_spec (actual_geometry_error_ordinary_contraction (α:=ι)
    A degree windowDegree hc hs), C

attribute [local irreducible] geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild geometryJointErrorDatum geometryJointErrorWeight

section Source
variable (reflected : Bool) (s : Input ι) (Ψ : 𝓢(ℝ,ℂ))
  (Z amp ξ reserve t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
  (P : Finset (Ideal O)) (Qfix : Ideal O) (m : O)
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
variable (υ : GeometryLowFirstIndex (α:=ι) reflected s (1:Ideal O) (1:Ideal O)
    (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
    elementPool P→ Fin 3→ RayCharacter→ Character)
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "Sources" => GeometryJointErrorSourceIndex (α:=ι) reflected s 1 1 Z 1 ξ t hZ key P
local notation "Selected" => GeometryJointErrorSelectedIndex (α:=ι) reflected s 1 1 Z 1 amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂
local notation "phase" => fun c=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ c)
local notation "weight" => geometryJointErrorWeight (α:=ι) reflected s 1 1 Z 1 amp ξ reserve (9/4) t hZ key P υ
  1 (Real.logb Z (volume s)) phase hz₁ hz₂
local notation "datum" => geometryJointErrorDatum (α:=ι) reflected s 1 1 Z 1 amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂

set_option linter.defProp false in
set_option maxHeartbeats 10000 in
private def affine_error_source_raw_payment (l : Sources) :=
  actual_geometry_error_exceptional_selected_norm_le (ι:=ι) reflected s 1 1 Ψ
    Z 1 amp ξ reserve (9/4) t hZ key l.1 P l.2.1.val l.2.2.1 l.2.2.2.2
    (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂

set_option linter.defProp false in
set_option maxHeartbeats 10000 in
private def affine_error_source_selected_payment (l : Sources) :=
  affine_error_source (affine_error_source_raw_payment (ι:=ι) reflected s Ψ Z amp ξ reserve t hZ key
    P υ hz₁ hz₂ l), Qfix, m

set_option linter.defProp false in
set_option maxHeartbeats 15000 in
private def affine_error_joint_raw_payment :=
  affine_error_collect (fun l : Sources=>
    affine_error_source_selected_payment (ι:=ι) reflected s Ψ Z amp ξ reserve t hZ key
      P Qfix m υ hz₁ hz₂ l)

set_option linter.defProp false in
private def affine_error_point_block_transport (j : Selected) (χ : RayCharacter) :=
  congrArg (fun b=>‖weight j*b.value ballProfile‖)
    (geometry_joint_error_exceptional_datum_block (α:=ι) reflected s 1 1 Z 1 amp ξ reserve
      (9/4) t hZ key P υ hz₁ hz₂ j χ Qfix m)

set_option linter.defProp false in
set_option maxHeartbeats 15000 in
private def affine_error_joint_selected_payment (χ : Selected→ RayCharacter) :=
  affine_error_transport
    (affine_error_apply (affine_error_joint_raw_payment (ι:=ι) reflected s Ψ Z amp ξ reserve
      t hZ key P Qfix m υ hz₁ hz₂), χ),
    (fun j : Selected=>‖weight j*(mainExceptionalDatum (datum j) (χ j) Qfix m).block.value ballProfile‖),
    (fun j : Selected=>affine_error_point_block_transport (ι:=ι) reflected s Ψ Z amp ξ reserve
      t hZ key P Qfix m υ hz₁ hz₂ j (χ j))

private theorem affine_error_source_mass_sum :
    (∑l : Sources,∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass (ι:=ι)
      reflected s 1 1 Ψ Z 1 amp ξ reserve (9/4) t hZ key l.1 P l.2.1.val l.2.2.1
      l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t Qfix m χ₀)=
    geometryAffineErrorExceptionalMass s Ψ Z amp ξ reserve t t hZ reflected key P Qfix m υ := by
  simp only [GeometryJointErrorSourceIndex,GeometryLowFirstIndex,
    geometryAffineErrorExceptionalMass,Fintype.sum_sigma]

set_option linter.defProp false in
set_option maxHeartbeats 20000 in
def actual_geometry_error_exceptional_sum_payment (χ : Selected→ RayCharacter) :=
  affine_error_cap
    (affine_error_joint_selected_payment (ι:=ι) reflected s Ψ Z amp ξ reserve t hZ key
      P Qfix m υ hz₁ hz₂ χ),
    (geometryAffineErrorExceptionalMass s Ψ Z amp ξ reserve t t hZ reflected key P Qfix m υ),
    (affine_error_source_mass_sum (ι:=ι) reflected s Ψ Z amp ξ reserve t hZ key P Qfix m υ)

end Source
/-- Literal retained error sum. The first allocation weight is undivided and
its actual Fourier cardinality is retained. -/
def geometryAffineErrorRetainedContractSum
    (reflected : Bool)(s : Input ι)(Ψ : 𝓢(ℝ,ℂ))(Z amp ξ reserve t : ℝ)
    (hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=ι) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→ Fin 3→ RayCharacter→ Character) : ℂ :=
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let phase:=fun c=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ c)
  jointErrorRetained
    (fun q : GeometryLowFirstIndex (α:=ι) reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key=>liveIndices q.2.val)
    (fun q=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key t q)
    (fun q=>geometryBranch reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key q.1.val)
    (fun q=>geometryAllocationWeight reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) q.1.val q.2)
    ballProfile Z (3*amp) ξ reserve P υ
    (fun q p i=>geometryErrorFourierScale reflected s 1 1 Z 1 amp ξ reserve (9/4)
      (Fintype.card ι) hZ key q p.val i)

set_option maxHeartbeats 15000 in
private theorem geometry_affine_error_fourier_eq_original
    {β : Type}[Fintype β][DecidableEq β]
    (reflected : Bool)(s : Input β)(Z amp ξ reserve : ℝ)(hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (q : GeometryLowFirstIndex (α:=β) reflected s 1 1 (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key)
    (p : elementPool P)(i : Fin 3) :
    geometryErrorFourierScale reflected s 1 1 Z 1 amp ξ reserve (9/4) (Fintype.card β)
      hZ key q p.val i=
    firstErrorTailFourier (Fintype.card β) (9/4) (volume s)
      (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val)
      p.val (errorIndex i+1)
      (firstErrorTailRadius reflected (geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val)
        Z 1 (volume s) amp (frequencyLoss Z 32 ξ) reserve p.val (errorIndex i+1)) := by
  unfold geometryErrorFourierScale firstErrorTailFourier
  rw [div_mul_eq_div_div]
  rfl

set_option maxHeartbeats 15000 in
/-- Exact identity with the retained source used by the frozen affine budget. -/
theorem geometry_affine_error_retained_contract_sum_eq_original
    {β : Type}[Fintype β][DecidableEq β]
    (reflected : Bool)(s : Input β)(Ψ : 𝓢(ℝ,ℂ))(Z amp ξ reserve t : ℝ)
    (hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=β) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→ Fin 3→ RayCharacter→ Character) :
    geometryAffineErrorRetainedContractSum reflected s Ψ Z amp ξ reserve t hZ key P υ=
      geometryAffineErrorRetainedSum s Ψ Z amp ξ reserve t hZ reflected key P υ := by
  unfold geometryAffineErrorRetainedContractSum geometryAffineErrorRetainedSum
  simp only [geometry_affine_error_fourier_eq_original]

/-- Exact joint ordinary normalized intermediate and resulting retained bound. -/
def GeometryErrorSourceRetainedSpec
    (A degree windowDegree : ℕ)(reflected : Bool)(s : Input ι)(Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=ι) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→ Fin 3→ RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(exceptional C : ℝ) : Prop :=
    let selected:=GeometryJointErrorSelectedIndex (α:=ι) reflected s 1 1 Z 1 amp ξ reserve
      (9/4) t hZ key P υ hz₁ hz₂
    let d:=geometryJointErrorDatum (α:=ι) reflected s 1 1 Z 1 amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂
    let phase:=fun c=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ c)
    let coeff:=geometryJointErrorWeight (α:=ι) reflected s 1 1 Z 1 amp ξ reserve (9/4) t hZ key P υ
      1 (Real.logb Z (volume s)) phase hz₁ hz₂
    ∀(χ : selected→ RayCharacter)(E Hratio : ℤ→ℝ),
    (∀r∈secondRatioBins (fun j=>(d j).block),0≤ E r) →
    (∀r∈secondRatioBins (fun j=>(d j).block),0< Hratio r) →
    SecondNormalizedBound ballProfile degree windowDegree
      (fun j=>ordinarySecondDatum (d j) (χ j) Qfix m) coeff E Hratio →
    (56/(P.card:ℝ))*‖geometryAffineErrorRetainedContractSum reflected s Ψ Z amp ξ reserve t hZ key P υ‖≤
      exceptional+C*∑r∈secondRatioBins (fun j=>(d j).block),E r/(1+dyadicScale r)^A

set_option maxHeartbeats 15000 in
private theorem affine_error_paid_source_bridge
    (reflected : Bool)(s : Input ι)(Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (Qfix : Ideal O)(m : O)
    (υ : GeometryLowFirstIndex (α:=ι) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→ Fin 3→ RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (C cap : ℝ)(hordinary : GeometryErrorOrdinaryFrozenSpec (ι:=ι) A degree windowDegree hc hs C)
    (hcap : geometryAffineErrorExceptionalMass s Ψ Z amp ξ reserve t t hZ reflected key P Qfix m υ≤ cap) :
    GeometryErrorSourceRetainedSpec A degree windowDegree reflected s Ψ Z amp ξ reserve t hZ
      key P υ hz₁ hz₂ Qfix m cap C := by
  dsimp only [GeometryErrorSourceRetainedSpec]
  intro χ E Hratio hE hHratio hnorm
  let phase:=fun c=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ c)
  have ho:=affine_error_call hordinary, [reflected,s,(1:Ideal O),(1:Ideal O),Z,(1:ℝ),amp,
    ξ,reserve,(9/4:ℝ),t,hZ,key,P,υ,hz₁,hz₂,(1:ℝ),(Real.logb Z (volume s)),phase,
    χ,Qfix,m,E,Hratio,hE,hHratio,hnorm]
  have hp:=actual_geometry_error_exceptional_sum_payment (ι:=ι) reflected s Ψ Z amp ξ reserve
    t hZ key P Qfix m υ hz₁ hz₂ χ
  unfold geometryAffineErrorRetainedContractSum
  affine_error_exact affine_error_join ho, hp, hcap

/-- The paid source contract keeps the entire normalized input and exact
retained sum. Its scalar exceptional cap is supplied by a proved payment. -/
def GeometryErrorPaidSourceSpec
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)
    (hs : ContDiff ℝ ∞ logAnnulus)(C : ℝ) : Prop :=
  ∀(reflected : Bool)(s : Input ι)(Ψ : 𝓢(ℝ,ℂ))(Z amp ξ reserve t : ℝ)
    (hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))(Qfix : Ideal O)(m : O)
    (υ : GeometryLowFirstIndex (α:=ι) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→ Fin 3→ RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(cap : ℝ),
    geometryAffineErrorExceptionalMass s Ψ Z amp ξ reserve t t hZ reflected key P Qfix m υ≤ cap →
    GeometryErrorSourceRetainedSpec A degree windowDegree reflected s Ψ Z amp ξ reserve t hZ
      key P υ hz₁ hz₂ Qfix m cap C

set_option maxHeartbeats 15000 in
private theorem affine_error_frozen_to_paid
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (C : ℝ)(hordinary : GeometryErrorOrdinaryFrozenSpec (ι:=ι) A degree windowDegree hc hs C) :
    GeometryErrorPaidSourceSpec (ι:=ι) A degree windowDegree hc hs C := by
  dsimp only [GeometryErrorPaidSourceSpec]
  intro reflected s Ψ Z amp ξ reserve t hZ key P Qfix m υ hz₁ hz₂ cap hcap
  affine_error_exact affine_error_call (affine_error_paid_source_bridge (ι:=ι)),
    [reflected,s,Ψ,Z,amp,ξ,reserve,t,hZ,key,P,Qfix,m,υ,hz₁,hz₂,
      A,degree,windowDegree,hc,hs,C,cap,hordinary,hcap]

private theorem affine_error_uniform_map {Index : Type*}{p q : Index→ℝ→ Prop}
    (h : ∃C : ℝ,0< C ∧ ∀i,p i C)(map : ∀i C,p i C→ q i C) :
    ∃C : ℝ,0< C ∧ ∀i,q i C := by
  obtain ⟨C,hC,hp⟩:=h
  exact ⟨C,hC,fun i=>map i C (hp i)⟩

local syntax (name := affineErrorUniformPaid) "affine_error_uniform_paid " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorUniformPaid] private def elabAffineErrorUniformPaid : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let map ← elabTerm stx[3] none
  let ht ← instantiateMVars (←inferType h)
  unless ht.getAppFn.isConstOf ``Exists do throwError "expected the checked uniform constant"
  let ea:=ht.getAppArgs
  lambdaTelescope ea[ea.size-1]! fun cs body=>do
    unless cs.size=1 && body.getAppFn.isConstOf ``And do throwError "expected a positive uniform constant"
    let ba:=body.getAppArgs
    let p ← forallBoundedTelescope ba[ba.size-1]! (some 1) fun ix point=>do
      unless ix.size=1 do throwError "expected the finite original subset"
      mkLambdaFVars #[ix[0]!,cs[0]!] point
    let mt ← instantiateMVars (←inferType map)
    forallBoundedTelescope mt (some 3) fun ix result=>do
      unless ix.size=3 do throwError "expected subset, constant, and frozen proof"
      if result.containsFVar ix[2]!.fvarId! then throwError "paid source predicate depends on its proof"
      let index ← inferType ix[0]!
      let u ← getDecLevel index
      let q ← mkLambdaFVars #[ix[0]!,ix[1]!] result
      pure (mkAppN (mkConst ``affine_error_uniform_map [u]) #[index,p,q,h,map])

private theorem affine_error_cap_increase {a b c C x : ℝ}
    (hc : c≤ C)(hx : 0≤ x)(h : a≤ b+c*x) : a≤ b+C*x :=
  h.trans (add_le_add_right (mul_le_mul_of_nonneg_right hc hx) b)

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem affine_error_ratio_sum_nonneg (bins : Finset ℤ)(E : ℤ→ℝ)(A : ℕ)
    (hE : ∀r∈bins,0≤ E r) : 0≤∑r∈bins,E r/(1+dyadicScale r)^A :=
  Finset.sum_nonneg (fun r hr=>div_nonneg (hE r hr)
    (pow_nonneg (by linarith [dyadicScale_pos r]) A))

private theorem affine_error_uniform_constant {Index : Type*}[Fintype Index]
    {p : Index→ℝ→ Prop}(data : ∀i,∃c : ℝ,0≤ c ∧ p i c)
    (mono : ∀i {c C : ℝ},c≤ C→ p i c→ p i C) :
    ∃C : ℝ,0< C ∧ ∀i,p i C := by
  choose c hc hp using data
  let total:=1+∑i,c i
  have ht : 0< total := by
    have hh:=Finset.sum_nonneg (s:=Finset.univ) (fun i _=>hc i)
    dsimp only [total]
    linarith
  have hl (i : Index) : c i≤ total := by
    have hh:=Finset.single_le_sum (fun i _=>hc i) (Finset.mem_univ i)
    dsimp only [total]
    linarith
  exact ⟨total,ht,fun i=>mono i (hl i) (hp i)⟩

/- This module-local adapter only reads the frozen ordinary telescope and
its final scalar coefficient. It emits applications of the two elementary
lemmas above; every emitted proof is checked by Lean's ordinary kernel. -/
local syntax (name := affineErrorUniform) "affine_error_uniform " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorUniform] private def elabAffineErrorUniform : TermElab := fun stx _=>do
  let data ← elabTerm stx[1] none
  let dt ← inferType data
  forallBoundedTelescope dt (some 1) fun ix ex=>do
    unless ix.size=1 do throwError "expected one finite-family binder"
    let i:=ix[0]!
    unless ex.getAppFn.isConstOf ``Exists do throwError "expected an ordinary constant"
    let ea:=ex.getAppArgs
    lambdaTelescope ea[ea.size-1]! fun cs ab=>do
      unless cs.size=1 && ab.getAppFn.isConstOf ``And do throwError "expected nonnegative constant and endpoint"
      let c:=cs[0]!
      let aa:=ab.getAppArgs
      let pointSpec:=aa[aa.size-1]!
      let pred ← mkLambdaFVars #[i,c] pointSpec
      withLocalDeclD `upper (mkConst ``Real) fun upper=>do
        let leType ← mkAppM ``LE.le #[c,upper]
        withLocalDeclD `hle leType fun hle=>do
          withLocalDeclD `point pointSpec fun hp=>do
            let raised ← forallTelescope pointSpec fun xs body=>do
              unless xs.size≥5 && body.getAppFn.isConstOf ``LE.le do throwError "expected the frozen real endpoint"
              let ba:=body.getAppArgs
              let lhs:=ba[ba.size-2]!
              let rhs:=ba[ba.size-1]!
              unless rhs.getAppFn.isConstOf ``HAdd.hAdd do throwError "expected exceptional plus ordinary"
              let ra:=rhs.getAppArgs
              let exceptional:=ra[ra.size-2]!
              let product:=ra[ra.size-1]!
              unless product.getAppFn.isConstOf ``HMul.hMul do throwError "expected a scalar ordinary payment"
              let pa:=product.getAppArgs
              unless pa[pa.size-2]! == c do throwError "ordinary coefficient is not the quantified constant"
              let ratio:=pa[pa.size-1]!
              unless ratio.getAppFn.isConstOf ``Finset.sum do throwError "expected the exact ratio sum"
              let sa:=ratio.getAppArgs
              let bins:=sa[sa.size-2]!
              let E:=xs[xs.size-5]!
              let hE:=xs[xs.size-3]!
              let A ← lambdaTelescope sa[sa.size-1]! fun rs fraction=>do
                unless rs.size=1 && fraction.getAppFn.isConstOf ``HDiv.hDiv do throwError "expected one real ratio summand"
                let fa:=fraction.getAppArgs
                unless fa[fa.size-2]! == mkApp E rs[0]! do throwError "ratio numerator changed"
                let power:=fa[fa.size-1]!
                unless power.getAppFn.isConstOf ``HPow.hPow do throwError "expected a dyadic power"
                let xa:=power.getAppArgs
                let A:=xa[xa.size-1]!
                if A.containsFVar rs[0]!.fvarId! then throwError "ratio exponent depends on the bin"
                pure A
              let hn:=mkAppN (mkConst ``affine_error_ratio_sum_nonneg) #[bins,E,A,hE]
              let paid:=mkAppN hp xs
              let result:=mkAppN (mkConst ``affine_error_cap_increase)
                #[lhs,exceptional,c,upper,ratio,hle,hn,paid]
              mkLambdaFVars xs result
            let mono ← mkLambdaFVars #[i,c,upper,hle,hp] raised
            let index ← inferType i
            let cl ← mkAppM ``Fintype #[index]
            let inst ← synthInstance cl
            let u ← getDecLevel index
            pure (mkAppN (mkConst ``affine_error_uniform_constant [u]) #[index,inst,pred,data,mono])

set_option linter.defProp false in
set_option maxHeartbeats 15000 in
def uniform_actual_geometry_error_ordinary_contraction
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :=
  affine_error_uniform (fun T : Finset α=>actual_geometry_error_ordinary_contraction (α:=T)
    A degree windowDegree hc hs)

set_option linter.defProp false in
set_option maxHeartbeats 15000 in
def uniform_actual_geometry_error_paid_contraction
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :=
  affine_error_uniform_paid
    (uniform_actual_geometry_error_ordinary_contraction (α:=α) A degree windowDegree hc hs),
    (fun T : Finset α=>affine_error_frozen_to_paid (ι:=T) A degree windowDegree hc hs)

variable (rayM : Ideal O) [NeZero rayM]
local instance affineErrorContractionFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤ H)

set_option maxHeartbeats 15000 in
/-- Genuine exceptional payment and the original retained error identity are
composed with the ordinary normalized intermediate contract. -/
theorem actual_affine_error_retained_contraction
    (A ordinaryDegree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤ Ideal.span {(72:O)})
    (m : O)(hm : m≠0)(hml : goodLambda∣m)(hm2 : (2:O)∣m) :
    ∃Ce : ℝ,0< Ce ∧ ∃Sp : Finset (ℕ×ℕ),∃exceptionalDegree : ℕ,
    ∃Co : ℝ,0< Co ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(T : Finset α)(η₀ : Character)(θ : T→ RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=η)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) →
      (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B →
      let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta:=Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i))
      let amp:=Cycle61.Arithmetic.amp beta
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let μ:=geometryLossUnit 1 εaffine
      ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ)
        (υ : GeometryLowFirstIndex (α:=T) reflected s (1:Ideal O) (1:Ideal O)
          (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
          elementPool P→ Fin 3→ RayCharacter→ Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T := Classical.decEq T;
      GeometryErrorSourceRetainedSpec (ι:=T) A ordinaryDegree windowDegree reflected s Ψ
        Z amp (μ/64) (μ/8) firstHeight hZ key P υ
        (affine_error_plain_zero p 0) (affine_error_plain_zero p 1) Qfix m
        (Ce*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
          (1+‖firstHeight‖)^exceptionalDegree*Z^(-(1/100:ℝ))) Co := by
  let ordinary:=uniform_actual_geometry_error_paid_contraction (α:=α)
    A ordinaryDegree windowDegree hc hs
  let Co:=affine_error_choice ordinary, 0
  have hCo:=affine_error_choice ordinary, 1
  have hordinary:=affine_error_choice ordinary, 2
  obtain ⟨Ce,hCe,Sp,exceptionalDegree,hexceptional⟩:=actual_affine_error_exceptional_payment (α:=α)
    rayM H hH Sbad hbad W hW hWs η εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2
  refine ⟨Ce,hCe,Sp,exceptionalDegree,Co,hCo,?_⟩
  filter_upwards [hexceptional] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone s beta amp P μ Ψ reflected key firstHeight
    υ hυ
  letI : DecidableEq T := Classical.decEq T
  have he:=hz.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone Ψ reflected key firstHeight firstHeight υ hυ
  affine_error_exact affine_error_call (affine_error_apply hordinary, T),
    [reflected,s,Ψ,Z,amp,(μ/64),(μ/8),firstHeight,hZ,key,P,Qfix,m,υ,
      (affine_error_plain_zero p 0),(affine_error_plain_zero p 1),
      (Ce*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
        (1+‖firstHeight‖)^exceptionalDegree*Z^(-(1/100:ℝ))),he]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_error_source_selected_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_error_source_raw_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_error_joint_raw_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_error_joint_selected_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_sum_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_actual_geometry_error_ordinary_contraction

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_error_retained_contraction

#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_error_paid_source_bridge

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_error_retained_contract_sum_eq_original

#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_error_frozen_to_paid
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_actual_geometry_error_paid_contraction

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorContraction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorAbsoluteBox; sha256 9167335e46fa92545002880cc644114202d605d8546f2d391855202f2e1aaaf6 -/
section
                                                             
                                                      
                                                              
                                                          

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle61Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput
local notation "O" => HeckeFamily.O

theorem actual_geometry_error_radius_interval {α : Type}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(M Z ξ a reserve B : ℝ)
    (hZ : 1< Z)(hK : 0< Z^M)(hB : 0≤ B)
    (hM : |M|≤ B)(hA : |Real.logb Z (volume s)|≤ B)(ha : |a|≤ B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤ B)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key))
    (p : O)(hp : p≠0)(k : ℕ)(hk : 1≤ k) :
    Z^(-(16*B))≤ firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
      Z M (volume s) a (frequencyLoss Z 32 ξ) reserve p k ∧
    firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
      Z M (volume s) a (frequencyLoss Z 32 ξ) reserve p k≤ Z^(16*B) := by
  let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
  let l := geometryFirstLabel s R seed (Z^M) Z ξ hK key j
  let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
  let A := Real.logb Z (volume s)
  have hv (i : Fin 5) : 0≤ v i ∧ v i≤ B := by
    have hh := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val i
    exact ⟨Real.logb_nonneg hZ hh.1,
      (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hh.1)).mpr hh.2⟩
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (CenteredMomentAmplificationChildInput.volume_pos s)).symm
  have he : Real.logb Z (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=v 4 := by
    change Real.logb Z (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=
      Real.logb Z (Ideal.span {primeSubsetGenerator (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm
    rw [first_projector_span]
  have hR : Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm=v 3 := rfl
  have hC : Real.logb Z (l.1.1.absNorm:ℝ)=v 0 := rfl
  have hD : Real.logb Z (l.1.2.absNorm:ℝ)=v 1 := rfl
  have hp0 : 0≤ Real.logb Z (normValue p) :=
    Real.logb_nonneg hZ (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hmove : errorMoving p Z k≤2*errorRemoval p Z k := by
    have hkR : (1:ℝ)≤ k := by exact_mod_cast hk
    unfold errorMoving errorRemoval
    split_ifs <;> nlinarith
  have hrem0 : 0≤ errorRemoval p Z k := by unfold errorRemoval; positivity
  rw [hV,actual_error_radius_power reflected l src.hC src.hD src.sameSupport
    Z M A a (frequencyLoss Z 32 ξ) reserve p k hZ]
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,hR,he,hC,hD]
  all_goals
    have hm0 (i j : Fin 5) : 0≤ max (v i-v j-2*errorRemoval p Z k+errorMoving p Z k) 0 := le_max_right _ _
    have hmB (i j : Fin 5) : max (v i-v j-2*errorRemoval p Z k+errorMoving p Z k) 0≤ B :=
      max_le (by linarith [(hv i).2,(hv j).1]) hB
    constructor
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [(abs_le.mp hA).1,(abs_le.mp hM).2,(abs_le.mp ha).1,
        (abs_le.mp hω).1,(hv 0).2,(hv 1).2,(hv 3).1,(hv 4).1,hm0 0 1,hm0 1 0]
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [(abs_le.mp hA).2,(abs_le.mp hM).1,(abs_le.mp ha).2,
        (abs_le.mp hω).2,(hv 0).1,(hv 1).1,(hv 3).2,(hv 4).2,hmB 0 1,hmB 1 0]

def geometryErrorAbsoluteBox (Z : ℝ)(N : ℕ)(B loss b : ℝ) : Finset (Fin 4→ℤ) :=
  secondAbsoluteBox Z (16*B) (16*B) (B+loss) (18*B+loss) (b^(2*N))

/-- The Fourier expression retains the actual source slot count. Only its
fixed polynomial envelope uses the ambient cap. -/
theorem actual_geometry_error_cutoff_cap {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(B loss b : ℝ)(_hB : 0≤ B)(hloss : 0≤ loss)(hb : 1≤ b)
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(Z M amp ξ reserve _t : ℝ)(hZ : 1< Z)
    (hn : Fintype.card α≤ N)(hξ : ξ≤ loss)(hV : volume s≤ Z^B)
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O)(hp : p≠0)(i : Fin 3)
    (hrad : Z^(-(16*B))≤ geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i) :
    frequencyRadius (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b
      (Fintype.card α) hZ bin q p i) Z ξ≤ b^(2*N)*Z^(18*B+loss) := by
  let I:=geometryColumnIdeal reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  have hI : (1:ℝ)≤ I.absNorm := norm_ge_one _ (allocation_ne s I q.2)
  have hpN : (1:ℝ)≤(normValue p)^(errorIndex i+1) :=
    one_le_pow₀ (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hb0 : 0< b:=zero_lt_one.trans_le hb
  have hv0 := volume_pos s
  have hi0 := zero_lt_one.trans_le hI
  have hp0 := zero_lt_one.trans_le hpN
  have hnum : b^(Fintype.card α)*volume s/((I.absNorm:ℝ)*(normValue p)^(errorIndex i+1))
      ≤ b^N*Z^B := by
    calc
      _≤ b^(Fintype.card α)*volume s := div_le_self (by positivity)
        (one_le_mul_of_one_le_of_one_le hI hpN)
      _≤ b^N*Z^B := mul_le_mul (pow_le_pow_right₀ hb hn) hV (volume_pos s).le (by positivity)
  have hnum0 : 0≤ b^(Fintype.card α)*volume s/((I.absNorm:ℝ)*(normValue p)^(errorIndex i+1)) := by positivity
  unfold frequencyRadius geometryErrorFourierScale
  change (_ / geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i)*Z^(ξ/2)≤ _
  calc
    _≤((b^N*Z^B)^2/Z^(-(16*B)))*Z^(ξ/2) := mul_le_mul_of_nonneg_right
      (div_le_div₀ (by positivity) (pow_le_pow_left₀ hnum0 hnum 2)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hrad) (Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
    _=b^(2*N)*Z^(18*B+ξ/2) := by
      rw [mul_pow,←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le,
        mul_div_assoc,←Real.rpow_sub (zero_lt_one.trans hZ),mul_assoc,
        ←Real.rpow_add (zero_lt_one.trans hZ)]
      rw [←pow_mul,show N*2=2*N by omega]
      congr 1
      ring_nf
    _≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity)

/-- Supported extraction retains the exact prime power denominator; it can
only decrease the coarse source envelope. -/
theorem eventual_geometry_error_child_source_cap (N : ℕ)(b bs loss : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hloss : 0< loss) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (s : Input α)(A : ℝ),Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^A →
      ∀(C R : Ideal O)(B₁ : actualAllocations s.pools C)(τ : Character)(t : ℝ),
      frozenCoefficient B₁.val C R s.ν s.W s.P≠0 →
      ∀(p : O),p≠0 → ∀k : ℕ,
      (∀i I,I∈(child s C R B₁ τ t).slots i→ IsCoprime (Ideal.span {p}) I) →
      ∀(Bp : actualAllocations (child s C R B₁ τ t).pools ((Ideal.span {p})^k))
        (υ : Character)(v : ℝ),
      sourceRadius (twiceChild s C R B₁ τ t (Ideal.span {p}) k Bp υ v)≤ Z^(A+loss) := by
  filter_upwards [(tendsto_rpow_atTop hloss).eventually
    (eventually_ge_atTop (geometry N b bs bs)),eventually_gt_atTop (1:ℝ)] with Z hg hZ
  refine ⟨hZ,?_⟩
  intro α _ _ s A hn hend hV C R B₁ τ t hf p hp k hcop Bp υ v
  have hc:=twice_caps N b bs bs hb hbs hbs s hn hend C R B₁ τ t hf
    (Ideal.span {p}) (Ideal.span_singleton_eq_bot.not.mpr hp) k hcop Bp υ v
  have hden := one_le_mul_of_one_le_of_one_le (norm_ge_one C (allocation_ne s C B₁))
    (one_le_pow₀ (n:=k) (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp)))
  have hrad : sourceRadius (twiceChild s C R B₁ τ t (Ideal.span {p}) k Bp υ v)≤
      geometry N b bs bs*volume s/((C.absNorm:ℝ)*((Ideal.span {p}).absNorm:ℝ)^k) := by
    simpa only [mul_div_assoc] using hc.2.2.2
  calc
    _≤ geometry N b bs bs*volume s := hrad.trans (div_le_self
      (mul_nonneg ((geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)) (volume_pos s).le) hden)
    _≤ Z^loss*Z^A := mul_le_mul hg hV (volume_pos s).le (Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
    _=Z^(A+loss) := by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]

/-- One fixed box covers all literal extracted sources, allocations,
heights and second blocks. The Fourier scale uses card α, not its cap N. -/
theorem eventual_actual_geometry_error_absolute_box (N : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hb : 1≤ b)(hbs : 1≤ bs)
    (hξ : ξ≤ loss)(hε : 0<ε) :
    ∃Cb : ℝ,0< Cb ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ((geometryErrorAbsoluteBox Z N B loss b).card:ℝ)≤ Cb*Z^ε ∧
      ∀{α : Type}[Fintype α][DecidableEq α](reflected : Bool)(s : Input α)(R seed : Ideal O)
        (M amp reserve t : ℝ)(hZ : 1< Z),
      Fintype.card α≤ N → Endpoints b bs bs s → Squarefree seed →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      |Real.logb Z (volume s)|≤ B → |M|≤ B → |amp|≤ B →
      |frequencyLoss Z 32 ξ+reserve|≤ B →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0 →
      ∀(p : O),p≠0 → ∀(i : Fin 3),
      (∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I) →
      ∀(Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ),
      let extracted:=geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v
      let rad:=geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i
      let fourier:=geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ bin q p i
      let Rsecond:=(R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
      Z^(-(16*B))≤ rad ∧ rad≤ Z^(16*B) ∧ sourceRadius extracted≤ Z^(B+loss) ∧
        frequencyRadius fourier Z ξ≤ b^(2*N)*Z^(18*B+loss) ∧
        ∀z : ActualSecondBlockIndex extracted Rsecond q.1.val.2.1.val rad fourier Z ξ,
          actualSecondDyad extracted Rsecond q.1.val.2.1.val rad fourier Z ξ z∈
            geometryErrorAbsoluteBox Z N B loss b := by
  have hCr : 0< b^(2*N):=pow_pos (zero_lt_one.trans_le hb) _
  obtain ⟨Cb,hCb,hcard⟩:=second_absolute_envelope_subpower
    (16*B) (16*B) (B+loss) (18*B+loss) (b^(2*N)) ε
    (by positivity) (by positivity) (by positivity) (by positivity) hCr hε
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hcard,eventual_geometry_error_child_source_cap N b bs loss hb hbs hloss]
    with Z hc hs
  refine ⟨hs.1,?_,?_⟩
  · simpa only [geometryErrorAbsoluteBox,second_absolute_box_card] using hc
  intro α _ _ reflected s R seed M amp reserve t hZ hn hend hseed hz₁ hz₂
    hsource hA hM ha hω bin q hf p hp i hcop Bp υ v extracted rad fourier Rsecond
  have hz0 := zero_lt_one.trans hZ
  have hK := Real.rpow_pos_of_pos hz0 M
  have hV : volume s≤ Z^B :=
    (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hr := actual_geometry_error_radius_interval reflected s R seed M Z ξ amp reserve B
    hZ hK hB hM hA ha hω hseed hz₁ hz₂ hsource bin q.1.val p hp (errorIndex i+1)
    (Nat.succ_le_succ (Nat.zero_le _))
  have hr' : Z^(-(16*B))≤ rad ∧ rad≤ Z^(16*B) := by
    simpa only [rad,geometryErrorSourceRadius,actual_geometry_error_tail_radius] using hr
  have hcut := actual_geometry_error_cutoff_cap N B loss b hB hloss.le hb
    reflected s R seed Z M amp ξ reserve t hZ hn hξ hV bin q p hp i hr'.1
  have hextracted : sourceRadius extracted≤ Z^(B+loss) :=
    hs.2 s B hn hend hV _ R q.2 _ t hf p hp (errorIndex i+1) hcop
      (errorActiveAllocation _ _ Bp) υ v
  refine ⟨hr'.1,hr'.2,hextracted,hcut,?_⟩
  intro z
  have hseed1 := actual_first_live_squarefree
    (geometryFirstSource s R seed (Z^M) Z ξ hK bin) (fun _=>logAnnulus) q.1.val q.1.property
  have hradpos := actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ bin q p i
  let d:=actualSecondBlockDatum _ extracted Rsecond q.1.val.2.1.val hseed1 hz₁ hz₂ rad fourier Z ξ hradpos z
  have hg:=actual_retained_block_gates _ extracted Rsecond q.1.val.2.1.val hseed1 hz₁ hz₂ rad fourier Z ξ hradpos z
  apply Fintype.mem_piFinset.mpr
  intro c
  exact actual_second_dyads_absolute Z (16*B) (16*B) (B+loss) (18*B+loss) (b^(2*N)) hZ.le
    (by positivity) (by positivity) (by positivity) (by positivity) hCr
    d.C d.D d.hC d.hD d.sameSupport d.inactive rad (frequencyRadius fourier Z ξ) (sourceRadius extracted)
    hradpos hr'.1 hr'.2 hcut hextracted (hg.2.2.1.trans hextracted) (hg.2.2.2.trans hextracted) z.2.2 c

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_radius_interval
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_cutoff_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_geometry_error_child_source_cap

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_absolute_box

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorAbsoluteBox -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighSourceCaps; sha256 206233a54e573c8c55f06cf5305ee874e1b0370f85b79831d6cb5ac6ea7fe979 -/
section
                                                          
                                                      

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentLogDyadic
open RayFourExpansion CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O

/-- Both first ideals retain the original source-radius cap in either
physical orientation. No allocation or ordinary-energy estimate is used. -/
theorem actual_geometry_main_first_norm_caps {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(hZ : 1≤ Z)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^(3:ℝ))(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    (l.1.1.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤ Z^(4:ℝ) := by
  have hc:=(actual_geometry_norm_caps s R seed K Z ξ 3 hs hz₁ hz₂ hsource j.1.val 0).2
  have hd:=(actual_geometry_norm_caps s R seed K Z ξ 3 hs hz₁ hz₂ hsource j.1.val 1).2
  have h34 : Z^(3:ℝ)≤ Z^(4:ℝ):=Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  exact ⟨hc.trans h34,hd.trans h34⟩

/-- The canonical ordinary datum retains the original ideals. Its true
first-child support, rather than the high-density ceiling, caps both
second ideals. Constants precede all labels, allocations and heights. -/
theorem eventual_actual_geometry_main_high_source_caps (N : ℕ)(b bs loss : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hloss : 0< loss)(hloss1 : loss≤1) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(M amp ξ reserve t : ℝ)(hZ : 1< Z),
      Fintype.card α≤ N → Endpoints b bs bs s → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤ Z^(3:ℝ) → volume s≤ Z^(3:ℝ) →
      ∀(bin : ℤ×(Fin 5→ℤ))(χ : RayCharacter)(Q : Ideal O)(m : O)
        (j : GeometryMainSecondIndex reflected s R seed Z M amp ξ reserve b t (Fintype.card α) hZ bin),
      frozenCoefficient j.1.2.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1.1.val) R s.ν s.W s.P≠0 →
      let l:=geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1.1.val
      let d:=geometryMainOrdinaryDatum reflected s R seed Z M amp ξ reserve b t (Fintype.card α) hZ bin hz₁ hz₂ χ Q m j
      (l.1.1.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤ Z^(4:ℝ) ∧
        (d.C.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (d.D.absNorm:ℝ)≤ Z^(4:ℝ) := by
  filter_upwards [eventual_geometry_child_source_cap N b bs loss hb hbs hloss] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed M amp ξ reserve t hZ hn hend hseed hz₁ hz₂ hsource hvolume bin χ Q m j hf l d
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  have hfirst:=actual_geometry_main_first_norm_caps s R seed (Z^M) Z ξ hK hZ.le hseed hz₁ hz₂ hsource bin j.1.1.val
  have hchild:=hz.2 s 3 hn hend hvolume
    (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.1.1.val) R j.1.2
    (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin j.1.1.val) t hf
  have hchild4 : sourceRadius (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK bin t j.1)≤ Z^(4:ℝ) :=
    hchild.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  let label:=geometryFirstLabel s R seed (Z^M) Z ξ hK bin j.1.1.val
  let Kmain:=firstMainRadius reflected (Z^M) (volume s) Z ξ (3*amp) reserve label
  let Tsec:=firstMainFourierScale reflected (Z^M) (volume s) Z ξ (3*amp) reserve b (Fintype.card α) label
  have hseed1:=actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
    (fun _=>logAnnulus) j.1.1.val j.1.1.property
  have hg:=actual_retained_block_gates (liveIndices j.1.2.val)
    (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK bin t j.1)
    (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.1.1.val) j.1.1.val.2.1.val
    hseed1 hz₁ hz₂ Kmain Tsec Z ξ
    (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*amp) reserve (zero_lt_one.trans hZ) label) j.2
  exact ⟨hfirst.1,hfirst.2,hg.2.2.1.trans hchild4,hg.2.2.2.trans hchild4⟩

/-- Original full-value nonzero selection supplies the supported first
allocation. No nonzero ordinary restricted block is required. -/
theorem eventual_actual_geometry_main_nonzero_high_source_caps (N : ℕ)(b bs loss : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hloss : 0< loss)(hloss1 : loss≤1) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(M amp ξ reserve t : ℝ)(hZ : 1< Z),
      Fintype.card α≤ N → Endpoints b bs bs s → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤ Z^(3:ℝ) → volume s≤ Z^(3:ℝ) →
      ∀(bin : ℤ×(Fin 5→ℤ))(χ : RayCharacter)(Q : Ideal O)(m : O)
        (j : geometryMainNonzeroBlocks reflected s R seed Z M amp ξ reserve b t (Fintype.card α) hZ bin hz₁ hz₂),
      let l:=geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.val.1.1.val
      let d:=geometryMainOrdinaryDatum reflected s R seed Z M amp ξ reserve b t (Fintype.card α) hZ bin hz₁ hz₂ χ Q m j.val
      (l.1.1.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤ Z^(4:ℝ) ∧
        (d.C.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (d.D.absNorm:ℝ)≤ Z^(4:ℝ) := by
  filter_upwards [eventual_actual_geometry_main_high_source_caps N b bs loss hb hbs hloss hloss1] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed M amp ξ reserve t hZ hn hend hseed hz₁ hz₂ hsource hvolume bin χ Q m j
  exact hz.2 reflected s R seed M amp ξ reserve t hZ hn hend hseed hz₁ hz₂ hsource hvolume bin χ Q m j.val
    (Finset.mem_filter.mp j.property).2.1

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_first_norm_caps
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_high_source_caps
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_nonzero_high_source_caps

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighSourceCaps -/
