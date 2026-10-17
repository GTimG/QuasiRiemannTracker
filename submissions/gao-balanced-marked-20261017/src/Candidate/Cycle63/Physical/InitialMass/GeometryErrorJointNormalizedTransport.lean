/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorOrdinaryContraction
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorNormalizedMenuPayment
import Candidate.Cycle63.Physical.InitialMass.SecondFullNormalizedContraction

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
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
open CenteredMomentSecondHeightFamily
open Cycle63FinalNatural Cycle63Moment Cycle63FinalError
open CenteredMomentCommonPairedSource
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable
local instance errorJointNormalizedSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := errorNormalizedFullFamilySumDecidableEq
universe u v

theorem error_normalized_column_ideal_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (R seed L : Ideal O) (z : O) (h : C=D) :
    normalizedColumn s C hC R seed L z=normalizedColumn s D hD R seed L z := by
  cases h
  rfl

/-- Pointwise column equality and scalar equality determine the positive label sum. -/
theorem error_normalized_label_congr {ι β : Type*} [Fintype ι] [Fintype β]
    [DecidableEq ι] [DecidableEq β] (d : SecondInputDatum ι) (g : SecondInputDatum β)
    (hb : d.block=g.block)
    (hv : CenteredMomentExceptionalAmplitudePair.volume d.input.toData=
      CenteredMomentExceptionalAmplitudePair.volume g.input.toData)
    (hC : d.C=g.C) (hD : d.D=g.D) (hτ : d.τ=g.τ) (ht : d.input.t=g.input.t)
    (hc : ∀η v C (h : Supported C) L z,
      normalizedColumn (withHeight d.input η v) C h d.R d.seed L z =
      normalizedColumn (withHeight g.input η v) C h g.R g.seed L z)
    (side : Bool) (w : ℂ) (t u : ℝ) :
    secondNormalizedLabelSum side d w t u=secondNormalizedLabelSum side g w t u := by
  unfold secondNormalizedLabelSum
  generalize hd : d.block=bd
  generalize hg : g.block=bg
  have hbg : bd=bg := hd.symm.trans (hb.trans hg)
  cases hbg
  simp only [hv,hτ,ht]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [hc]
    exact congrArg (fun c : ℂ=>‖c‖^2)
      (error_normalized_column_ideal_congr _ _ _ _ _ _ _ _ _ hC)
  · rw [hc]
    exact congrArg (fun c : ℂ=>‖c‖^2)
      (error_normalized_column_ideal_congr _ _ _ _ _ _ _ _ _ hD)

/-- The equality-instance cast preserves volume before any source is specialized. -/
theorem error_normalized_cast_volume {ι : Type*} [Fintype ι]
    (eqι : DecidableEq ι) (d : @SecondInputDatum ι _ eqι) :
    (letI := Classical.decEq ι; CenteredMomentExceptionalAmplitudePair.volume
      (cast (congrArg (fun eq=>@SecondInputDatum ι _ eq)
        (Subsingleton.elim eqι (Classical.decEq ι))) d).input.toData) =
      (letI := eqι; CenteredMomentExceptionalAmplitudePair.volume d.input.toData) := by
  have he : eqι=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  rfl

/-- The stored instance cast and embedding preserve the source volume. -/
theorem error_normalized_cast_image_volume {ι β : Type*}
    [Fintype ι] [Fintype β] (eqι : DecidableEq ι)
    (d : @SecondInputDatum ι _ eqι) (e : ι↪β) :
    CenteredMomentExceptionalAmplitudePair.volume
      ((cast (congrArg (fun eq=>@SecondInputDatum ι _ eq)
        (Subsingleton.elim eqι (Classical.decEq ι))) d).image e).input.toData =
      (letI := eqι; CenteredMomentExceptionalAmplitudePair.volume d.input.toData) := by
  exact (second_datum_image_volume e _).trans (error_normalized_cast_volume eqι d)

/-- Share the raw source datum in the statement and its ordinary kernel proof. -/
private def buildErrorJointVolume (g : Lean.Syntax) (wantType : Bool) :
    Lean.Elab.Term.TermElabM Lean.Expr := do
  let dg ← Lean.Elab.Term.elabTerm g none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let dg ← Lean.instantiateMVars dg
  let some image ← Lean.Meta.unfoldDefinition? dg true
    | Lean.throwError "expected the stored joint datum definition"
  let ia := image.getAppArgs
  unless image.getAppFn.isConstOf ``SecondInputDatum.image && ia.size=6 do
    Lean.throwError "expected the stored datum image"
  let ca := ia[5]!.getAppArgs
  unless ca.size=4 do Lean.throwError "expected the canonical instance cast"
  let rt ← Lean.Meta.inferType ca[3]!
  Lean.Meta.withLetDecl `rawDatum rt ca[3]! fun raw => do
    let proof ← Lean.Meta.mkAppOptM ``error_normalized_cast_image_volume
      #[some ca[0]!,some ia[1]!,some ca[1]!,some ia[3]!,some ca[2]!,some raw,some ia[4]!]
    let result ← if wantType then Lean.Meta.inferType proof else pure proof
    Lean.Meta.mkLetFVars #[raw] result

elab "errorJointVolume%(" g:term ")" : term =>
  buildErrorJointVolume g false
elab "errorJointVolumeType%(" g:term ")" : term =>
  buildErrorJointVolume g true

/-- Emit an explicitly typed proof constant through Lean's checked declaration path.
The type and ordinary proof are captured together; no kernel checks are bypassed. -/
elab "checked_error_proof " name:ident binders:bracketedBinder* " := " proof:term : command => do
  let declName := (← Lean.getCurrNamespace) ++ name.getId
  Lean.Elab.Command.runTermElabM fun vars =>
    Lean.Elab.Term.elabBinders binders fun xs => do
      let value ← Lean.Elab.Term.elabTerm proof none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let value ← Lean.instantiateMVars value
      let value ← Lean.Meta.mkLambdaFVars xs value
      let value ← Lean.Meta.mkLambdaFVars vars value (usedOnly := true)
      let value ← Lean.Elab.Term.levelMVarToParam value
      let value ← Lean.instantiateMVars value
      let type ← Lean.Meta.inferType value
      unless ← Lean.Meta.isProp type do Lean.throwError "expected a theorem proposition"
      let params := (Lean.collectLevelParams (Lean.collectLevelParams {} type) value).params.toList
      let es := ShareCommon.shareCommon' #[type,value]
      let decl := Lean.Declaration.defnDecl { name := declName, levelParams := params, type := es[0]!, value := es[1]!, hints := .regular 1, safety := .safe }
      Lean.Elab.Term.ensureNoUnassignedMVars decl
      let auxName := Lean.mkPrivateName (← Lean.getEnv) (declName ++ `_proof)
      let preDef : Lean.Elab.PreDefinition := { ref := name, kind := .«def», levelParams := params, modifiers := { visibility := .«private» }, declName := auxName, binders := .missing, type := es[0]!, value := es[1]!, termination := default }
      Lean.Elab.addNonRec ((← Lean.getLCtx),(← Lean.Meta.getLocalInstances)) preDef
      let info ← Lean.getConstInfo auxName
      let publicDecl := Lean.Declaration.defnDecl { name := declName, levelParams := info.levelParams, type := info.type, value := Lean.mkConst auxName (info.levelParams.map Lean.mkLevelParam), hints := .regular 1, safety := .safe }
      Lean.Elab.Term.ensureNoUnassignedMVars publicDecl
      Lean.addDecl publicDecl


/-- Use the frozen projection interfaces and their literal carrier instances. -/
elab "errorJointFieldLabel%(" g:term "," χ:term "," Q:term "," m:term "," side:term "," w:term "," t:term "," u:term ")" : term => do
  let dg ← Lean.Elab.Term.elabTerm g none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let dg ← Lean.instantiateMVars dg
  let args := dg.getAppArgs
  let levels := dg.getAppFn.constLevels!
  let chr ← Lean.Elab.Term.elabTerm χ none
  let qr ← Lean.Elab.Term.elabTerm Q none
  let mr ← Lean.Elab.Term.elabTerm m none
  let sr ← Lean.Elab.Term.elabTerm side none
  let wr ← Lean.Elab.Term.elabTerm w none
  let tt ← Lean.Elab.Term.elabTerm t none
  let uu ← Lean.Elab.Term.elabTerm u none
  let hb := Lean.mkAppN (Lean.mkConst ``geometry_joint_error_ordinary_datum_block levels) (args++#[chr,qr,mr])
  let hbt ← Lean.Meta.whnf (← Lean.Meta.inferType hb)
  let ea := hbt.getAppArgs
  unless hbt.getAppFn.isConstOf ``Eq && ea.size=3 do Lean.throwError "expected the frozen block equality"
  let ga := ea[1]!.getAppArgs
  let ra := ea[2]!.getAppArgs
  unless ga.size=4 && ra.size=4 do Lean.throwError "expected the exact datum block projections"
  let fields := Lean.mkAppN (Lean.mkConst ``geometry_joint_error_datum_fields levels) args
  let hC ← Lean.Meta.mkAppM ``And.left #[fields]
  let tail ← Lean.Meta.mkAppM ``And.right #[fields]
  let hD ← Lean.Meta.mkAppM ``And.left #[tail]
  let tail ← Lean.Meta.mkAppM ``And.right #[tail]
  let hτ ← Lean.Meta.mkAppM ``And.left #[tail]
  let ht ← Lean.Meta.mkAppM ``And.right #[tail]
  let hv := Lean.mkAppN (Lean.mkConst `OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_datum_volume levels) args
  let hc := Lean.mkAppN (Lean.mkConst ``geometry_joint_error_datum_column levels) args
  Lean.Meta.mkAppOptM ``error_normalized_label_congr
    #[some ga[0]!,some ra[0]!,some ga[1]!,some ra[1]!,some ga[2]!,some ra[2]!,
      some ga[3]!,some ra[3]!,some hb,some hv,some hC,some hD,some hτ,some ht,some hc,
      some sr,some wr,some tt,some uu]

/-- Read the exact checked sigma RHS, without reconstructing a datum record. -/
elab "errorJointRawSum%(" proof:term ")" : term => do
  let e ← Lean.Elab.Term.elabTerm proof none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType (← Lean.instantiateMVars e))
  let args := ty.getAppArgs
  unless ty.getAppFn.isConstOf ``Eq && args.size=3 do
    Lean.throwError "expected an exact normalized-sum equality"
  pure args[2]!

/-- Extract one literal summand from the checked raw sigma RHS. -/
elab "errorJointRawSource%(" proof:term "," source:term ")" : term => do
  let e ← Lean.Elab.Term.elabTerm proof none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType (← Lean.instantiateMVars e))
  let rhs := ty.getAppArgs[2]!
  let args := rhs.getAppArgs
  unless rhs.getAppFn.isConstOf ``Finset.sum && args.size=5 do
    Lean.throwError "expected the literal source sum"
  let l ← Lean.Elab.Term.elabTerm source none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  pure (Lean.mkApp args[4]! (← Lean.instantiateMVars l)).headBeta

/-- Transport positive source sums without a source-label cardinality. -/
theorem error_normalized_effective_sigma_congr
    {α S : Type*} [Fintype α] [DecidableEq α] [Fintype S]
    {B : S→Type*} [∀s,Fintype (B s)]
    {ι : S→Type*} [∀s,Fintype (ι s)] [∀s,DecidableEq (ι s)]
    (g : Sigma B→SecondInputDatum α) (d : (s : S)→B s→SecondInputDatum (ι s))
    (w : Sigma B→ℂ) (W : 𝓢(ℝ,ℂ))
    (hb : ∀j : Sigma B,(g j).block=(d j.1 j.2).block)
    (hl : ∀(j : Sigma B) side c t u,
      secondNormalizedLabelSum side (g j) c t u=
      secondNormalizedLabelSum side (d j.1 j.2) c t u)
    (side : Bool) (t u : ℝ) :
    secondNormalizedSum side g
      (secondEffectiveWeight (fun j=>(g j).block) w W) t u=
    ∑s,secondNormalizedSum side (d s)
      (secondEffectiveWeight (fun b=>(d s b).block) (fun b=>w ⟨s,b⟩) W) t u := by
  rw [second_normalized_sum_labels,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  rw [second_normalized_sum_labels]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [secondEffectiveWeight]
  simp only [hb ⟨s,b⟩]
  exact hl ⟨s,b⟩ side _ t u

/-- A source-sum envelope controls every ratio fiber with H=1. -/
theorem error_normalized_bound_of_source_sum
    {α S : Type*} [Fintype α] [DecidableEq α] [Fintype S]
    {B : S→Type*} [∀s,Fintype (B s)]
    {ι : S→Type*} [∀s,Fintype (ι s)] [∀s,DecidableEq (ι s)]
    (g : Sigma B→SecondInputDatum α) (d : (s : S)→B s→SecondInputDatum (ι s))
    (w : Sigma B→ℂ) (W : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ) (E : ℝ)
    (hb : ∀j : Sigma B,(g j).block=(d j.1 j.2).block)
    (hl : ∀(j : Sigma B) side c t u,
      secondNormalizedLabelSum side (g j) c t u=
      secondNormalizedLabelSum side (d j.1 j.2) c t u)
    (hfull : ∀side t u,
      (∑s,secondNormalizedSum side (d s)
        (secondEffectiveWeight (fun b=>(d s b).block) (fun b=>w ⟨s,b⟩) W) t u)≤
      (E*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) :
    SecondNormalizedBound W degree windowDegree g w (fun _=>E) (fun _=>1) := by
  apply second_normalized_bound_of_full W degree windowDegree g w E
  intro side t u
  rw [error_normalized_effective_sigma_congr g d w W hb hl]
  exact hfull side t u


variable {α : Type u} [Fintype α]
section Actual
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
local notation "N" => Fintype.card α
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
variable (P : Finset (Ideal O))
  (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)
  (Mprice Aprice : ℝ)
  (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ)
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "Sources" => GeometryJointErrorSourceIndex (reflected:=reflected) (s:=s) (R:=R) (seed:=seed) (Z:=Z) (M:=M) (ξ:=ξ) (t:=t) (hZ:=hZ) (key:=key) (P:=P)
local notation "Selected" => GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂
local notation "datum" => geometryJointErrorDatum reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂
local notation "coeff" => geometryJointErrorWeight reflected s R seed Z M amp ξ reserve b t hZ key P υ Mprice Aprice weight hz₁ hz₂

set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_datum_volume (j : Selected) :=
  errorJointVolume%((datum j))
set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_normalized_label
    (j : Selected) (χ : RayCharacter) (Q : Ideal O) (m : O)
    (side : Bool) (w : ℂ) (tₑ u : ℝ) :=
  errorJointFieldLabel%((datum j),χ,Q,m,side,w,tₑ,u)



set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_normalized_sum
    (χ : Selected→RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) :=
  letI : ∀l : Sources,DecidableEq ↥(liveIndices l.1.2.val) := fun _ a b=>a.instDecidableEq b;
  let raw := fun l : Sources=>fun n : geometryErrorNonzeroBlocks
      reflected s R seed Z M amp ξ reserve b t N hZ key l.1 l.2.1.val l.2.2.1 l.2.2.2.2
      (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂=>
    ordinarySecondDatum
      (geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t N hZ key
        l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂ n.val)
      (χ ⟨l,n⟩) Q fixedBadMask;
  let hb := fun j : Selected=>
    geometry_joint_error_ordinary_datum_block reflected s R seed Z M amp ξ reserve b t
      hZ key P υ hz₁ hz₂ j (χ j) Q fixedBadMask;
  let hl := fun (j : Selected) (side : Bool) (c : ℂ) (tₑ u : ℝ)=>
    geometry_joint_error_normalized_label reflected s R seed Z M amp ξ reserve b t
      hZ key P υ hz₁ hz₂ j (χ j) Q fixedBadMask side c tₑ u;
  error_normalized_effective_sigma_congr
    (fun j : Selected=>ordinarySecondDatum (datum j) (χ j) Q fixedBadMask)
    raw coeff W hb hl side tₑ u


/-- The exact raw source sum from the checked sigma transport. -/
def geometryJointErrorRawNormalizedSum
    (χ : Selected→RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) : ℝ :=
  errorJointRawSum%((geometry_joint_error_normalized_sum reflected s R seed Z M amp ξ reserve b t
    hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u))

/-- One summand of the exact source sum. -/
def geometryJointErrorRawNormalizedSource
    (χ : Selected→RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) (l : Sources) : ℝ :=
  errorJointRawSource%((geometry_joint_error_normalized_sum reflected s R seed Z M amp ξ reserve b t
    hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u),l)

set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_raw_sum_sources
    (χ : Selected→RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) :=
  show geometryJointErrorRawNormalizedSum reflected s R seed Z M amp ξ reserve b t
    hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u=
    ∑l : Sources,geometryJointErrorRawNormalizedSource reflected s R seed Z M amp ξ reserve b t
      hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u l from by rfl

set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_raw_source
    (χ : Selected→RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (side : Bool) (tₑ u : ℝ) (l : Sources) :=
  show geometryJointErrorRawNormalizedSource reflected s R seed Z M amp ξ reserve b t
    hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u l=
    geometryErrorRawNormalizedSum reflected s R seed Z M amp ξ reserve b t N hZ key
      l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂
      P (geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key weight N b l.1.1.val l.1.2) W
      (fun n : geometryErrorNonzeroBlocks reflected s R seed Z M amp ξ reserve b t N hZ key
        l.1 l.2.1.val l.2.2.1 l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂=>n.val)
      (fun n=>χ ⟨l,n⟩) Q side tₑ u from by rfl

set_option maxHeartbeats 100000 in
set_option Elab.async false in
checked_error_proof geometry_joint_error_normalized_bound
    (χ : Selected→RayCharacter) (Q : Ideal O) (W : 𝓢(ℝ,ℂ))
    (degree windowDegree : ℕ) (numerator : ℝ)
    (hfull : ∀side tₑ u,
      geometryJointErrorRawNormalizedSum reflected s R seed Z M amp ξ reserve b t
        hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u≤
      (numerator*(1+‖tₑ‖)^degree)*(1+‖u‖)^(2*windowDegree)) :=
  second_normalized_bound_of_full W degree windowDegree
    (fun j : Selected=>ordinarySecondDatum (datum j) (χ j) Q fixedBadMask)
    coeff numerator (fun side tₑ u=>
      (geometry_joint_error_normalized_sum reflected s R seed Z M amp ξ reserve b t
        hZ key P υ Mprice Aprice weight hz₁ hz₂ χ Q W side tₑ u).le.trans (hfull side tₑ u))

end Actual

end
end OAI.SevenEighths.Cycle63InitialMass



#print axioms OAI.SevenEighths.Cycle63InitialMass.error_normalized_label_congr
#print axioms OAI.SevenEighths.Cycle63InitialMass.error_normalized_cast_volume
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_datum_volume

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_normalized_label

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_normalized_sum

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_normalized_bound

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_raw_source

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_error_raw_sum_sources
