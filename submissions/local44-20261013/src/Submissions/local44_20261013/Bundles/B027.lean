/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.local44_20261013.Bundles.B014
import Submissions.local44_20261013.Bundles.B020
import Submissions.local44_20261013.Bundles.B024
import Submissions.local44_20261013.Bundles.B025
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseFields
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseMarkedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseRawField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainExceptional ; sha256 52b57dd70e7c1c84a3b2885a5b0682faea409db2bbe9b8d5667c329897a312bf -/
section





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainExceptional Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open Cycle25CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=> HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def weighted_retainedSourceEnergy (keep:O→Prop)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy keep (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

theorem weighted_retained_positive_energy_le_source
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0 ≤ (Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0< U)
    (hkeep:∀u∈F.rows,keep u.val):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2) ≤ 
      weighted_retainedSourceEnergy keep F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=> fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=> Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted keep Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      exact hkeep u hu) (fun z=> hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=> Subtype.val_injective hxy)]
    _ ≤ _:=div_le_div_of_nonneg_right hb ht.le

variable {D:Cycle25.Weighted.MomentData}

theorem weighted_source_fibers_eventually_retained (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        weighted_initialKeep η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (weighted_sourceExceptional S η₀))=∅:=by
  filter_upwards [weighted_eventually_source_no_exceptional S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      weighted_initialKeep η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) u.val:=by
    intro u hu
    apply (weighted_source_keep_iff S η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact ((weighted_source_keep_iff S η₀ u).mp (hk u hu)) hex

theorem weighted_source_batch_plain_retained (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2) ≤ 
        weighted_retainedSourceEnergy (weighted_initialKeep η₀ (internalQ (weighted_sourceFixedIdeal S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [weighted_source_fibers_eventually_retained S η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1) 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0< Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus ≤ Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
  have hη:∀s∈selected,∀I∈primePool S.modulus ⊤ (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((I.absNorm:ℝ)/((Z^d)^(F.widths s)))≠0→IsCoprime I η₀.modulus:=by
    intro s hs I hI hn
    change I∈primePool S.modulus ⊤ (B.upper s) ((Z^d)^(B.widths s)) at hI
    change B.profile s ((I.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hn
    rw [hwidth] at hI
    rw [hwidth,hprofile] at hn
    exact hcop label s d hd (fun x=>(S.w x:ℂ)) (B.upper s)
      (by
        intro x hx
        have hn:S.w x≠0:=by simpa using hx
        exact (S.support hn).1.le) I hI hn
  rw [fiber_plain_energy_eq F η₀ hdataF hMm hU selected j k σ t hη]
  exact weighted_retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end SevenEighths.Cycle25CenteredMomentDetectorPlainExceptional

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainExceptional -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.OriginalInverseFields ; sha256 59a1a7729a6e631e4fba7a886cab5621ce9be88df2399a064ae87900af2ee949 -/
section





namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.Cycle25OriginalDetectorInverseFields
open ProbeDetectorInverseFields Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
local notation "O"=> HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

private lemma raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A ≤ B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

theorem weighted_source_batch_inverse_fields {D:Cycle25.Weighted.MomentData}
    (S:WeightedSourceData D)(counts:ProbeFinalAssembly.CountParameters M H D.t):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀d:ℝ,(1/200:ℝ) ≤ d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=> D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0 ≤ height →
    let F:=B.fiber bin label left right hne;
    (∀n:ℕ,n ≤ 2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W counts.cB
        counts.kB (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) counts.cB
        counts.kB (C*(1+height)^J)) ∧
    (∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
      ∀n:ℕ,n ≤ 2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2) ≤ 
          (C*(1+height)^J)*(Z^d)^(1+D.t)) := by
  obtain ⟨Jr,hr⟩ := Cycle25OriginalDetectorInverseRawField.source_batch_inverse_raw
    M H hH S.S S.exclusions.prime D.t counts
  obtain ⟨Jm,hm⟩ := Cycle25ProbeDetectorInverseMarkedField.weighted_source_batch_inverse_marked M H hH S
  refine ⟨Jr+Jm,?_⟩
  intro η
  obtain ⟨Cr,hCr,hr⟩ := hr η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  refine ⟨Cr+Cm,add_pos hCr hCm,?_⟩
  filter_upwards [hm] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
    bin label left right hne height hheight F
  have hU:0< Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _
  have hscale:1 ≤ 1+height := by linarith
  have hraw:Cr*(1+height)^Jr ≤ (Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_right _ _)
    · positivity
    · positivity
  have hmarked:Cm*(1+height)^Jm ≤ (Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_left _ _)
    · positivity
    · positivity
  constructor
  · intro n hn s hs t ht
    have hh:=hr hU B hdata bin label left right hne height hheight n hn s hs t ht
    exact ⟨raw_mono _ _ _ _ _ _ hraw hh.1,raw_mono _ _ _ _ _ _ hraw hh.2⟩
  · intro selected hselected hfirst hsecond n hn s hs t ht
    have hh:=hZ.2 d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
      bin label left right hne height hheight selected hselected hfirst hsecond n hn s hs t ht
    exact hh.trans (mul_le_mul_of_nonneg_right hmarked (Real.rpow_nonneg hU.le _))

end SevenEighths.Cycle25OriginalDetectorInverseFields

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.OriginalInverseFields -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.SourceMomentInput ; sha256 8746e9a4f08421c4f99308b01449ddb5b6f8b00f2587b487c0a0287f579f255b -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle25ProbeHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def SourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (κplain c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=> ell j/d) → B.profile=W → B.upper=(fun _=> b) → B.external=(fun _=> z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm

end SevenEighths.Cycle25ProbeHighRowFamily

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.SourceMomentInput -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.DeletedRobustGeometry ; sha256 795b91c72d0dd45130769b8655248cdc7025ddabebfc7b440276cf79f82bf38f -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/DeletedRobustGeometry.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyDeletedRobustGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState Cycle25CenteredMomentEnergyReferenceDivisors
open Cycle25CenteredMomentEnergyLiveClippingDefect
local notation "O" => HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(hB:0≤ Bmask)(Mcap L X₁ X₂ ell z κ xi e:ℝ)
    (hwidth:s.width≤ Mcap)(hL:Mcap+Bmask+xi≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hκ:7/10≤κ)(hxi:0≤ xi)(he:0≤ e)(hreserve:xi+13*e/8≤ s.width/16)
    (hlarge:5*s.width/6-e≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤ L ∧ along≤ L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤ L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):= by
  have hbase : 0 < Z := zero_lt_one.trans hZ
  have hb := robust_balanced_long_nonneg s.width (Real.logb Z (X₁*X₂)) ell κ xi e
    s.width_nonneg hell hκ hxi hlarge hcap hreserve
  have hy₁ : 1 ≤ comparisonFirst Z s.width :=
    Real.one_le_rpow hZ.le (by linarith [s.width_nonneg])
  have hy₂ : 1 ≤ comparisonSecond Z s.width X₁ X₂ := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hf : Real.logb Z (comparisonFirst Z s.width) = s.width/4 :=
    Real.logb_rpow hbase hZ.ne'
  have hl : Real.logb Z (comparisonSecond Z s.width X₁ X₂) = Real.logb Z (X₁*X₂)-s.width/4 := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂, Real.logb_rpow hbase hZ.ne']
  have hd₁ := divisor_reflection_range s hZ Mcap _ hwidth hy₁ D₁ hD₁
  have hd₂ := divisor_reflection_range s hZ Mcap _ hwidth hy₂ D₂ hD₂
  dsimp only at hd₁ hd₂
  rw [hf] at hd₁
  rw [hl] at hd₂
  have hn₁ := (divisor_norm s D₁ hD₁).1
  have hn₂ := (divisor_norm s D₂ hD₂).1
  have hlog₁ := Real.logb_nonneg hZ hn₁
  have hlog₂ := Real.logb_nonneg hZ hn₂
  have hMcap : 0 ≤ Mcap := s.width_nonneg.trans hwidth
  have hLc : 0 ≤ L := by linarith
  have hslot : 0 ≤ (6*κ-1)*ell := mul_nonneg (by linarith) hell
  dsimp only
  refine ⟨hd₁.2.2, hd₂.2.2, by linarith, by linarith [s.width_nonneg],
    by linarith, hd₂.2.1, max_le hLc (by linarith [hd₂.1]), ?_⟩
  have hp₁ : ∀ I ∈ D₁, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₁ hi)
  have hp₂ : ∀ I ∈ D₂, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₂ hi)
  let along := Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ)
  have halong : Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏ P ∈ D₂, P).absNorm : ℝ)) = along := by
    rw [← hd₂.2.2]
    exact Real.logb_rpow hbase hZ.ne'
  rcases robust_deleted_reference_cases Z s.width X₁ X₂ ell z κ xi e (max 0 (s.width-along+xi))
    hZ s.width_nonneg hX₁ hX₂ hell hz hze hκ hxi he hreserve hlarge hcap D₁ D₂ hp₁ hp₂
    (by rw [halong]) with hc | hc
  · exact Or.inl (by simpa only [hd₁.2.2, hd₂.2.2] using hc)
  · apply Or.inr
    have hh := robust_reflected_low_admissible s.width xi e _ (max 0 (s.width-along+xi)) z κ
      he hreserve hc.2.1 hc.2.2
    simpa only [hd₁.2.2] using hh

end SevenEighths.Cycle25CenteredMomentEnergyDeletedRobustGeometry

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.DeletedRobustGeometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionGeometry ; sha256 f7462015ada95676308671e3a9853a481f8ba2bf3f965f4c901f6dd990db27d2 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/OriginalHighReflectionGeometry.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState Cycle25CenteredMomentEnergyReferenceDivisors
open Cycle25CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=> HeckeFamily.O

lemma original_long_positive (Z M X₁ X₂ ell κ:ℝ)(hZ:1< Z)(hM:0< M)
    (_hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:7/10≤κ)
    (hshort:length Z X₁≤ M/4)
    (hlarge:5*M/6≤ length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤ M):
    0< Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤ X₂:=by
  have hbudget:=slot_budgets M (length Z X₁+length Z X₂) ell κ hM.le hell hκ hlarge (by linarith)
  have hpos:0< length Z X₂:=by linarith [hbudget.1]
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0< Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma deleted_length_le (Z X N:ℝ)(hZ:1< Z)(hX:0< X)(hN:1≤ N):
    length Z (X/N)≤ length Z X:=by
  exact Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 _))
    (max_le_max_left 1 (div_le_self hX.le hN))

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(hM:0< s.width)(hB:0≤ Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤ Mcap)(hL:Mcap+Bmask+xi≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hκ:7/10≤κ)(hxi:0≤ xi)(hxiM:xi≤ s.width/16)
    (hshort:length Z X₁≤ s.width/4)
    (hlarge:5*s.width/6≤ length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ));
    let along:=Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ));
    Z^short=X₁/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤ L ∧ along≤ L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤ L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):=by
  dsimp only
  have hZ0:=zero_lt_one.trans hZ
  obtain ⟨hn₁,hc₁⟩:=divisor_norm s D₁ hD₁
  obtain ⟨hn₂,hc₂⟩:=divisor_norm s D₂ hD₂
  have hp₁:=div_pos hX₁ (zero_lt_one.trans_le hn₁)
  have hp₂:=div_pos hX₂ (zero_lt_one.trans_le hn₂)
  have he₁:=Real.rpow_logb hZ0 hZ.ne' hp₁
  have he₂:=Real.rpow_logb hZ0 hZ.ne' hp₂
  have hd₁:=deleted_length_le Z X₁ _ hZ hX₁ hn₁
  have hd₂:=deleted_length_le Z X₂ _ hZ hX₂ hn₂
  have hraw₁:Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ))≤
      length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₁];exact le_max_right _ _
  have hraw₂:Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))≤
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₂];exact le_max_right _ _
  have hlen₁:=length_nonneg Z X₁ hZ
  have hlen₂:=length_nonneg Z X₂ hZ
  have hslot:0≤6*κ*ell:=mul_nonneg (by linarith) hell
  have hl:=original_long_positive Z s.width X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hshort hlarge hcap
  have hrange:=divisor_reflection_range s hZ Mcap X₂ hwidth hl.2.2 D₂ hD₂
  dsimp only at hrange
  have hlogdiv:=Real.logb_div (b:=Z) hX₂.ne' (zero_lt_one.trans_le hn₂).ne'
  rw [←hlogdiv] at hrange
  have hL0:0≤ L:=by linarith
  refine ⟨he₁,he₂,by linarith,by linarith,by linarith,hrange.2.1,
    max_le hL0 (by linarith [hrange.1]),?_⟩
  rw [he₁,he₂]
  by_cases hd:length Z (X₁/((∏P∈D₁,P).absNorm:ℝ))+
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+z≤5*s.width/6
  · refine Or.inl ⟨hd,?_⟩
    have hkz:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*κ)
    linarith
  · obtain ⟨he,hbudget⟩:=slot_budgets s.width (length Z X₁+length Z X₂) ell κ
      hM.le hell hκ hlarge (by linarith)
    have hlow:=reflected_low s.width (length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)))
      (Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))) ell z κ xi
      (max 0 (s.width-Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+xi))
      hM.le (length_nonneg Z _ hZ)
      (hd₁.trans hshort) hell hz hze hκ he hbudget hxi
      (by rw [←length_eq_max_log Z _ hZ hp₂];exact lt_of_not_ge hd) le_rfl
    exact Or.inr (reflected_low_admissible s.width xi _ _ z κ hxiM hlow.2.1 hlow.2.2)

end SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionGeometry

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionGeometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorCorrectionExpansion ; sha256 edb1adf233a212176c98dff8fb19d3a5b4c1c3dbf0d112555c7af2ef18b88a98 -/
section



/-! Absolute Mellin coefficient packet for the original complete correction. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem weighted_product_term {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ) (i : ι) (j : κ) :
    ‖A i * B j‖ * ((N i * M j : ℝ≥0) : ℝ) ^ (-sigma) =
      (‖A i‖ * (N i : ℝ) ^ (-sigma)) * (‖B j‖ * (M j : ℝ) ^ (-sigma)) := by
  rw [norm_mul, NNReal.coe_mul, Real.mul_rpow (show (0 : ℝ) ≤ N i from (N i).property) (show (0 : ℝ) ≤ M j from (M j).property)]
  ring

theorem mellin_product_term {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (w : ℂ) (i : ι) (j : κ) :
    (A i * B j) * ((N i * M j : ℝ≥0) : ℂ) ^ (-w) =
      (A i * (N i : ℂ) ^ (-w)) * (B j * (M j : ℂ) ^ (-w)) := by
  have hh := map_mul (positiveCpowHom (-w)) (N i) (M j)
  simp only [positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hh
  rw [hh]
  ring

theorem weighted_product_summable {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ)
    (hA : Summable (fun i => ‖A i‖ * (N i : ℝ) ^ (-sigma)))
    (hB : Summable (fun i => ‖B i‖ * (M i : ℝ) ^ (-sigma))) :
    Summable (fun ij : ι × κ => ‖A ij.1 * B ij.2‖ *
      ((N ij.1 * M ij.2 : ℝ≥0) : ℝ) ^ (-sigma)) := by
  simp_rw [weighted_product_term]
  exact hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity)

theorem weighted_product_mass {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ)
    (hA : Summable (fun i => ‖A i‖ * (N i : ℝ) ^ (-sigma)))
    (hB : Summable (fun i => ‖B i‖ * (M i : ℝ) ^ (-sigma))) :
    (∑' ij : ι × κ, ‖A ij.1 * B ij.2‖ * ((N ij.1 * M ij.2 : ℝ≥0) : ℝ) ^ (-sigma)) =
      (∑' i, ‖A i‖ * (N i : ℝ) ^ (-sigma)) *
      (∑' j, ‖B j‖ * (M j : ℝ) ^ (-sigma)) := by
  simp_rw [weighted_product_term]
  exact (hA.tsum_mul_tsum hB
    (hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity))).symm

def CorrectionIndex (S : Finset (Ideal O)) (u : FreeRow) :=
  (ramifiedPrimes S u → Fin 3) × EulerIndex {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} 3

def correctionCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (e : CorrectionIndex S u) : ℂ :=
  ramifiedTupleCoefficient S hS η u x z e.1 *
    eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e.2

def correctionScale (S : Finset (Ideal O)) (u : FreeRow) (e : CorrectionIndex S u) : ℝ≥0 :=
  ramifiedTupleScale S u e.1 * eulerScale (fun P => primeScale P.val) e.2

theorem ramifiedTupleScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (j : ramifiedPrimes S u → Fin 3) : 1 ≤ ramifiedTupleScale S u j := by
  apply Finset.one_le_prod
  intro P hP
  exact one_le_pow₀ (primeScale_one_le P.val)

theorem correctionScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (e : CorrectionIndex S u) : 1 ≤ correctionScale S u e := by
  unfold correctionScale
  exact one_le_mul_of_one_le_of_one_le (ramifiedTupleScale_one_le S u e.1)
    (eulerScale_one_le (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val)
      (fun P => primeScale_one_le P.val) e.2)

theorem continuedCorrection_coefficient_mass (eps sigma : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
    (x z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hsigma : -(1 / 100 : ℝ) ≤ sigma) (hxw : 1 + eps ≤ x.re + sigma) :
    Summable (fun e : CorrectionIndex S u => ‖correctionCoefficient S hS η u x z e‖ *
      (correctionScale S u e : ℝ) ^ (-sigma)) ∧
    (∑' e : CorrectionIndex S u, ‖correctionCoefficient S hS η u x z e‖ *
      (correctionScale S u e : ℝ) ^ (-sigma)) ≤
      579 ^ (ramifiedPrimes S u).card * Real.exp (1 / 2) := by
  obtain ⟨hU,hUm⟩ := actual_unramified_coefficient_mass eps sigma S hfirst η u x z hx hz hsigma hxw
  have hR := ramified_product_coefficient_mass S hS η u x z sigma hx hsigma hz
    (by linarith [hfirst.positive])
  have hRs := (hasSum_fintype (fun j : ramifiedPrimes S u → Fin 3 =>
    ‖ramifiedTupleCoefficient S hS η u x z j‖ * (ramifiedTupleScale S u j : ℝ) ^ (-sigma))).summable
  refine ⟨weighted_product_summable _ _ _ _ sigma hRs hU, ?_⟩
  change (∑' e : (ramifiedPrimes S u → Fin 3) × EulerIndex {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} 3,
    ‖ramifiedTupleCoefficient S hS η u x z e.1 *
      eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e.2‖ *
    ((ramifiedTupleScale S u e.1 * eulerScale (fun P => primeScale P.val) e.2 : ℝ≥0) : ℝ) ^ (-sigma)) ≤ _
  rw [weighted_product_mass _ _ _ _ sigma hRs hU, tsum_fintype]
  exact mul_le_mul hR hUm (tsum_nonneg (fun _ => by positivity)) (by positivity)

theorem continuedCorrection_coefficient_expansion (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    continuedCorrection S hS η u x w z =
      ∑' e : CorrectionIndex S u, correctionCoefficient S hS η u x z e *
        (correctionScale S u e : ℂ) ^ (-w) := by
  have hU := (actual_unramified_coefficient_mass eps w.re S hfirst η u x z hx hz hw hxw).1
  have hUn : Summable (fun e : EulerIndex {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} 3 =>
      ‖eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e *
        (eulerScale (fun P => primeScale P.val) e : ℂ) ^ (-w)‖) := by
    convert hU using 1
    ext e
    have hp : 0 < (eulerScale (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val) e : ℝ) := by
      have hh := eulerScale_one_le (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val)
        (fun P => primeScale_one_le P.val) e
      exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.neg_re]
  rw [continuedCorrection, ramified_product_expansion,
    actual_unramified_expansion eps S hfirst η u x w z hx hz hw hxw]
  have hprod := tsum_mul_tsum_of_summable_norm
    (hasSum_fintype (fun j : ramifiedPrimes S u → Fin 3 =>
      ‖ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w)‖)).summable hUn
  simp only [tsum_fintype] at hprod
  rw [hprod]
  apply tsum_congr
  intro e
  exact (mellin_product_term _ _ _ _ w e.1 e.2).symm

theorem continuedCorrection_coefficient_subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (eps sigma : ℝ) (S : Finset (Ideal O))
      (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
      (x z : ℂ), (51 / 100 : ℝ) ≤ x.re → (17 / 50 : ℝ) ≤ z.re →
      -(1 / 100 : ℝ) ≤ sigma → 1 + eps ≤ x.re + sigma →
      (∑' e : CorrectionIndex S u, ‖correctionCoefficient S hS η u x z e‖ *
        (correctionScale S u e : ℝ) ^ (-sigma)) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ epsilon := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 579 epsilon
    (by norm_num) hepsilon
  refine ⟨C * Real.exp (1 / 2), by positivity, ?_⟩
  intro eps sigma S hS hfirst η u x z hx hz hsigma hxw
  have hm := (continuedCorrection_coefficient_mass eps sigma S hS hfirst η u x z
    hx hz hsigma hxw).2
  have hc : (579 : ℝ) ^ (ramifiedPrimes S u).card ≤
      C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ epsilon := by
    apply le_trans _ (hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
    apply pow_le_pow_right₀ (by norm_num)
    rw [←HeckeDeletionBounds.primeSet_card]
    exact Finset.card_filter_le _ _
  exact hm.trans ((mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq (by ring))

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorCorrectionExpansion -/
