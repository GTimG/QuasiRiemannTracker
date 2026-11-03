/- UNVERIFIED adapters retaining original physical plain moment objects. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.DetectorEnergyInitialState
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.NaturalFixedRaySourceFreeExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

variable {Δ total margin recordMesh : ℝ}{D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin recordMesh}

theorem source_fibers_eventually_retained_retuned (S:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        initialKeep η₀ (internalQ (sourceFixedIdeal_retuned S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (sourceExceptional_retuned S η₀))=∅:=by
  filter_upwards [eventually_source_no_exceptional_retuned S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      initialKeep η₀ (internalQ (sourceFixedIdeal_retuned S) η₀) u.val:=by
    intro u hu
    apply (source_keep_iff_retuned S η₀ u).mpr
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
  exact ((source_keep_iff_retuned S η₀ u).mp (hk u hu)) hex

theorem source_exceptional_energy_eventually_zero_retuned (S:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀f:FreeRow→ℂ,
      (∑u∈rows.filter (sourceExceptional_retuned S
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)),‖f u‖^2)=0:=by
  filter_upwards [eventually_source_no_exceptional_retuned S η] with Z hz
  intro rows hrows label f
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact False.elim ((hz label u (hrows u hu)) hex)

theorem source_batch_plain_retained_retuned (S:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        retainedSourceEnergy (initialKeep η₀ (internalQ (sourceFixedIdeal_retuned S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [source_fibers_eventually_retained_retuned S η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1) 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0<Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus≤Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
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
  exact retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end SevenEighths.CenteredMomentDetectorPlainExceptional

end

end OAI

#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.source_fibers_eventually_retained_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.source_exceptional_energy_eventually_zero_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.source_batch_plain_retained_retuned
