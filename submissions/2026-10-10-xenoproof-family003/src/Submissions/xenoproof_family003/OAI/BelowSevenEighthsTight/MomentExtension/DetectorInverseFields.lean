/- UNVERIFIED adapters of original physical inverse moment estimates. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseFields
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.DetectorInverseRawField
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.DetectorInverseMarkedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseRawField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseMarkedField

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.ProbeDetectorInverseFields
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

private lemma raw_mono_retuned_fields (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

theorem source_batch_inverse_fields_retuned {Δ total margin mesh : ℝ}{D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin mesh}
    (S:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(counts:_root_.BelowSevenEighthsTight.FiberExtension.RetunedCountParameters M H D.t):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀d:ℝ,(1/200:ℝ)≤d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=>D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height →
    let F:=B.fiber bin label left right hne;
    (∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J)) ∧
    (∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
      ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
          (C*(1+height)^J)*(Z^d)^(1+D.t)) := by
  obtain ⟨Jr,hr⟩ := ProbeDetectorInverseRawField.source_batch_inverse_raw_retuned
    M H hH S.S S.exclusions.prime D.t counts
  obtain ⟨Jm,hm⟩ := ProbeDetectorInverseMarkedField.source_batch_inverse_marked_retuned M H hH S
  refine ⟨Jr+Jm,?_⟩
  intro η
  obtain ⟨Cr,hCr,hr⟩ := hr η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  refine ⟨Cr+Cm,add_pos hCr hCm,?_⟩
  filter_upwards [hm] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
    bin label left right hne height hheight F
  have hU:0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _
  have hscale:1≤1+height := by linarith
  have hraw:Cr*(1+height)^Jr≤(Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_right _ _)
    · positivity
    · positivity
  have hmarked:Cm*(1+height)^Jm≤(Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_left _ _)
    · positivity
    · positivity
  constructor
  · intro n hn s hs t ht
    have hh:=hr hU B hdata bin label left right hne height hheight n hn s hs t ht
    exact ⟨raw_mono_retuned_fields _ _ _ _ _ _ hraw hh.1,raw_mono_retuned_fields _ _ _ _ _ _ hraw hh.2⟩
  · intro selected hselected hfirst hsecond n hn s hs t ht
    have hh:=hZ.2 d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
      bin label left right hne height hheight selected hselected hfirst hsecond n hn s hs t ht
    exact hh.trans (mul_le_mul_of_nonneg_right hmarked (Real.rpow_nonneg hU.le _))

end SevenEighths.ProbeDetectorInverseFields

end

end OAI

#print axioms OAI.SevenEighths.ProbeDetectorInverseFields.source_batch_inverse_fields_retuned
