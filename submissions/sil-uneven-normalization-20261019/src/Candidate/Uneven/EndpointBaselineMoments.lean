import Candidate.Uneven.EndpointCountParameters
import Candidate.Cycle25.Assembly.SourceData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseRawUniform
import Candidate.Cycle25.Assembly.Count.Parameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseFields
import Candidate.Cycle25.Assembly.Count.MomentDetectorInverseMarkedField
import Candidate.Cycle25.Assembly.Count.InverseRawField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseRawField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseMarkedField
import Candidate.Uneven.EndpointSourceCountInitial
import Candidate.Uneven.MainNinePlaneFields
import Candidate.Cycle25.Energy.Endpoint
import Candidate.Cycle25.Assembly.Count.PlainInput
import Candidate.Cycle25.Assembly.Mesh
import Candidate.Cycle25.Assembly.Count.ActualMoments
import Candidate.Affine.SourceCount
import Candidate.Affine.Mesh
import Candidate.Uneven.EndpointMomentGates

/- Original module: Candidate.Uneven.EndpointInverseRaw. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Adapted from OpenAI, Hailey Collet, DaysSky and accepted PR60. Apache-2.0.
Fresh .874830 geometry; the original inverse source fields remain unchanged. -/

namespace OAI

noncomputable section
set_option autoImplicit false

open scoped Classical BigOperators
namespace SevenEighths.UnevenEndpoint.Physical.InverseRawField
variable [config : Configuration]
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open HeckeDetectorInverseFiberCount DetectorDictionaryInverseClippedUniform
open ProbeHighRowFamily ProbeFinalAssembly Cycle25ProbeHighRowFamily

private theorem raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤ B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro H D hH hD hcap rows hrows
  apply (h H D hH hD hcap rows hrows).trans
  gcongr

theorem fixed_raw_profiles (c κ:ℝ)(hc:0< c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0< C ∧
      ∀reverse:Bool,∀n:ℕ,n≤2→∀U:ℝ,0< U→∀tstar r:ℝ,
      ∀s∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤ height→t∈Set.Icc (-height) height→
      let W:=twistProfile (logTest (orientedProfile reverse (inverseTest U tstar r)) n) s t;
      RawMoment data W c κ (C*(1+height)^J) ∧
      RawMoment data (scaleProfile W) c κ (C*(1+height)^J):=by
  obtain ⟨J,hreference⟩:=DetectorDictionaryInverseRawReference.raw_reference_moment
    referenceWindow (1/18) (13/4) c κ (by norm_num) (by norm_num)
    (fun x hx=> referenceWindow_support (subset_tsupport _ hx)) hc hκ
  obtain ⟨K,C,hC,hfamily⟩:=DetectorDictionaryInverseRawUniform.raw_pair_height_uniform J
  refine ⟨K,?_⟩
  intro data
  obtain ⟨A,hA,href⟩:=hreference data
  exact ⟨A*C,mul_pos hA hC,hfamily data c κ A hA.le href⟩

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_raw
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(εm:ℝ)(counts:UnevenEndpoint.Physical.DetectorCount.CountParameters M H εm):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀{Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ},0< U→
    ∀(B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height→∀n:ℕ,n≤2→∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W counts.c
        counts.k (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) counts.c
        counts.k (C*(1+height)^J):=by
  obtain ⟨J,hraw⟩:=fixed_raw_profiles counts.c counts.k counts.c_pos counts.k_pos
  refine ⟨J,?_⟩
  intro η
  let data:=sourceMomentData M H hH S hS η
  choose C hC hb using (fun label=> hraw (data label))
  let Csum:ℝ:=1+∑label,C label
  have hsum:0≤∑label,C label:=Finset.sum_nonneg (fun j _=>(hC j).le)
  have hCs:0< Csum:=by dsimp [Csum];linarith
  have hClabel (label):C label≤ Csum:=by
    have he:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ label)
    dsimp [Csum];linarith
  refine ⟨Csum,hCs,?_⟩
  intro Slot U a ε tstar T allowance i hU B hdata bin label left right hne height hheight n hn s hs t ht F W
  have hd:F.rowData=data label:=by change B.data label=data label;rw [hdata]
  have hp:=hb label F.reverse n hn U hU tstar F.r s hs height t hheight ht
  have hconstant:C label*(1+height)^J≤ Csum*(1+height)^J:=
    mul_le_mul_of_nonneg_right (hClabel label) (by positivity)
  rw [hd]
  exact ⟨raw_mono _ _ _ _ _ _ hconstant hp.1,raw_mono _ _ _ _ _ _ hconstant hp.2⟩
end SevenEighths.UnevenEndpoint.Physical.InverseRawField
end
end OAI
end

/- Original module: Candidate.Uneven.EndpointInverseFields. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Adapted from OpenAI, Hailey Collet, DaysSky and accepted PR60. Apache-2.0.
Fresh .874830 geometry; the original inverse source fields remain unchanged. -/
namespace OAI

noncomputable section
set_option autoImplicit false

open scoped Classical BigOperators Topology
namespace SevenEighths.UnevenEndpoint.Physical.InverseFields
variable [config : Configuration]
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
    (S:WeightedSourceData D)(counts:UnevenEndpoint.Physical.DetectorCount.CountParameters M H D.t):
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
      RawMoment F.rowData W counts.c
        counts.k (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) counts.c
        counts.k (C*(1+height)^J)) ∧
    (∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
      ∀n:ℕ,n ≤ 2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2) ≤ 
          (C*(1+height)^J)*(Z^d)^(1+D.t)) := by
  obtain ⟨Jr,hr⟩ := UnevenEndpoint.Physical.InverseRawField.source_batch_inverse_raw
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

end SevenEighths.UnevenEndpoint.Physical.InverseFields

end

end OAI
end

/- Original module: Candidate.Uneven.EndpointSourceMoments. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Adapted from OpenAI, Hailey Collet, DaysSky and accepted PR60. Apache-2.0.
Private .874836 assembly; the new affine analytic input remains explicit. -/
/- Copyright (c) 2026. Released under Apache 2.0. -/

/-! Source moments at the region-aware cutoff. The original MI/MP fields are
re-used verbatim (they hold for every cutoff); the affine marked plain moment
is an explicit input, proved in `Candidate.Affine.Supply`. -/

namespace OAI.SevenEighths.UnevenEndpoint.Physical.SourceMoments
variable [config : Configuration]
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local instance : Fintype MainCount.Plane :=
  ⟨{.PR62,.PR60,.oldA,.oldC,.oldWeak,.A,.C,.A2,.C2},by intro P; cases P <;> simp⟩
open scoped Classical BigOperators SchwartzMap ComplexConjugate
local notation "SupportedPlane" => {P : MainCount.Plane // config.stage.Supports P}
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle25ProbeFinalAssembly ProbeFinalAssembly Cycle25ProbeFinalAssemblyCertifiedBands CenteredMomentEnergyCappedWidthInduction
open Cycle25ProbeDetectorPlainMarkedFineField Cycle25ProbeDetectorPlainUnmarkedField
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbePhysical

/-- `weighted_SourceMomentBound` at the region-aware cutoff with the affine field. -/
def weighted_SourceMomentBoundA {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (κplain : ℝ) (counts : UnevenEndpoint.Physical.DetectorCount.CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100< a → a ≤ 7/8 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im| ≤ height →
    UnevenEndpoint.Physical.SourceCount.SourceMomentsAtA F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
      (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z κplain counts.c counts.k C height D.t

theorem weighted_source_moments_A {D:Cycle25.Weighted.MomentData}(F:WeightedSourceData D)
    (κplain:ℝ)(hk1:κplain≤3/4)(counts:UnevenEndpoint.Physical.DetectorCount.CountParameters F.modulus ⊤ D.t)(fineMesh:ℝ)(hmesh:(0:ℝ)< fineMesh)
    (hfine:∀j,D.ell j ≤ fineMesh/200)
    (hpositive:weighted_PositiveFineSourceInput F κplain fineMesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A)
    (haffine:∀P : MainCount.Plane, config.stage.Supports P → MainInitialTransport.weighted_AffineFineInputAt P F):
    ∀η:Character,∃J:ℝ,0 ≤ J ∧ ∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ ≤ 1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBoundA F κplain counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=UnevenEndpoint.Physical.InverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=weighted_source_batch_plain_marked_fine F κplain fineMesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked D F hzero
  intro η
  choose Ja Ca hCa ha using (fun P : SupportedPlane => haffine P.val P.property η)
  let JaSum : ℕ := ∑P,Ja P
  let CaSum : ℝ := 1+∑P,Ca P
  have hCaSum : 0< CaSum := by
    have hh := Finset.sum_nonneg (fun P (_:P∈Finset.univ)=>(hCa P).le)
    dsimp [CaSum]; linarith
  have hCaLe (P : SupportedPlane) : Ca P≤ CaSum := by
    have hh := Finset.single_le_sum (fun P (_:P∈Finset.univ)=>(hCa P).le) (Finset.mem_univ P)
    dsimp [CaSum]; linarith
  have hJaLe (P : SupportedPlane) : Ja P≤ JaSum := Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ P)
  refine ⟨(Ji+Jm+Ju+JaSum:ℕ),by positivity,?_⟩
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu+CaSum,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu,Filter.eventually_all.mpr ha] with Z hi hm hu ha
  have hZ:0< Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0 ≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1 ≤ 1+height:=by linarith
  have hCi':Ci*(1+height)^Ji ≤ (Ci+Cm+Cu+CaSum)*(1+height)^(Ji+Jm+Ju+JaSum):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm ≤ (Ci+Cm+Cu+CaSum)*(1+height)^(Ji+Jm+Ju+JaSum):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju ≤ (Ci+Cm+Cu+CaSum)*(1+height)^(Ji+Jm+Ju+JaSum):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCa' (P : SupportedPlane) : Ca P*(1+height)^(Ja P) ≤ (Ci+Cm+Cu+CaSum)*(1+height)^(Ji+Jm+Ju+JaSum):=by
    apply mul_le_mul (by linarith [hCaLe P]) (pow_le_pow_right₀ hbase (by have := hJaLe P; omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha' hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im| ≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=> by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0 ≤ Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) hk1
    · constructor
      · intro n hn σ hσ t ht
        exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
          rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
      · intro selected hselected hfirst hsecond n hn σ hσ t ht
        exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
          (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
      · intro j k hjk σ hσ t ht
        exact (hunmarked j k hjk σ hσ t ht).1.trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
    · intro selected hselected hcap j k hjk σ hσ t ht
      exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro P hP hmlo hmhi selected hsel h1 h2 h3 j k hjk σ hσ t ht
    have haff := (ha ⟨P,hP⟩).2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
      (fun s=> by rw [hupper]) hext bin label left right hne height hh hheight hmlo hmhi
    exact (haff selected hsel h1 h2 h3 j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right (hCa' ⟨P,hP⟩) (Real.rpow_nonneg hU _))

end
end OAI.SevenEighths.UnevenEndpoint.Physical.SourceMoments


namespace OAI.SevenEighths.UnevenEndpoint.Physical.SourceMoments
variable [config : Configuration]
noncomputable section
set_option autoImplicit false
open scoped Classical
open Filter HeckeFamily Cycle25ProbeFinalAssembly
open Cycle25ProbeDetectorPlainMarkedFineField

theorem weighted_actual_source_moments_A {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain)
    (counts : DetectorCount.CountParameters F.modulus ⊤ D.t)
    (hfine : ∀j,D.ell j≤ Cycle25.sourceMesh D.t/200)
    (haffine : ∀P : MainCount.Plane, config.stage.Supports P → MainInitialTransport.weighted_AffineFineInputAt P F) :
    ∀η:Character,∃J:ℝ,0≤ J ∧ ∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBoundA F κplain counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact weighted_source_moments_A F κplain hk1
    counts (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine
    (terminal_plain_input F κplain hk hk1 hbeta hκbeta)
    (terminal_zero_input F κplain hk hk1 hbeta hκbeta) haffine
end
end OAI.SevenEighths.UnevenEndpoint.Physical.SourceMoments
end

/- Original module: Candidate.Uneven.EndpointBaselineMoments. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Actual original moments on the fresh Target830 slots and finite count family. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical
variable [config : Configuration]
noncomputable section
open scoped Classical
open Filter HeckeFamily

theorem actual_baseline_source_moments (D : BaselineData) (F : BaselineSourceData D)
    (counts : DetectorCount.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤ D.momentKappa)
    (hfine : ∀j,D.length j≤ Cycle25.sourceMesh D.t/200)
    (haffine : ∀P : MainCount.Plane, config.stage.Supports P → MainInitialTransport.weighted_AffineFineInputAt P F) :
    ∀η:Character,∃J:ℝ,0≤ J ∧ ∃C:ℝ,0< C ∧ ∀τ:ℝ,0<τ→τ≤1→
      ∀ᶠZ:ℝ in atTop,SourceMomentBound D (baselineSource D F) counts η Z τ
        (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact SourceMoments.weighted_actual_source_moments_A F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hβ hκβ counts hfine haffine
end
end OAI.SevenEighths.UnevenEndpoint.Physical
end
