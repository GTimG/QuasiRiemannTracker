/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.local44_20261013.Bundles.B021
import Submissions.local44_20261013.Bundles.B022
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseMarkedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceFiberEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseRawUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RelativeCapacityRemoval
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorBudget

/- BEGIN ORIGINAL MODULE Analytic.SecondRayDictionary ; sha256 b010b4a25f1ac6773424f13a819fb965aabdce32ca2ed9f6fb9abcc8c266f39b -/
section


/-! The second Poisson ray character also stays in a fixed finite parent
dictionary. Its coefficient identity holds on all ideals, including zeros. -/

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge HeckeFamily CenteredMomentFixedRay
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def rayParent (η : Character) (ξ : RayCharacter) : Character :=
  η.product (primaryRayCharacter ξ)

def rayClosure (parents : Finset Character) : Finset Character :=
  (parents ×ˢ (Finset.univ : Finset RayCharacter)).image (fun p => rayParent p.1 p.2)

theorem rayParent_mem (parents : Finset Character) (η : Character)
    (hη : η ∈ parents) (ξ : RayCharacter) : rayParent η ξ ∈ rayClosure parents :=
  Finset.mem_image.mpr ⟨(η, ξ), Finset.mem_product.mpr ⟨hη, Finset.mem_univ _⟩, rfl⟩

theorem rayClosure_fixedQ (parents : Finset Character) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)})
    (hparents : ∀ η ∈ parents, Q ≤ η.modulus)
    (τ : Character) (hτ : τ ∈ rayClosure parents) : Q ≤ τ.modulus := by
  obtain ⟨⟨η, ξ⟩, hmem, rfl⟩ := Finset.mem_image.mp hτ
  change Q ≤ η.modulus ⊓ (primaryRayCharacter ξ).modulus
  refine le_inf (hparents η (Finset.mem_product.mp hmem).1) ?_
  rw [primaryRayCharacter_modulus]
  exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6, by norm_num⟩)

theorem rayParent_rowWeight (η : Character) (ξ : RayCharacter)
    (w : O) (t : ℝ) (I : Ideal O) :
    rowWeight (rayParent η ξ) fixedBadMask 1 w t I =
      rowWeight η fixedBadMask 1 w t I * rayCharacter ξ (primaryGenerator I) := by
  by_cases hI : Supported I
  · have hn := supported_primaryGenerator_ne_zero I hI
    have hs := primary_span_supported I hI
    have hp := (primaryGenerator_spec I hn).2
    have he : idealCoeff (primaryRayCharacter ξ) I =
        elementCoeff (primaryRayCharacter ξ) (primaryGenerator I) := by
      simpa only [hs] using idealCoeff_span (primaryRayCharacter ξ) hn
    rw [primaryRayCharacter_primary ξ _ (hs.symm ▸ hI) hp] at he
    simp only [rowWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      rayParent, idealCoeff_product, he]
    ring
  · have hz (τ : Character) : rowWeight τ fixedBadMask 1 w t I = 0 :=
      rowWeight_zero_of_not_supported τ fixedBadMask 1 w t
        (dvd_mul_right goodLambda 2) (dvd_mul_left 2 goodLambda) I hI
    rw [hz, hz, zero_mul]

theorem actual_source_second_ray_rows (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    ∃ u : Oˣ, ∃ τL ∈ fixedParentDictionary η, ∃ τR ∈ fixedParentDictionary η,
      activeConductor C D = (u : O) * ∏ i, activePrimary C D i ∧
      ∀ ξ : RayCharacter, ∀ j : O, ∀ t : ℝ, ∀ I : Ideal O,
        (rowWeight F.left fixedBadMask 1 j t I * rayCharacter ξ (primaryGenerator I) =
          rowWeight (rayParent τL ξ) fixedBadMask 1
            (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
              (u : O) * leftEffectiveFactor C D * j) t I *
            leftCanceledMask C D (primaryGenerator I)) ∧
        (rowWeight F.right fixedBadMask 1 j t I * rayCharacter ξ (primaryGenerator I) =
          rowWeight (rayParent τR ξ) fixedBadMask 1
            (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
              (u : O) * rightEffectiveFactor C D * j) t I *
            rightCanceledMask C D (primaryGenerator I)) := by
  obtain ⟨u, τL, hτL, τR, hτR, hu, hrows⟩ :=
    actual_source_rows_fixed_parent η C D hC E ξ₁ ξ₂ F
  refine ⟨u, τL, hτL, τR, hτR, hu, ?_⟩
  intro ξ j t I
  obtain ⟨hl, hr⟩ := hrows j t I
  constructor
  · rw [hl, rayParent_rowWeight]
    ring
  · rw [hr, rayParent_rowWeight]
    ring

#print axioms actual_source_second_ray_rows
#print axioms rayClosure_fixedQ
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.SecondRayDictionary -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.InverseRawField ; sha256 c4a5b60b1dd4ce344a4c52e73e963fa95d231d296f0a3c71f8d08ee607c1d15f -/
section






namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.Cycle25ProbeDetectorInverseRawField
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
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(εm:ℝ)(counts:Cycle25ProbeHighRowFamily.CountParameters M H εm):
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
end SevenEighths.Cycle25ProbeDetectorInverseRawField
end
end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.InverseRawField -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorInverseMarkedField ; sha256 7106a6049fea29ed91b8a5fd05be178b54bef2b309e53db88af863331f15a214 -/
section





namespace OAI

noncomputable section

open scoped Classical BigOperators Topology SchwartzMap ContDiff
namespace SevenEighths.Cycle25ProbeDetectorInverseMarkedField
open ProbeDetectorInverseMarkedField Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open Cycle25ProbeHighRowFamily ProbeFinalAssembly Filter
open ProbeHighRowFamily ProbeFinalAssembly Filter
open Cycle25DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
local notation "O"=> HeckeFamily.O

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem weighted_source_batch_inverse_marked {D:Cycle25.Weighted.MomentData}
    (S:WeightedSourceData D):
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
    ∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
    ∀n:ℕ,n ≤ 2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
        ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2) ≤ 
        (C*(1+height)^J)*(Z^d)^(1+D.t) := by
  obtain ⟨Jref,hreference⟩:=weighted_fiber_reference_energy S referenceWindow (1/18) (13/4)
    (by norm_num) (by norm_num)
    (fun x hx=> referenceWindow_support (subset_tsupport _ hx)) (referenceWindow.smooth ⊤)
    D.t D.t_pos D.N
  obtain ⟨J,Cfourier,hCfourier,hfourier⟩:=DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform Jref
  refine ⟨J,?_⟩
  intro η
  let data:=sourceMomentData M H hH S.S S.exclusions.prime η
  choose C U₀ hC hU₀ hb using fun label=> hreference (data label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0< Csum:=by
    have hh:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label ≤ Csum:=by
    have hh:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le) (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ) ≤ d → U₀ label ≤ Z^d := by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  refine ⟨Cfourier*Csum,mul_pos hCfourier hCsum,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hscale,
    weighted_deleted_large_eventually data D.ell (fun s=>(D.slots_bounds s).1),
    weighted_sourceMoment_fiber_prime_geometry_eventually M H hH S η D.t D.t_pos] with Z hZ hscale hlarge hgeom
  refine ⟨hZ,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin label left right hne
    height hheight F selected hselected hfirst hsecond n hn s hs t ht
  have hd0:0< d:=by linarith
  have hUone:1< Z^d:=Real.one_lt_rpow hZ hd0
  have hUp:0< Z^d:=zero_lt_one.trans hUone
  have hprofile:B.profile=(fun _=>(S.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext j x
    exact (S.complex_eq x).symm
  have hfd:F.rowData=data label:=by change B.data label=data label;rw [hdata]
  have hfp (j):F.profile j=S.W:=by change B.profile j=S.W;rw [hprofile]
  have hfu (j):F.upper j=2:=by change B.upper j=2;rw [hupper]
  have hfw (j):F.widths j=D.ell j/d:=by change B.widths j=_;rw [hwidths]
  have hfe (j):(F.external j).re ≤ 1:=by change (B.external j).re ≤ 1;rw [hz j];norm_num
  have hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
    intro j hj k hk hjk
    exact (hgeom.2 d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz
      bin label left right hne).1 j k (fun he=> hjk (Subtype.ext he))
  have hlargeF:∀j∈selected,((DetectorDictionaryInverseRawInitialGates.deletedBase (data label)).modulus.absNorm:ℝ)<
      (Z^d)^(F.widths j) := by
    intro j hj
    rw [hfw]
    exact hlarge.2 d hd0 label j
  have hr:0 ≤ F.r:=Real.logb_nonneg hUone (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have href (v:ℝ):
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest referenceWindow v)
        ((Z^d)^F.r) 0 0*F.physicalProduct selected u‖^2) ≤ 
      (Csum*(Z^d)^(1+D.t))*(1+‖v‖)^(2*Jref) := by
    have hh:=hb label (Z^d) (hscale label d hd) M H F selected hfd
      (by simpa using Finset.card_le_univ selected) (fun j _=> hfp j) (fun j _=> hfu j)
      (fun j hj=>(F.widths_pos j (hselected hj)).le) (fun j _=> hfe j) hdis hlargeF hr hfirst hsecond v
    rw [(show 2*Jref=Jref*2 by omega),pow_mul]

    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hClabel label) (Real.rpow_nonneg hUp.le _)
  have hh:=hfourier F selected hUp (Csum*(Z^d)^(1+D.t)) (by positivity) href
    n hn s hs height t hheight ht
  convert hh using 1 ; ring

end SevenEighths.Cycle25ProbeDetectorInverseMarkedField

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorInverseMarkedField -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainCapacity ; sha256 570385c605b5b80f1abfcfe65a2b53a1f5ee07958367219c401d56037e24c350 -/
section




namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.Cycle25CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainCapacity Cycle25ProbeFinalAssembly
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary Cycle25CenteredMomentDetectorPlainSlotProfile
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSlotProfile
local notation "O"=> HeckeFamily.O
variable {D:Cycle25.Weighted.MomentData}

theorem weighted_physical_annular_all (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η₀:Character)
    (P:ℝ)(hP:0< P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=> conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

end SevenEighths.Cycle25CenteredMomentDetectorPlainCapacity

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainCapacity -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.OriginalInverseRawField ; sha256 befc7cd2e6746447c5c86824d61efee603de668d1261ad514918c4f79081532f -/
section






namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.Cycle25OriginalDetectorInverseRawField
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
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(εm:ℝ)(counts:ProbeFinalAssembly.CountParameters M H εm):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀{Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ},0< U→
    ∀(B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height→∀n:ℕ,n≤2→∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W counts.cB
        counts.kB (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) counts.cB
        counts.kB (C*(1+height)^J):=by
  obtain ⟨J,hraw⟩:=fixed_raw_profiles counts.cB counts.kB counts.cB_pos counts.kB_pos
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
end SevenEighths.Cycle25OriginalDetectorInverseRawField
end
end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.OriginalInverseRawField -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.SourceParametersCount ; sha256 d66b458cd29ff806f1e6079d28c157cf988bd4671d6ebf4fe28f3041f5925532 -/
section




namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open Cycle25ProbeHighRowFamily
open ProbeHighRowFamily

theorem balanced_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (_hH : RayOrthogonality.globalUnits M≤ H) (_S : Finset (Ideal O))
    (φ : ℝ→ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ)
    (_hφp : tsupport φ⊆Ioi 0) (_hφ0 : ∀y,0≤φ y) (_hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (_ha₀ : 0< a₀) (_hab₀ : a₀≤ b₀) (_hB₀ : 0< B₀)
    (_hφs : Function.support φ⊆Ioo a₀ b₀) (_hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (_hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0< dmin) (hdmax : 0< dmax) (hτ : 0<τ)
    (hl : 0< logCost) (hh : τ< heightCost) (hb : 0< binWidth) (counts : Cycle25ProbeHighRowFamily.CountParameters M H εm) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀(a ε κplain ν C q : ℝ) (i : ℕ),i≤ n → 51/100< a → 2*a-1≤3/4 → a≤1 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → 0≤ C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤ N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain counts.c counts.k (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤ K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(rowCount (2*a-1) (q/(2*a-1)) κplain+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.balanced
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε κplain ν C q i hi ha haδ ha' hε hε' hk hk1 hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) κplain ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hk hk1 hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.SourceParametersCount -/
