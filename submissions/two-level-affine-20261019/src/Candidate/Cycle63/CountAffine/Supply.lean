/- The detector affine moment from Collet's anchor-general affine machinery.
Adapted from the detector-affine submission of DaysSky (Apache-2.0).
Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryChosenSetup
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainTwoLevel
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePaidComponents
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceNaturalRow

/-! For every detector label the dictionary character has modulus dividing the
source modulus, so it is a natural row of itself (`naturalRowOf`). Collet's paid main and
error families and her literal geometry assembly are generic in that character; they give
the initial affine moment for each label, at the mesh `detectorMesh` and loss `D.t`. The
detector fiber energy is matched to the initial energy as in Collet's κ-marked moment. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate SchwartzMap HeckeNotation
open Filter HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open ProbePhysical CenteredMomentDetectorDictionary Cycle25ProbeFinalAssembly
open Cycle25WeightedNumeratorPhysical CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentLogDyadic

/-- The early mesh copy is Collet's chosen geometry mesh. -/
theorem detectorMesh_eq (ε : ℝ) :
    Cycle63.CountAffine.detectorMesh ε = Cycle63.FinalAssembly.geometryChosenMesh ε := rfl

/-- The inverse of a residue character is the residue character of the inverse. -/
theorem ofResidue_inverse (M : Ideal O) (hM : M ≠ ⊥) (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) :
    (Character.ofResidue M hM χ hu).inverse =
      Character.ofResidue M hM χ⁻¹ (Character.ofResidue M hM χ hu).inverse.unit_trivial := rfl

theorem excluded_one_inverse_ofResidue (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) :
    excluded (Character.ofResidue M hM χ hu).inverse 1 = (Character.ofResidue M hM χ hu).inverse := by
  rw [ofResidue_inverse]
  exact excluded_one_ofResidue _ _ _ _

theorem supported_of_modulus (χ : Character) (hχ : χ.modulus ≤ Ideal.span {fixedBadMask})
    (n : O) (hn : elementCoeff χ n ≠ 0) : Supported (Ideal.span {n}) := by
  have hunit := MulChar.apply_ne_zero_iff.mp hn
  have hcop : IsCoprime (Ideal.span {n}) χ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp hunit
  have hc : IsCoprime n fixedBadMask :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hχ))
  have hlam : IsCoprime goodLambda n := (hc.symm.of_isCoprime_of_dvd_left (dvd_mul_right _ _))
  have htwo : IsCoprime (2 : O) n := (hc.symm.of_isCoprime_of_dvd_left (dvd_mul_left _ _))
  apply (supported_span_iff n).mpr
  refine ⟨PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp hlam, ?_⟩
  have hneg : IsCoprime (-2 : O) n := htwo.of_isCoprime_of_dvd_left ⟨-1, by ring⟩
  simpa only [neg_dvd] using negative_two_prime.irreducible.coprime_iff_not_dvd.mp hneg

theorem unit_row_of_modulus (χ : Character) (hχ : χ.modulus ≤ Ideal.span {fixedBadMask}) (n : O) :
    elementCoeff χ n = rowTwist (elementHom χ) fixedBadMask 1 1 n := by
  by_cases hs : Supported (Ideal.span {n})
  · have hcop : IsCoprime (Ideal.span {n}) (Ideal.span {fixedBadMask}) :=
      (Ideal.isCoprime_span_singleton_iff _ _).mpr (fixedBadMask_coprime n hs).symm
    have hrow := idealRowHom_sixth_mask fixedBadMask (Ideal.span {n}) hs
    rw [ite_eq_left hcop] at hrow
    change elementCoeff _ n = elementCoeff _ n * idealRowHom (fixedBadMask ^ 6 * 1 ^ 4 * 1) _
    simp only [one_pow, mul_one]
    change elementCoeff _ n = elementCoeff _ n * idealRowHom (fixedBadMask ^ 6) (Ideal.span {n})
    rw [hrow, mul_one]
  · have hz : elementCoeff χ n = 0 := by
      by_contra h
      exact hs (supported_of_modulus χ hχ n h)
    change elementCoeff _ n = elementCoeff _ n * idealRowHom _ _
    rw [hz, zero_mul]

/-- A character whose modulus divides the fixed bad mask is its own natural row. -/
def naturalRowOf (χ : Character) (hχ : χ.modulus ≤ Ideal.span {fixedBadMask}) :
    NaturalRow χ (1 : O) where
  character := χ
  modulus_bound := by
    have hm : 1 ≤ (Ideal.span {fixedBadMask} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    have h72 : 1 ≤ (Ideal.span {(72 : O)} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    simp only [rowConductorBound, Ideal.span_singleton_one, Ideal.absNorm_top, one_pow, mul_one]
    exact (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt hm)).trans
      (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt h72))
  element := unit_row_of_modulus χ hχ

theorem source_modulus_le_mask {D : WeightedQRH.MomentData} (S : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) :
    S.modulus ≤ Ideal.span {fixedBadMask} := by
  have h := source_product_le_rowMask S.S S.exclusions.bad
  have e : ProbeHighRowFamily.rowMaskElement = fixedBadMask := by
    unfold ProbeHighRowFamily.rowMaskElement fixedBadMask; ring
  rw [e] at h
  exact h

/-- Every detector dictionary character has modulus inside the source modulus. -/
theorem detector_label_modulus {D : WeightedQRH.MomentData} (S : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤)) :
    (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus ≤
      Ideal.span {fixedBadMask} := by
  apply le_trans _ (source_modulus_le_mask S)
  rcases label with b|θ
  · cases b
    · change η.inverse.modulus * (∏ P ∈ S.S, P) ≤ ∏ P ∈ S.S, P
      exact Ideal.mul_le_right
    · change (fixedSourcePrincipal S.S S.exclusions.prime).modulus ≤ S.modulus
      exact le_rfl
  · change (HeckeRayQuotient.character S.modulus ⊤ le_top θ).inverse.modulus ≤ S.modulus
    exact le_rfl

theorem detector_label_excluded {D : WeightedQRH.MomentData} (S : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤)) :
    excluded (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label) 1 =
      sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label := by
  rcases label with b|θ
  · cases b
    · change excluded (η.inverse.excludePrimes S.S S.exclusions.prime) 1 =
        η.inverse.excludePrimes S.S S.exclusions.prime
      unfold Character.excludePrimes Character.refineModulus
      exact excluded_one_ofResidue _ _ _ _
    · change excluded (fixedSourcePrincipal S.S S.exclusions.prime) 1 =
        fixedSourcePrincipal S.S S.exclusions.prime
      unfold fixedSourcePrincipal HeckeRayFamily.character
      exact excluded_one_ofResidue _ _ _ _
  · change excluded (HeckeRayQuotient.character S.modulus ⊤ le_top θ).inverse 1 =
      (HeckeRayQuotient.character S.modulus ⊤ le_top θ).inverse
    unfold HeckeRayQuotient.character HeckeRayFamily.character
    exact excluded_one_inverse_ofResidue _ _ _ _

/-- The initial affine moment for one detector label. -/
theorem detector_label_initial_affine {D : WeightedQRH.MomentData}
    (S : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤))
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (ε : ℝ) (hε : 0<ε) (mesh : ℝ) (hmesh0 : 0< mesh)
    (hmesh : mesh ≤ Cycle63.FinalAssembly.geometryChosenMesh ε) (bΦ : ℝ) (hbΦ : 2≤bΦ) :
    let ηl := sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,
      Cycle63Moment.InitialAffineAt (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
        ηl ηl (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) degree Sd C := by
  intro ηl
  let W:=fun x=>conj (S.W x)
  have hW : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (S.W.smooth ⊤)
  have hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact S.complex_support (by intro hz;exact hx (by change conj (S.W x)=0;rw [hz];simp))
  have hm := Cycle63.FinalAssembly.geometry_chosen_mesh_admission ε hε
  have hmeshlt : mesh<Cycle63.Arithmetic.amplifierFloor/2 := by simpa using hmesh.trans_lt hm.2.2.2.2
  have hmeshμ : mesh≤ geometryLossUnit 1 (ε/4)/8 := hmesh.trans hm.2.2.2.1
  have hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 (ε/4)/8) :=
    hmesh.trans hm.2.2.1
  have hε4 : 0<ε/4 := by positivity
  let row := naturalRowOf ηl (detector_label_modulus S η label)
  have hmarked : mesh ≤ Cycle63MarkedPlain.markedRawMesh*Cycle63MarkedPlain.markedCoreMin := by
    have hg : Cycle63.FinalAssembly.geometryChosenMesh ε ≤
        Cycle63MarkedPlain.markedRawMesh*Cycle63MarkedPlain.markedCoreMin/64 := by
      unfold Cycle63.FinalAssembly.geometryChosenMesh Cycle63MarkedPlain.markedGeometryMesh
      exact min_le_right _ _
    have hr := Cycle63MarkedPlain.marked_raw_mesh_gates.1
    have hc : (0:ℝ) < Cycle63MarkedPlain.markedCoreMin := Cycle63MarkedPlain.markedCoreMin_pos
    have hprod := mul_pos hr hc
    linarith
  have h2 := Cycle63.FinalAssembly.geometry_chosen_mesh_two_level ε
  obtain ⟨τ,hτ,_hτcap,hpaid⟩:=actual_affine_main_uniform_paid_two_level (α:=Fin D.N)
    S.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad
    W hW hs hβlo hβhi ηl 1 row 1 (by norm_num) (ε/4) mesh bΦ hε4 hmeshlt hmesh0.le
    hmeshμ hmeshcap (hmesh.trans h2.1) ((mul_le_mul_of_nonneg_left hmesh (by norm_num)).trans h2.2) hmarked hbΦ
  have hp:=hpaid (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_le_modulus S)
    (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates S ηl).1
    (internalQ_ne_top _ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_ne_top S) ηl)
    (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates S ηl).2.2.2
  have hex : excluded row.character 1 = ηl := detector_label_excluded S η label
  rw [hex] at hp
  have herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset (Fin D.N),∃Se : Finset (ℕ×ℕ),∃De : ℕ,∃Ce : ℝ,0≤ Ce ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          GeometryAffineErrorPaidSpec S.modulus ⊤ le_top S.S W hW.continuous hs Ψ ηl ηl mesh (ε/4)
            T Se De Ce Z := by
    intro Ψ _ _
    apply actual_affine_error_uniform_paid_of_normalized (α:=Fin D.N) S.modulus ⊤ le_top
      0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad W hW.continuous hs Ψ ηl ηl (ε/4) mesh
      hε4 hmeshlt (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) ηl) (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_ne_top S) ηl)
      (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates S ηl).2.2.2
    exact actual_affine_error_normalized_family (α:=Fin D.N) S.modulus ⊤ le_top
      S.S S.exclusions.bad W hW hs hβlo Ψ ηl ηl (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S)
      (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_le_modulus S) (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_ne_top S) ηl)
      (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates S ηl).2.2.2 (ε/4) mesh hε4 hmesh0.le hmeshlt hmeshμ hmeshcap
  have hbudget := literal_affine_geometry_budget_of_main_error S.modulus ⊤ le_top S.S S.exclusions.bad
    W hW.continuous hs ηl ηl (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) bΦ mesh (ε/4) τ hε4 hmeshlt hp herror
  obtain ⟨degree,Sd,C,hC,hev⟩ := literal_geometry_initial_affine (α:=Fin D.N) S.modulus ⊤ le_top
    W hW hs ηl ηl (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) bΦ mesh ε τ (geometryLossUnit 1 (ε/4)/64)
    (by linarith) hmesh0 hε hτ
    (div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) hε4) (by norm_num))
    (hmesh.trans hm.2.1) hβlo (by linarith) (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_le_modulus S)
    (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates S ηl).1 (internalQ_ne_top _ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_ne_top S) ηl)
    (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates S ηl).2.2.2 logAnnulus_compact logAnnulus_smooth hbudget
  exact ⟨degree,Sd,C,hC,hev⟩

end
end OAI.SevenEighths.Cycle63InitialMass

namespace OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate ContDiff
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle25ProbeFinalAssembly ProbeFinalAssembly
open Cycle25ProbeDetectorPlainMarkedFineField
open CenteredMomentNaturalFixedRaySource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorEnergyInitialState
open Cycle25CenteredMomentDetectorPlainMarkedState CenteredMomentDetectorDictionary
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentDetectorPlainFiberSource

/-- The detector affine moment holds for every source at the detector mesh. -/
theorem actual_detector_affine_input : DetectorAffineInputAt Cycle63.CountAffine.detectorMesh := by
  intro D S hβlo hβhi hfineA η
  obtain ⟨b0,_hb0,hsource⟩ := weighted_source_batch_marked_initial 0 S
  let bΦ : ℝ := max b0 2
  have hlab : ∀label : Sum Bool (RayQuotient.Characters S.modulus ⊤),
      ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,
      Cycle63Moment.InitialAffineAt (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ (Cycle63.CountAffine.detectorMesh D.t)
        (33/50) (33/50) 1 1 D.t U
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)
        (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) degree Sd C :=
    fun label => Cycle63InitialMass.detector_label_initial_affine S η label hβlo hβhi D.t D.t_pos
      (Cycle63.CountAffine.detectorMesh D.t) (Cycle63.CountAffine.detectorMesh_pos D.t_pos)
      (le_of_eq (Cycle63InitialMass.detectorMesh_eq D.t)) bΦ (le_max_right _ _)
  choose deg Sl Cl hCl hev using hlab
  let Dmax : ℕ := Finset.univ.sup deg
  let Sall : Finset (ℕ×ℕ) := Finset.univ.biUnion Sl
  obtain ⟨J₀,Cprofile,hCprofile,hprofile⟩ :=
    CenteredMomentDetectorPlainProfileControl.source_height_factor Sall
  let Csum : ℝ := 1+∑label,Cl label
  have hCsum : 0<Csum := by
    have h := Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hCl label).le)
    dsimp [Csum]; linarith
  have hClabel (label) : Cl label ≤ Csum := by
    have h := Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hCl label).le)
      (Finset.mem_univ label)
    dsimp [Csum]; linarith
  choose U₀ hU₀ using fun label=>Filter.eventually_atTop.mp (hev label)
  have hscale : ∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ) ≤ d→U₀ label ≤ Z^d := by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  have hdiag : 0 ≤ diagonalControl radialMajorant := diagonalControl_nonneg _
  refine ⟨J₀+Dmax,Csum*(1+diagonalControl radialMajorant)*Cprofile,by positivity,?_⟩
  filter_upwards [hsource η D.t D.t_pos,hscale] with Z hs hscale
  refine ⟨hs.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal selected hselected hm1 hm2 hw1 hw2 hcapA j k hjk
    σ hσ t ht
  let F := B.fiber bin label left right hne
  have hdpos : 0<d := by linarith
  have hU : 1<Z^d := Real.one_lt_rpow hs.1 hdpos
  obtain ⟨state,hchar,_hQ,hpuncture,hΦ,hK,hkeep,_hwidthstate,_hcapacity,hwidths,hrow⟩ :=
    hs.2 rows hrows d hd a D.ε tstar T allowance i B hB hdata hprof hwidth hupper hreal
      bin label left right hne selected hselected (by
        have : F.m ≤ Cycle63.CountAffine.plainLengthTop := hm2
        simp only [mul_zero, zero_mul, add_zero]
        simp only [Cycle63.CountAffine.plainLengthTop] at this
        linarith)
  let ηl := sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let p := OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_detectorProfiles F.reverse j k σ t
  have heq := CenteredMomentDetectorPlainRelativeClass.energy_eq S.modulus ⊤ le_top
    state.character ηl (fun (_:selected)=>1) state.mask 1
    (p.profile 0) (p.profile 1) (fun _=>2) (fun s:selected=>(Z^d)^(F.widths s.val))
    (fun s I=>HeckePrimeAnnular.annularWeight (fun x=>conj (S.W x))
      ((Z^d)^(F.widths s.val)) (33/50) (-(F.external s.val).im) I)
    0 ((Z^d)^F.m) ((Z^d)^F.m) state.radial.keep state.radial.profile state.radial.scale
  have hlen : CenteredMomentEnergyBands.length (Z^d) ((Z^d)^F.m) = F.m :=
    OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState.weighted_plain_length_eq F hU
  have hwsum : (∑s:selected,F.widths s.val) = ∑s∈selected,F.widths s := Finset.sum_coe_sort _ _
  have hwmesh (s:selected) : F.widths s.val ≤ Cycle63.CountAffine.detectorMesh D.t := by
    change B.widths s.val ≤ Cycle63.CountAffine.detectorMesh D.t
    rw [hwidth]
    apply (div_le_iff₀ hdpos).mpr
    have := hfineA s.val
    nlinarith [Cycle63.CountAffine.detectorMesh_pos D.t_pos]
  have hsupp : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ := by
    intro x hx
    have := state.radial_support (by rw [hΦ]; exact hx)
    exact (show x ≤ b0 from this).trans (le_max_left _ _)
  have hw1' : Cycle63.AffineLedger.slotFloor ≤ ∑ s ∈ selected, F.widths s := hw1
  have hw2' : ∑ s ∈ selected, F.widths s ≤ Cycle63.AffineLedger.slotTop := hw2
  have hcapA' : 2 * F.m + Cycle63.AffineLedger.lam * ∑ s ∈ selected, F.widths s ≤ Cycle63.AffineLedger.B := hcapA
  have hb := hU₀ label (Z^d) (hscale label d hd) selected (fun _=>1)
    (fun s=>F.widths s.val) (fun _=>(33/50:ℝ)) (fun s=>-(F.external s.val).im) 0 height
    (fun s=>(hwidths s).1.le) hwmesh (fun _=>le_rfl) (fun _=>le_rfl) hheight
    (fun s=>by
      change |-(B.external s.val).im| ≤ height
      simpa only [abs_neg] using hexternal s.val)
    1 le_rfl le_rfl radialMajorant hsupp radialMajorant_nonneg p ((Z^d)^F.m) ((Z^d)^F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by rw [hlen]; linarith) (by rw [hlen]; linarith) (by rw [hlen]; linarith) (by rw [hlen]; linarith)
    (by rw [hwsum]; linarith) (by rw [hwsum]; linarith)
    (by
      rw [hlen, hwsum]
      linarith)
  have hmask : state.mask = CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1 := by
    unfold CenteredMomentEnergyState.NaturalState.mask; rw [hpuncture]
  have hkeep' : state.radial.keep =
      initialKeep ηl (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) ηl) :=
    hkeep
  have hstep : energy state.character state.mask 1 0 (p.profile 0) (p.profile 1)
      (fun s:selected=>CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
      (fun (s:selected) I=>idealCoeff
          (relativeCharacter S.modulus ⊤ le_top ηl ((fun (_:selected)=>(1:RayQuotient.Characters S.modulus ⊤)) s)) I*
        HeckePrimeAnnular.annularWeight (fun x=>conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
          (-(F.external s.val).im) I)
      (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
      state.radial.keep state.radial.profile state.radial.scale ≤
      Cl label*diagonalControl radialMajorant*(p.control (Sl label))^2*
        (1+|(0:ℝ)|+height)^(deg label)*(Z^d)^(1+D.t) := by
    rw [hchar, hmask, hkeep', hΦ, hK]
    simpa only [Real.rpow_one] using hb
  have hnorm := hprofile Dmax F.reverse j k hjk σ hσ height t hheight (abs_le.mpr ht)
  have hpS : (p.control (Sl label))^2 ≤ (p.control Sall)^2 :=
    pow_le_pow_left₀ (p.control_nonneg _)
      (Cycle63Physical.profile_control_mono p (Finset.subset_biUnion_of_mem Sl (Finset.mem_univ label))) 2
  have hbase : 1 ≤ 1+|(0:ℝ)|+height := by simp only [abs_zero]; linarith
  have hpowD : (1+|(0:ℝ)|+height)^(deg label) ≤ (1+|(0:ℝ)|+height)^Dmax :=
    pow_le_pow_right₀ hbase (Finset.le_sup (Finset.mem_univ label))
  have hZpow : 0 ≤ (Z^d)^(1+D.t) := Real.rpow_nonneg (Real.rpow_nonneg (by linarith [hs.1]) _) _
  calc _ ≤ _ := hrow j k σ t
    _ = _ := heq
    _ ≤ _ := hstep
    _ ≤ (Csum*(1+diagonalControl radialMajorant))*
          ((p.control Sall)^2*(1+|(0:ℝ)|+height)^Dmax)*(Z^d)^(1+D.t) := by
      have e1 : Cl label*diagonalControl radialMajorant ≤ Csum*(1+diagonalControl radialMajorant) :=
        mul_le_mul (hClabel label) (by linarith) hdiag hCsum.le
      have e2 : (p.control (Sl label))^2*(1+|(0:ℝ)|+height)^(deg label) ≤
          (p.control Sall)^2*(1+|(0:ℝ)|+height)^Dmax :=
        mul_le_mul hpS hpowD (pow_nonneg (by linarith) _) (sq_nonneg _)
      have e3 := mul_le_mul e1 e2 (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _))
        (mul_nonneg hCsum.le (by linarith))
      have e4 := mul_le_mul_of_nonneg_right e3 hZpow
      calc _ = (Cl label*diagonalControl radialMajorant)*
            ((p.control (Sl label))^2*(1+|(0:ℝ)|+height)^(deg label))*(Z^d)^(1+D.t) := by ring
        _ ≤ _ := e4
    _ ≤ (Csum*(1+diagonalControl radialMajorant))*(Cprofile*(1+height)^(J₀+Dmax))*(Z^d)^(1+D.t) := by
      apply mul_le_mul_of_nonneg_right _ hZpow
      exact mul_le_mul_of_nonneg_left hnorm (mul_nonneg hCsum.le (by linarith))
    _ = _ := by ring

end
end OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
