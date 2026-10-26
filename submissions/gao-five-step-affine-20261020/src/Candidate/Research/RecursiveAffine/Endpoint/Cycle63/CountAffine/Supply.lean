/- The same literal root estimate supplies all detector labels.
Copyright (c) 2026 Hailey Collet; adaptation (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.CountAffine.SourceMoments
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.CountAffine.Mesh
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceNaturalRow
import Candidate.Research.RecursiveAffine.Endpoint.RootMomentFactory
variable [Cycle153Endpoint.RootMomentFactory]


noncomputable local instance endpointFixedLedger_Candidate_Cycle63_CountAffine_Supply : Cycle63.AffineLedger := Cycle153.Root.rootLedger

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153EndpointSource
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate SchwartzMap HeckeNotation
open Filter HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open ProbePhysical CenteredMomentDetectorDictionary Cycle153EndpointProbeFinalAssembly
open Cycle63InitialMass CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentLogDyadic

theorem source_modulus_le_mask {D : WeightedQRH.MomentData} (S : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) :
    S.modulus ≤ Ideal.span {fixedBadMask} := by
  have h := source_product_le_rowMask S.S S.exclusions.bad
  have e : ProbeHighRowFamily.rowMaskElement = fixedBadMask := by
    unfold ProbeHighRowFamily.rowMaskElement fixedBadMask; ring
  rw [e] at h
  exact h

/-- The inverse residue character keeps the same excluded-one identity. -/
theorem source_ofResidue_inverse (M : Ideal O) (hM : M ≠ ⊥) (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) :
    (Character.ofResidue M hM χ hu).inverse =
      Character.ofResidue M hM χ⁻¹ (Character.ofResidue M hM χ hu).inverse.unit_trivial := rfl

theorem source_excluded_one_inverse_ofResidue (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) :
    excluded (Character.ofResidue M hM χ hu).inverse 1 = (Character.ofResidue M hM χ hu).inverse := by
  rw [source_ofResidue_inverse]
  exact excluded_one_ofResidue _ _ _ _

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
    exact source_excluded_one_inverse_ofResidue _ _ _ _

end
end OAI.SevenEighths.Cycle153EndpointSource

namespace OAI.SevenEighths.Cycle153EndpointProbeFinalAssemblyCertifiedBands
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate ContDiff
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle153EndpointProbeFinalAssembly ProbeFinalAssembly
open Cycle153EndpointProbeDetectorPlainMarkedFineField
open CenteredMomentNaturalFixedRaySource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorEnergyInitialState
open Cycle25CenteredMomentDetectorPlainMarkedState CenteredMomentDetectorDictionary
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional

/-- Profile-control monotonicity is independent of any endpoint estimate. -/
private theorem source_profile_control_mono {a b : ℝ} (p : Profiles a b)
    {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T) : p.control S ≤ p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

/-- The detector affine moment holds for every source at the detector mesh. -/
theorem actual_detector_affine_input : DetectorAffineInputAt Cycle153Endpoint.CountAffine.detectorMesh := by
  intro D S hβlo hβhi hfineA η
  obtain ⟨b0,_hb0,hsource⟩ := weighted_source_batch_marked_initial 0 S
  let bΦ : ℝ := max b0 2
  have hlab : ∀label : Sum Bool (RayQuotient.Characters S.modulus ⊤),
      ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      Cycle153EndpointMoment.InitialAffineAt (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ (Cycle153Endpoint.CountAffine.detectorMesh D.t)
        (33/50) (33/50) 1 1 D.t U
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)
        (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal S) degree Sd C :=
    fun label => Cycle153Endpoint.RootMomentFactory.moment S _
      (Cycle153EndpointSource.detector_label_modulus S η label)
      (Cycle153EndpointSource.detector_label_excluded S η label)
      D.t (Cycle153Endpoint.CountAffine.detectorMesh D.t) bΦ D.t_pos
      (Cycle153Endpoint.CountAffine.detectorMesh_pos D.t_pos)
      (Cycle153Endpoint.CountAffine.detectorMesh_le_moment D.t) (le_max_right _ _)
      hβlo hβhi
  choose deg Sl Cl hCl hev using hlab
  let Dmax : ℕ := Finset.univ.sup deg
  let Sall : Finset (ℕ×ℕ) := Finset.univ.biUnion Sl
  obtain ⟨J₀,Cprofile,hCprofile,hprofile⟩ :=
    CenteredMomentDetectorPlainProfileControl.source_height_factor Sall
  let Csum : ℝ := 1+∑label,Cl label
  have hCsum : 0< Csum := by
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
  have hdpos : 0< d := by linarith
  have hU : 1< Z^d := Real.one_lt_rpow hs.1 hdpos
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
  have hwmesh (s:selected) : F.widths s.val ≤ Cycle153Endpoint.CountAffine.detectorMesh D.t := by
    change B.widths s.val ≤ Cycle153Endpoint.CountAffine.detectorMesh D.t
    rw [hwidth]
    apply (div_le_iff₀ hdpos).mpr
    have := hfineA s.val
    nlinarith [Cycle153Endpoint.CountAffine.detectorMesh_pos D.t_pos]
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
      (source_profile_control_mono p (Finset.subset_biUnion_of_mem Sl (Finset.mem_univ label))) 2
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
end OAI.SevenEighths.Cycle153EndpointProbeFinalAssemblyCertifiedBands

#print axioms OAI.SevenEighths.Cycle153EndpointProbeFinalAssemblyCertifiedBands.actual_detector_affine_input
