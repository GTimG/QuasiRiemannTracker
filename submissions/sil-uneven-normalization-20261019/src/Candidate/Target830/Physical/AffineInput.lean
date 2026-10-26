/- Actual detector-label transport for the two new source planes.
Adapted DaysSky/Hailey Collet/PR60 source, Apache-2.0. -/
import Candidate.Affine.Supply
import Candidate.Target830.Physical.Contract
import Candidate.Target830.Count.MarkedFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Target830.Physical.InitialTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate ContDiff
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle25ProbeFinalAssembly ProbeFinalAssembly Cycle25ProbeDetectorPlainMarkedFineField
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open Cycle25CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorEnergyInitialState
open Cycle25CenteredMomentDetectorPlainMarkedState CenteredMomentDetectorDictionary
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentDetectorPlainFiberSource

def countPlane : SourcePlane → Count.Plane | .A => .A | .C => .C
@[simp] theorem countPlane_lambda (P : SourcePlane) : (countPlane P).lambda=P.lambda := by cases P <;> rfl
@[simp] theorem countPlane_B (P : SourcePlane) : (countPlane P).B=P.B := by cases P <;> rfl

def weighted_AffineFineInputAt (plane : Count.Plane) {D:Cycle25.Weighted.MomentData}
    (S:Cycle25ProbeFinalAssembly.WeightedSourceData D) : Prop :=
  ∀η:Character,∃J:ℕ,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
    ∀d:ℝ,(1/200:ℝ) ≤ d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0 ≤ height→(∀s,|(B.external s).im| ≤ height)→
    Count.lowerPlain plane ≤ (B.fiber bin label left right hne).m →
    (B.fiber bin label left right hne).m ≤ Count.mHi →
    Count.AffineMarkedMoment (B.fiber bin label left right hne) plane (C*(1+height)^J) height D.t


def LabelInitialMoments (plane : SourcePlane) {D : Cycle25.Weighted.MomentData}
    (S : WeightedSourceData D) (mesh : ℝ) : Prop :=
  ∀ η : Character, ∀ bPhi : ℝ, 2 ≤ bPhi →
  ∀ label : Sum Bool (RayQuotient.Characters S.modulus ⊤),
    let etaL := sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃ degree : ℕ, ∃ seminorms : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop,
        Physical.InitialAffineAt (P:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
          (fun x=>conj (S.W x)) 2 (1/4) (9/4) bPhi mesh
          (33/50) (33/50) 1 1 D.t U etaL etaL
          (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal S)
          degree seminorms C

/-- Actual batch transport, conditional on the still-required new source
moment supplier. Constants precede all moving rows, heights and selected slots. -/
theorem actual_detector_affine_input_of_initial (plane : SourcePlane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hfineA : ∀ j, D.ell j ≤ mesh/200)
    (hlabel : LabelInitialMoments plane S mesh) :
    weighted_AffineFineInputAt (countPlane plane) S := by
  intro η
  obtain ⟨b0,_hb0,hsource⟩ := weighted_source_batch_marked_initial 0 S
  let bΦ : ℝ := max b0 2
  have hlab : ∀label : Sum Bool (RayQuotient.Characters S.modulus ⊤),
      ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,
      Physical.InitialAffineAt (P:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 D.t U
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)
        (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal S) degree Sd C :=
    fun label => hlabel η bΦ (le_max_right _ _) label
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
    bin label left right hne height hheight hexternal
  intro hm1 hm2 selected hselected hw1 hw2 hcapA j k hjk σ hσ t ht
  rw [countPlane_lambda,countPlane_B] at hcapA
  let F := B.fiber bin label left right hne
  have hdpos : 0<d := by linarith
  have hU : 1<Z^d := Real.one_lt_rpow hs.1 hdpos
  obtain ⟨state,hchar,_hQ,hpuncture,hΦ,hK,hkeep,_hwidthstate,_hcapacity,hwidths,hrow⟩ :=
    hs.2 rows hrows d hd a D.ε tstar T allowance i B hB hdata hprof hwidth hupper hreal
      bin label left right hne selected hselected (by
        have : F.m ≤ 44/100 := hm2.trans (by norm_num [Count.mHi,kappa0,widthLower])
        simp only [mul_zero, zero_mul, add_zero]
        linarith)
  let ηl := sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let p := weighted_detectorProfiles F.reverse j k σ t
  have heq := CenteredMomentDetectorPlainRelativeClass.energy_eq S.modulus ⊤ le_top
    state.character ηl (fun (_:selected)=>1) state.mask 1
    (p.profile 0) (p.profile 1) (fun _=>2) (fun s:selected=>(Z^d)^(F.widths s.val))
    (fun s I=>HeckePrimeAnnular.annularWeight (fun x=>conj (S.W x))
      ((Z^d)^(F.widths s.val)) (33/50) (-(F.external s.val).im) I)
    0 ((Z^d)^F.m) ((Z^d)^F.m) state.radial.keep state.radial.profile state.radial.scale
  have hlen : CenteredMomentEnergyBands.length (Z^d) ((Z^d)^F.m) = F.m :=
    weighted_plain_length_eq F hU
  have hwsum : (∑s:selected,F.widths s.val) = ∑s∈selected,F.widths s := Finset.sum_coe_sort _ _
  have hwmesh (s:selected) : F.widths s.val ≤ mesh := by
    change B.widths s.val ≤ mesh
    rw [hwidth]
    apply (div_le_iff₀ hdpos).mpr
    have := hfineA s.val
    nlinarith [hmesh]
  have hsupp : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ := by
    intro x hx
    have := state.radial_support (by rw [hΦ]; exact hx)
    exact (show x ≤ b0 from this).trans (le_max_left _ _)
  have hplainLo : plainLower ≤ F.m := by
    have hh := (Count.plane_plain_window (countPlane plane)).1
    have hlo : plainLower ≤ Count.lowerPlain (countPlane plane) :=
      (by norm_num [plainLower] : plainLower ≤ (41/100:ℝ)).trans hh.le
    exact hlo.trans hm1
  have hplainHi : F.m ≤ plainUpper := hm2.trans
    (Count.plane_plain_window (countPlane plane)).2.le
  have hb := hU₀ label (Z^d) (hscale label d hd) selected (fun _=>1)
    (fun s=>F.widths s.val) (fun _=>(33/50:ℝ)) (fun s=>-(F.external s.val).im) 0 height
    (fun s=>(hwidths s).1.le) hwmesh (fun _=>le_rfl) (fun _=>le_rfl) hheight
    (fun s=>by
      change |-(B.external s.val).im| ≤ height
      simpa only [abs_neg] using hexternal s.val)
    1 le_rfl le_rfl radialMajorant hsupp radialMajorant_nonneg p ((Z^d)^F.m) ((Z^d)^F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by rw [hlen]; simpa only [mul_one] using hplainLo)
    (by rw [hlen]; simpa only [mul_one] using hplainHi)
    (by rw [hlen]; simpa only [mul_one] using hplainLo)
    (by rw [hlen]; simpa only [mul_one] using hplainHi)
    (by rw [hwsum]; linarith) (by rw [hwsum]; linarith)
    (by
      rw [hlen, hwsum]
      linarith)
  have hmask : state.mask = CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1 := by
    unfold CenteredMomentEnergyState.NaturalState.mask; rw [hpuncture]
  have hkeep' : state.radial.keep =
      initialKeep ηl (internalQ (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal S) ηl) :=
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
end OAI.SevenEighths.Target830.Physical.InitialTransport
#print axioms OAI.SevenEighths.Target830.Physical.InitialTransport.actual_detector_affine_input_of_initial
