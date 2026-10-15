/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B018
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B037
import Submissions.local44_20261013.Bundles.B052
import Submissions.local44_20261013.Bundles.B053
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSecondActiveErrorGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorArithmetic

/- BEGIN ORIGINAL MODULE Global.Transport.NonfloorNormalized ; sha256 1b0ca61fe0299013b1de1805aad868c2e95ee1f221e2c89e6e6a7f59d1399be4 -/
section
/- Adapted from weighted upstream PR6; original proof structure retained. -/





open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_normalized_nonfloor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0 < dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (μ : ℝ)
    (hfinal : (159*ε+εm+R+7*ν)+(12*e+eps*(N+8))+
      (logCost+heightCost+momentCost+loss+mesh*Submission20261012.Global.ell+(16-6*Submission20261012.Global.ly)*e)+μ≤1/4000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0 < nu) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 < C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤ d → d-v≤μ →
      51/100 < a → a≤7/8 → Submission20261012.Global.Transport.OriginalBranch d a → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ) < a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell (fun j y=>(W j y:ℂ)) Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) 0
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) (fun j y=>(W j y:ℂ)) Y
        W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (fun _=> a) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(Submission20261012.Global.signal Submission20261012.Global.theta-1/4000+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤ A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨C,hC,hbound⟩ :=
    actual_nonfloor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm ν logCost heightCost momentCost hεm hν hlog hMomentHeight
      μ hfinal
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 counts
  have hellpos (j : Fin N) : 0 < ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := Submission20261012.Global.LowNormalizer.actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C*Cn,mul_pos hC hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hbranch hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only at hn ⊢
  intro hmom
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v a C0 hv hv' hdv ha ha' hbranch hC0 rows hrows hnorm i hi hnext hcurrent hmom
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (Submission20261012.Global.signal Submission20261012.Global.theta-1/4000) nu]
  ring

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.NonfloorNormalized -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderTransport ; sha256 c69175ad4e8e1266203de29d71e8ba1175c51e919405612faec628d448954015 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/



noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace Submission20261012.Global.Transport.PrincipalTransport
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalTransport
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
open Submission20261012.Global.Transport.PrincipalFiniteProduct Submission20261012.Global.Transport.PrincipalFiniteProductX Submission20261012.Global.Transport.PrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma gaussianMoment_tendsto (n : ℕ) : Tendsto (gaussianMoment n) atTop (𝓝 0) := by
  have hb (t : ℝ) : gaussianMoment n t  ≤  (2:ℝ)^(n-1)*Continuation.polynomialGaussian n t := by
    have h := add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg t) n
    unfold gaussianMoment height Continuation.polynomialGaussian
    calc
      _  ≤  ((2:ℝ)^(n-1)*(1^n+|t|^n))*Real.exp (-(t^2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by simp only [one_pow]; ring
  exact squeeze_zero (gaussianMoment_nonneg n) hb
    (by simpa using (Continuation.polynomialGaussian_tendsto n).const_mul ((2:ℝ)^(n-1)))

lemma gaussianMoment_even (n : ℕ) (t : ℝ) : gaussianMoment n (-t)=gaussianMoment n t := by
  simp [gaussianMoment,height]

lemma shifted_gaussian_integrable (n : ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => gaussianMoment n (t+v)) := by
  exact (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussianMoment_integrable n)

lemma shifted_gaussian_top (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (t+v)) atTop (𝓝 0) :=
  (gaussianMoment_tendsto n).comp (tendsto_atTop_add_const_right _ v tendsto_id)

lemma shifted_gaussian_bottom (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (-t+v)) atTop (𝓝 0) :=
by
  convert shifted_gaussian_top n (-v) using 1
  funext t
  rw [←gaussianMoment_even n (t + -v)]
  congr 1
  ring

theorem verticalIntegral_eq_of_shifted_gaussian (F : ℂ → ℂ) {a c A : ℝ}
    (n : ℕ) (v : ℝ) (hac : a ≤ c)
    (hF : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ c})
    (hb : ∀σ∈Icc a c,∀t : ℝ,‖F ((σ:ℂ)+t*I)‖ ≤ A*gaussianMoment n (t+v)) :
    verticalIntegral a F=verticalIntegral c F := by
  have hc (σ : ℝ) (hσ : σ∈Icc a c) : Continuous (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  have hi (σ : ℝ) (hσ : σ∈Icc a c) : Integrable (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    ((shifted_gaussian_integrable n v).const_mul A).mono' (hc σ hσ).aestronglyMeasurable
      (Eventually.of_forall (hb σ hσ))
  have hj (T : ℝ) : ‖∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)‖ ≤ A*gaussianMoment n (T+v)*|c-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hb σ (by simpa [uIcc_of_le hac] using uIoc_subset_uIcc hσ) T
  have ht : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hj
      (by simpa using ((shifted_gaussian_top n v).const_mul A).mul_const |c-a|)
  have hbot : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+(-T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa only [Complex.ofReal_neg] using hj (-T))
      (by simpa using ((shifted_gaussian_bottom n v).const_mul A).mul_const |c-a|)
  unfold verticalIntegral
  congr 1
  exact Continuation.vertical_integral_eq_of_horizontal_vanish F hac hF
    (hi a ⟨le_rfl,hac⟩) (hi c ⟨hac,le_rfl⟩) hbot ht

theorem principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta< a) (hξlo : 1/6<ξlo) :
    ∃ A : ℝ,0 ≤ A ∧ ∀σ∈Icc a 3,∀ξ∈Icc ξlo 2,∀p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2*I)‖ ≤ A*jointEnvelope 8 p := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith [Submission20261012.Global.Transport.theta_bounds]) 10
  obtain ⟨E,hE,he⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
  let B := realGaussianBound a 3 ξlo 2*2^8*D*E
  have hA : 0 ≤ A := Submission20261012.Global.Transport.PrincipalContours.arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
    (by norm_num) hC (by norm_num) (by linarith [Submission20261012.Global.Transport.theta_bounds])
  have hB : 0 ≤ B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ∈Icc (33/200 : ℝ) 2 := ⟨by linarith [Submission20261012.Global.Transport.theta_bounds, hξ.1],hξ.2⟩
  have hw : (2:ℝ) ≤ ‖((3:ℂ)+p.2*I)-1‖ := by
    convert pole_distance_vertical 1 3 p.2 using 1; norm_num
  have hz : 6*ξlo-1 ≤ ‖6*((ξ:ℂ)+p.1.2*I)-1‖ := by
    have h := Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)
    have hh : 0 ≤ 6*ξ-1 := by linarith [Submission20261012.Global.Transport.theta_bounds, hξ.1]
    simp only [sub_re,mul_re,ofReal_re,ofReal_im,add_re,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero,one_re] at h
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [Submission20261012.Global.Transport.theta_bounds, hξ.1]) h
  have hb := Submission20261012.Global.Transport.PrincipalContours.arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6*ξlo-1)
    (by norm_num) (by linarith [Submission20261012.Global.Transport.theta_bounds]) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl,le_rfl⟩) p
  rw [←Submission20261012.Global.Transport.PrincipalContours.arithmetic_profile_eq_source,norm_mul]
  calc
    _  ≤  (A*jointHeight p.1.1 p.1.2 p.2^8)*‖profile W0 W1
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines,ofReal_ofNat]; ring
    _  ≤  A*(B*jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := Submission20261012.Global.Transport.PrincipalFiniteProductX.continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3:ℂ)+u*I) ((ξ:ℂ)+v*I) (by norm_num) (by simpa using (show (4/25:ℝ) ≤ ξ by linarith [Submission20261012.Global.Transport.theta_bounds])) ha hβ
    (c:=3)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A:=A*cauchy v*cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl,hξ2⟩ ((t,v),u)
  simpa only [jointEnvelope,Prod.fst,Prod.snd,mul_assoc,mul_left_comm,mul_comm] using h

lemma continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : theta  ≤  s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4/25< z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25< z.re} := (ProbeRadialMellin.radial_mellin_differentiable W0).mono
        (by intro z hz; change 0< z.re; change (4/25:ℝ)< z.re at hz; linarith [Submission20261012.Global.Transport.theta_bounds])
  have hH := (Submission20261012.Global.Transport.PrincipalFiniteProduct.combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hnX : (X:ℂ)≠0 := by exact_mod_cast hX.ne'
  have hnZ : (Z:ℂ)≠0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)=
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s)*
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)) := by
    funext z; unfold continuedSourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

lemma continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : theta  ≤  s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1/6< z.re} := by
  have hK := continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4/25:ℝ)< z.re; change (1/6:ℝ)< z.re at hz; linarith [Submission20261012.Global.Transport.theta_bounds])).mul ?_).mul_const
  intro z hz
  have h0 : (6*z:ℂ)≠0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)< z.re at hz; linarith [Submission20261012.Global.Transport.theta_bounds]
  have h1 : (6*z:ℂ)≠1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)< z.re at hz; linarith [Submission20261012.Global.Transport.theta_bounds]
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta  ≤  a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a:ℂ)+t*I) ((3:ℂ)+u*I) (by simpa using ha) (by norm_num)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1/6:ℝ)< z.re; exact hξ.trans_le hz.1)) (A:=A*cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl,ha3⟩ ζ hζ ((t,v),u)
  calc
    _  ≤  A*(gaussianMoment 8 (t+v)*cauchy v*cauchy u) := h
    _  ≤  A*(gaussianMoment 8 (t+v)*1*cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t+v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

lemma verticalIntegral_swap (F : ℂ → ℂ → ℂ) (a b : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ => F ((a:ℂ)+q.1*I) ((b:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun z => verticalIntegral b (F z))=
      verticalIntegral b (fun w => verticalIntegral a (fun z => F z w)) := by
  simp only [verticalIntegral,integral_const_mul]
  congr 2
  exact integral_integral_swap (f:=fun t u : ℝ => F ((a:ℂ)+t*I) ((b:ℂ)+u*I)) hi

lemma verticalIntegral_triple_reverse (F : ℂ → ℂ → ℂ → ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace => F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w => F s w z)))=
      verticalIntegral υ (fun w => verticalIntegral ξ (fun z => verticalIntegral a (fun s => F s w z))) := by
  have h1 := integral_prod _ hi
  have h2 := integral_prod _ hi.integral_prod_left
  have h3 := integral_prod_symm _ hi
  have h4 : (∫u : ℝ,∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume)=
      ∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) := by
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu
  have he := h2.symm.trans (h1.symm.trans (h3.trans h4))
  simp only [verticalIntegral,integral_const_mul]
  congr 3

lemma verticalIntegral_congr_line (F G : ℂ → ℂ) (a : ℝ)
    (h : ∀t : ℝ,F ((a:ℂ)+t*I)=G ((a:ℂ)+t*I)) : verticalIntegral a F=verticalIntegral a G := by
  unfold verticalIntegral
  congr 1
  exact integral_congr_ae (Eventually.of_forall h)

theorem continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta< a) (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := Submission20261012.Global.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith [Submission20261012.Global.Transport.theta_bounds]) (by norm_num) (by norm_num) (by linarith [Submission20261012.Global.Transport.theta_bounds]) (by norm_num)
  have hi3 := Submission20261012.Global.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds])) (hβ.trans_le ha3) (by linarith [Submission20261012.Global.Transport.theta_bounds])
    (by norm_num) (by norm_num) (by linarith [Submission20261012.Global.Transport.theta_bounds]) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  rw [verticalIntegral_triple_reverse F a ξ 3 hiA,verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply verticalIntegral_congr_line
  intro u
  apply verticalIntegral_congr_line
  intro v
  exact continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta  ≤  a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta< a) (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ,Kξ,hCξ,hKξ,hξi⟩ := Submission20261012.Global.Transport.PrincipalContours.continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha hβ (by linarith [Submission20261012.Global.Transport.theta_bounds]) (by norm_num) (by norm_num) (by linarith [Submission20261012.Global.Transport.theta_bounds]) (by norm_num) 0
  obtain ⟨C2,K2,hC2,hK2,h2i⟩ := Submission20261012.Global.Transport.PrincipalContours.continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 3 3 hX hY hZ ha hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  apply verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) ξ 3 hiξ,
    verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) 2 3 hi2]
  apply verticalIntegral_congr_line
  intro u
  exact continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

lemma continued_triple_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w)))=
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w))) := by
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  have h0 : (a:ℂ)+t*I≠0 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+t*I≠1 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  simp_rw [Submission20261012.Global.Transport.PrincipalFiniteProductX.continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
  dsimp only
  rw [←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1/6+e) 3]
  have hx := continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1/6+e) hX hY hZ ha.le ha3 hβ (by linarith [Submission20261012.Global.Transport.theta_bounds]) (by linarith [Submission20261012.Global.Transport.theta_bounds])
  exact hx.symm.trans hz.symm

theorem source_initial_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  exact (source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (Submission20261012.Global.Transport.PrincipalContours.source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)

theorem source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := source_initial_ordered_at_a η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2
  have hf := (Submission20261012.Global.Transport.PrincipalContours.source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds])) (hβ.trans_le ha3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hi : (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
      verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
        (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
    dsimp [K,π]
    simp only [ofReal_ofNat] at hf
    rw [hf]
    simp only [verticalIntegral,integral_const_mul,ofReal_ofNat]
    ring
  exact hi.trans hh

end Submission20261012.Global.Transport.PrincipalTransport
end

end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderTransport -/

/- BEGIN ORIGINAL MODULE Analytic.AllocatedBufferedData ; sha256 73d08efb4581a02d654d464890079632356ba07aa970949b80d12d0b48dd42d9 -/
section


/-! Canonical data for the actual allocated source product. Logarithmic
lengths recover the literal clipped and prime scales exactly; the live
slot subtype is transported by inclusion, with no cardinality payment. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedProfile CenteredMomentHeckeVolume CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRetained
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : Character} {w : NonzeroElement} {n : ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}

/-- The source allocation chooses the surviving slots. The only analytic
input here is the two plain profile records, supplied by uniform profile
bounds; all row characters and scale lengths are explicit. -/
def allocatedBufferedData (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (puncture : Ideal O) (hpuncture : puncture ≠ 0)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P₁ P₂ : BufferedPlainProfile n profileBound a e) (Z d X₁ X₂ : ℝ)
    (P : ι → ℝ) (t : ℝ) (bin : ℕ) :
    JointBufferedProductData η w (liveIndices D allocation) n profileBound a e where
  parent := parent
  natural := N
  puncture := puncture
  puncture_ne := hpuncture
  plain₁ := P₁
  plain₂ := P₂
  r₁ := Real.logb (Z^d) (clippedScale (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ)))
  r₂ := Real.logb (Z^d) (clippedScale (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ)))
  r := fun i => Real.logb (Z^d) (P i)
  σ := fun _ => 0
  v := fun _ => 0
  t := t
  bin := bin

lemma allocatedBufferedData_length
    (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (puncture : Ideal O) (hpuncture : puncture ≠ 0)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P₁ P₂ : BufferedPlainProfile n profileBound a e) (Z d X₁ X₂ : ℝ)
    (P : ι → ℝ) (t : ℝ) (bin : ℕ) :
    (allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin).length =
      Real.logb (Z^d) (clippedScale (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ)))+
      Real.logb (Z^d) (clippedScale (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ)))+
      ∑ i ∈ liveIndices D allocation, Real.logb (Z^d) (P i) := by
  exact congrArg (fun x =>
    Real.logb (Z^d) (clippedScale (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ)))+
    Real.logb (Z^d) (clippedScale (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ)))+x)
    (Finset.sum_coe_sort (liveIndices D allocation) (fun i : ι => Real.logb (Z^d) (P i)))

lemma allocated_live_card_le (D : Ideal O)
    (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    Fintype.card (liveIndices D allocation) ≤ Fintype.card ι := by
  simpa using Finset.card_le_univ (liveIndices D allocation)

/-- Literal value equality after replacing logarithmic lengths by their
source scales. Every surviving relative character is the original one. -/
theorem allocatedBufferedData_value
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (puncture : Ideal O) (hpuncture : puncture ≠ 0)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P₁ P₂ : BufferedPlainProfile n profileBound a e) (Z d X₁ X₂ : ℝ)
    (η₀ : ι → Character) (V : ι → ℝ → ℂ) (b P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (t : ℝ) (bin : ℕ) (hbase : 1 < Z^d) (hP : ∀ i, 0 < P i)
    (hW₁ : P₁.W = dilated W₁ (clipDilation (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))))
    (hW₂ : P₂.W = dilated W₂ (clipDilation (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))))
    (hσ₁ : P₁.σ = 0) (hσ₂ : P₂.σ = 0) (ht₁ : P₁.freq = t) (ht₂ : P₂.freq = t) :
    (allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin).value
      M H (fun i : liveIndices D allocation => η₀ i.val)
        (fun i : liveIndices D allocation => V i.val) (fun i : liveIndices D allocation => b i.val) Z d =
    allocatedBufferedValue M H parent.val (fixedBadMask*idealGenerator puncture) 1 w.val
      η₀ W₁ W₂ V b P t X₁ X₂ D allocation := by
  unfold JointBufferedProductData.value allocatedBufferedData allocatedBufferedValue
  have hc (X : ℝ) : 0 < clippedScale X := zero_lt_one.trans_le (clippedScale_ge_one X)
  simp only [Real.rpow_logb (zero_lt_one.trans hbase) (ne_of_gt hbase) (hc _),
    Real.rpow_logb (zero_lt_one.trans hbase) (ne_of_gt hbase) (hP _),
    hW₁,hW₂,hσ₁,hσ₂,ht₁,ht₂]

/-- The actual source allocated row is exactly the constructed product in
squared norm. The pure height phases have norm one. -/
theorem allocatedBufferedData_source_norm_sq
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (puncture : Ideal O) (hpuncture : puncture ≠ 0)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P₁ P₂ : BufferedPlainProfile n profileBound a e) (Z d X₁ X₂ : ℝ)
    (η₀ : ι → Character) (V : ι → ℝ → ℂ) (b P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (t : ℝ) (bin : ℕ) (hbase : 1 < Z^d) (hP : ∀ i, 0 < P i)
    (hW₁ : P₁.W = dilated W₁ (clipDilation (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))))
    (hW₂ : P₂.W = dilated W₂ (clipDilation (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))))
    (hσ₁ : P₁.σ = 0) (hσ₂ : P₂.σ = 0) (ht₁ : P₁.freq = t) (ht₂ : P₂.freq = t) :
    ‖allocatedPositiveRow parent.val (fixedBadMask*idealGenerator puncture) 1 w.val t
      (fun i => primePool M H (b i) (P i))
      (fun i I => idealCoeff (η₀ i).inverse I*V i ((I.absNorm : ℝ)/P i)) P
      D allocation W₁ W₂ X₁ X₂‖^2 =
    ‖(allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin).value
      M H (fun i : liveIndices D allocation => η₀ i.val)
        (fun i : liveIndices D allocation => V i.val) (fun i : liveIndices D allocation => b i.val) Z d‖^2 := by
  rw [allocatedBufferedData_value M H parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂
    η₀ V b P W₁ W₂ t bin hbase hP hW₁ hW₂ hσ₁ hσ₂ ht₁ ht₂]
  exact allocated_positive_norm_sq_eq_buffered M H parent.val
    (fixedBadMask*idealGenerator puncture) 1 w.val η₀ W₁ W₂ V b P (fun i => (hP i).le)
    t X₁ X₂ D allocation

#print axioms allocatedBufferedData_source_norm_sq
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.AllocatedBufferedData -/

/- BEGIN ORIGINAL MODULE Analytic.JointAllocatedPoolCongruence ; sha256 4fdecf1cba1d927bad81b1e014494679409028a945f7e1a1ae43484db7ff63fe -/
section


/-! Allocated products depend only on coefficients in their actual pools. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
local notation "O" => HeckeFamily.O

theorem allocatedPositiveRow_congr_coeff_on_pool
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β γ : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (h : ∀ i, ∀ I ∈ S i, β i I = γ i I) :
    allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂ =
      allocatedPositiveRow η m A z t S γ P D a W₁ W₂ X₁ X₂ := by
  unfold allocatedPositiveRow retainedPositiveRow positiveSlotRow
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [h i.val I hI]

#print axioms allocatedPositiveRow_congr_coeff_on_pool
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointAllocatedPoolCongruence -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalActiveError ; sha256 aacc136061d46200c803b816b8d18341f5914f8891c05e7af9618b6cfeebb83d -/
section




/-! Exceptional error powers with actual active-pool extracted inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst CenteredMomentFirstMixedExceptionalCap
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstChildLower CenteredMomentFirstAmplifiedFourCoefficients
local notation "O" => HeckeFamily.O
local instance jointExceptionalActiveErrorDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem actual_local_error_exceptional_reference_of_cap
    (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D))
    (hE : E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U})
    (K V Z sigma omega M r : ℝ) (hZ : 1 < Z) (hK : 0 < K) (hV : 0 < V)
    (hsigma : sigma ≤ 9/500)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D})
    (Mray : Ideal O) [NeZero Mray] (H : Subgroup (O ⧸ Mray)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (p0 : O) (hp0 : p0 ∈ elementPool (primePool Mray H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k = 1 ∨ k = 6 ∨ k = 7)
    (hM : 1 ≤ M) (hwidth : M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z V ≤ (883/1000)*M)
    (hcap : M/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p0 Z k ≤ r) :
    let Rerror := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) sigma omega 0 p0 k
    ((V/(C.absNorm : ℝ))*localErrorCost p0 (k-1)*
      (V/(C.absNorm : ℝ)/(normValue p0)^k)^(1/3 : ℝ)*Rerror^(5/6 : ℝ)/
      ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))^2*Z^(allowance C D Z)))*
        Z^(-2*max (r) 0/3) ≤ Z^(-9/100+5*omega/6) := by
  dsimp only
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc := commonPart_of_equal_support C D hC.1 hCD
  have hd := commonPart_of_equal_support D C hD.1 hCD.symm
  let Rerror := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
    (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) sigma omega 0 p0 k
  have hr : 0 < Rerror := by unfold Rerror errorCommonRadius; positivity
  have hs := CenteredMomentFirstMixedCommonRadius.actual_error_column_saving
    η τ fixedBadMask C D E hC hD U K V Z 0 sigma omega 0 hZ hmod
    Mray H Sbad hbad p0 hp0 k hk
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq C D hC.1 hD.1 hCD Z] at hs
  have hp := elementPool_data _
    (fun P hP => (primePool_data Mray H Sbad hbad (1/2) 1 (Z^(sigma/3)) P hP).1)
    (fun P hP => (primePool_data Mray H Sbad hbad (1/2) 1 (Z^(sigma/3)) P hP).2) p0 hp0
  have he := actual_error_reference_le η τ C D hC hD hCD U K V Z 0
    (Real.logb Z Rerror) hK hV hZ hmod p0 hp.1.ne_zero k hk
  dsimp only at he
  rw [←hE] at he
  simp only [zero_add] at he
  rw [Real.rpow_logb hz hZ.ne' hr] at he
  have hh := mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hh.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  dsimp only [Rerror] at *
  simp only [nominalLog,sub_zero,add_zero] at hs ⊢
  have hrmax := le_max_left r (0 : ℝ)
  linarith


/-- The lower plain scales survive the active-pool restriction and both
literal extractions. This supplies one cap uniformly over all allocations. -/
theorem actual_errorInput_plain_lower
    {ι : Type*} [Fintype ι]
    (s : Input ι) (C Rmask : Ideal O) (hC : C ≠ 0)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (p0 : O) (hp0 : p0 ≠ 0) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C Rmask B τ t)).pools ((Ideal.span {p0})^k))
    (υ : Character) (v Z M : ℝ) (hZ : 1 < Z)
    (hX₁ : Z^(M/4) ≤ s.X₁) (hX₂ : Z^(M/4) ≤ s.X₂)
    (hY₁ : Z^(M/4) ≤ s.Y₁) (hY₂ : Z^(M/4) ≤ s.Y₂) :
    let input := errorInput s C Rmask B τ t (Ideal.span {p0}) k Bp υ v
    let r := M/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p0 Z k
    Z^r ≤ input.X₁ ∧ Z^r ≤ input.X₂ ∧ Z^r ≤ input.Y₁ ∧ Z^r ≤ input.Y₂ := by
  have hQ : Ideal.span {p0} ≠ (0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hp0
  have hfirst := child_lower s C Rmask hC B τ t Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hsecond := child_lower (activeInput (child s C Rmask B τ t)) ((Ideal.span {p0})^k)
    (Rmask*C) (pow_ne_zero k hQ) Bp υ v Z (M/4-Real.logb Z (C.absNorm : ℝ)) hZ
    hfirst.1 hfirst.2.1 hfirst.2.2.1 hfirst.2.2.2
  have hnorm : ((Ideal.span {p0}).absNorm : ℝ) = normValue p0 := by
    simp only [normValue,eisEmbedding_norm_sq_eq_absNorm_span]
  have he : Real.logb Z (((Ideal.span {p0})^k).absNorm : ℝ) = errorRemoval p0 Z k := by
    rw [map_pow,Nat.cast_pow,Real.logb_pow,hnorm]
    rfl
  simpa only [he,errorInput] using hsecond

/-- Literal exceptional component of the four source error cores. Its
cap is the one just derived for every active extracted input. -/
theorem actual_local_error_core_one
    (η τ : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (K V Z sigma delta reserve M deficit paid eps saving : ℝ)
    (hZ : 1 < Z) (hK : 0 < K) (hV : 0 < V) (hsigma : sigma ≤ 9/500)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D})
    (Mray : Ideal O) [NeZero Mray] (H : Subgroup (O ⧸ Mray)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (p0 : O) (hp0 : p0 ∈ elementPool (primePool Mray H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k = 1 ∨ k = 6 ∨ k = 7)
    (hM : 1 ≤ M) (hwidth : M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z V ≤ (883/1000)*M) :
    let Rerror := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U}) K V Z)
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve p0 k
    errorCores p0 k (τ.modulus.absNorm : ℝ) V (C.absNorm : ℝ) Z (allowance C D Z)
      Rerror deficit paid eps saving
      (M/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p0 Z k) 1 ≤
        Z^(-9/100+5*(delta+reserve)/6) := by
  have hh := actual_local_error_exceptional_reference_of_cap η τ C D
    (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U}) hC hD hCD U rfl
    K V Z sigma (delta+reserve) M
    (M/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p0 Z k)
    hZ hK hV hsigma hmod Mray H Sbad hbad p0 hp0 k hk hM hwidth hvolume le_rfl
  dsimp only at hh ⊢
  have he : errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U}) K V Z)
      (Real.logb Z (C.absNorm : ℝ)) sigma (delta+reserve) 0 p0 k =
      errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U}) K V Z)
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve p0 k := by
    unfold errorCommonRadius
    congr 1
    ring
  rw [he] at hh
  convert hh using 1 <;> simp only [errorCores,reference,Matrix.cons_val_one,Matrix.cons_val_zero] <;> ring

#print axioms actual_local_error_exceptional_reference_of_cap
#print axioms actual_errorInput_plain_lower
#print axioms actual_local_error_core_one
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalActiveError -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalUniformChild ; sha256 be9929211c9ded8bf881ea318ad2eb9867d46c00ddecaed078695f8189f0a0ad -/
section


/-! Actual exceptional first children, with source-derived normalization,
profile control and the local negative exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstChildProfileControl CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondExceptionalUniformSource CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondEnergySplit
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open ConcretePrimeRowBridge RayFourExpansion
local notation "O" => HeckeFamily.O
local instance jointExceptionalUniformChildDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance jointExceptionalUniformChildDecEq2 {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

/-- A fixed original slot set has one Fourier order and one profile seminorm
for every surviving subset. The scalar constants may be selected afterwards. -/
lemma finite_exceptional_profile_control
    {ι : Type*} [Fintype ι] (orders : ι → ℕ)
    (seminorms : ι → Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ coeff : ι → ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ {wlo whi : ℝ} (p : Profiles wlo whi) (t : ℝ) (i : ι),
      coeff i*p.control (seminorms i)^2*(1+‖t‖)^(2*orders i) ≤
        C*p.control S^2*(1+‖t‖)^(2*J) := by
  let J := ∑ i, orders i
  let S := insert (0,0) (Finset.univ.biUnion seminorms)
  refine ⟨J,S,Finset.mem_insert_self _ _,?_⟩
  intro coeff
  let C := 1 + ∑ i, |coeff i|
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro wlo whi p t i
  have hc : coeff i ≤ C := by
    have hs : |coeff i| ≤ ∑ j, |coeff j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (coeff j)) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_abs_self (coeff i)]
  have hj : orders i ≤ J :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (orders j)) (Finset.mem_univ i)
  have hS : seminorms i ⊆ S := by
    intro q hq
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hq⟩)
  have hp : p.control (seminorms i) ≤ p.control S := by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hS) _)
      (Seminorm.le_def.mp (Finset.sup_mono hS) _)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hpsq := pow_le_pow_left₀ (p.control_nonneg (seminorms i)) hp 2
  have ht := pow_le_pow_right₀ (show (1:ℝ) ≤ 1+‖t‖ by linarith [norm_nonneg t])
    (Nat.mul_le_mul_left 2 hj)
  calc
    _ ≤ C*p.control (seminorms i)^2*(1+‖t‖)^(2*orders i) := by gcongr
    _ ≤ C*p.control S^2*(1+‖t‖)^(2*J) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpsq hC.le) ht
        (by positivity) (mul_nonneg hC.le (sq_nonneg _))

theorem actual_local_main_exceptional_child_uniform
    {Slot : Type*} [Fintype Slot]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi)
    (lo hi : Slot → ℝ) (b : ℝ) (hb : 1 ≤ b) (ε δ θ Bcap : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hBcap : 0 ≤ Bcap) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
      ∃ Cfixed : ℝ, 0 < Cfixed ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : Input Slot) (p : Profiles wlo whi),
      (∀ i, s.lo i = lo i) → (∀ i, s.hi i = hi i) →
      s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
      ∀ (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C = primeSupport D →
      ∀ U : Finset (CommonIndex C D),
      E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U} →
      ∀ (K omega M : ℝ), 0 < K →
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D} →
      ∀ (Rmask seed : Ideal O) (B : actualAllocations s.pools (commonPart C D)) (t : ℝ),
      s.upper ≤ b →
      frozenCoefficient B.val (commonPart C D) Rmask s.ν s.W s.P ≠ 0 →
      1 ≤ M → M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s) ≤ (883/1000)*M →
      Z^(M/4) ≤ s.X₁ → Z^(M/4) ≤ s.X₂ → Z^(M/4) ≤ s.Y₁ → Z^(M/4) ≤ s.Y₂ →
      Rmask ≠ 0 → Squarefree seed → seed ≠ 0 →
      let d := child s (commonPart C D) Rmask B τ t
      let V := CenteredMomentAmplificationChildInput.volume s
      let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
        (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
      (∀ i, 1 ≤ d.P i) → 0 ≤ sourceRadius d → sourceRadius d ≤ Z^Bcap →
      (τ.modulus.absNorm : ℝ) ≤ Z^Bcap → ((Rmask*commonPart C D).absNorm : ℝ) ≤ Z^Bcap →
      ∀ (ray : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
      ∀ Tsec ξ : ℝ, 0 < frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ ≤ Z^Bcap →
      ‖partEnergy true τ ray Q m t (finiteColumns (Fintype.piFinset d.pools))
        (coefficient d (Rmask*commonPart C D) seed) ballProfile Rmain
        Tsec Z ξ (sourceRadius d)‖ /
        (CenteredMomentAmplificationChildInput.volume d*Z^(3/500 : ℝ)*
          ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))*Z^(allowance C D Z))) ≤
      Cfixed*p.control S^2*(1+‖t‖)^(2*J)*mass s^4*mass d^2*
        Z^(2*ε+2*δ+2*(5*Bcap+1)*θ-93/1000+5*omega/6)/(seed.absNorm : ℝ) := by
  obtain ⟨orders,seminorms,hseminorms,Cs,hCs,hsource⟩ :=
    actual_local_main_exceptional_child wlo whi hwlo hwhi lo hi ε δ θ Bcap hε hδ hθ hBcap
  obtain ⟨J,S,hS,huniform⟩ := finite_exceptional_profile_control orders seminorms
  refine ⟨J,S,hS,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Ks,hKs,hsource⟩ := hsource Q hQ hQt hQ72
  let coeff := fun I : Finset Slot =>
    Cs I*exceptionalConstant (Fintype.card Slot) b (orders I) Q (Ks I)*
      (b^(Fintype.card Slot))^(1/3 : ℝ)*
      ((∏ i : I, lo i.val)*wlo*wlo)^(-2/3 : ℝ)
  obtain ⟨Cfixed,hCfixed,hcontrol⟩ := huniform coeff
  refine ⟨Cfixed,hCfixed,?_⟩
  filter_upwards [hsource] with Z hsource
  refine ⟨hsource.1,?_⟩
  intro s p hlo hhi hW₁ hW₂ η τ C D E hC hD hCD U hE K omega M hK hmod
    Rmask seed B t hupper hne hM hwidth hvolume hX₁ hX₂ hY₁ hY₂
    hRmask hseed hseed0 d V Rmain hP hH0 hH hτ hRnorm ray m hm hml hm2 Tsec ξ hfreq hfreqcap
  have hh := hsource.2 s p hlo hhi hW₁ hW₂ η τ C D E hC hD hCD U hE K omega M hK hmod
    Rmask seed B t (Fintype.card Slot) b hb le_rfl hupper hne hM hwidth hvolume
    hX₁ hX₂ hY₁ hY₂ hRmask hseed hseed0 hP hH0 hH hτ hRnorm ray m hm hml hm2 Tsec ξ
    hfreq hfreqcap
  apply hh.trans
  have hc := hcontrol p t (liveIndices B.val)
  have hp : 0 ≤ mass s^4*mass d^2*
      Z^(2*ε+2*δ+2*(5*Bcap+1)*θ-93/1000+5*omega/6)/(seed.absNorm : ℝ) := by
    have hZ := (zero_lt_one.trans hsource.1).le
    positivity
  have hf := mul_le_mul_of_nonneg_right hc hp
  change coeff _ * _ * _ * _ ≤ _ at hf
  convert hf using 1 <;> ring

#print axioms actual_local_main_exceptional_child_uniform
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalUniformChild -/
