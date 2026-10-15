/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B006
import Submissions.local44_20261013.Bundles.B020
import Submissions.local44_20261013.Bundles.B021
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalErrorHomogeneous
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.SourceSZBound ; sha256 7122a666247c4f5f042a9abffbb7b1ab519df9a3e976e6cb3c02566980aa5853 -/
section


/-! Uniform integration of the two remaining Mellin variables after inversion. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open ProbePhysical ProbeMellinBoundary EisensteinSchwartzPoisson

def szProfile (W0 : SchwartzMap ℝ ℂ) (σ r : ℝ) (q : ℝ×ℝ) : ℂ :=
  Complex.exp ((((σ:ℂ)+q.1*I)+((r:ℂ)+q.2*I)-1)^2)*
    mellin (paperRadialFourier W0) ((r:ℂ)+q.2*I)

def szEnvelope (J : ℕ) (q : ℝ×ℝ) : ℝ :=
  gaussianMoment J (q.1+q.2)*cauchy q.2

lemma szEnvelope_nonneg (J : ℕ) (q : ℝ×ℝ) : 0 ≤ szEnvelope J q :=
  mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _)

lemma szEnvelope_integrable (J : ℕ) : Integrable (szEnvelope J) (volume.prod volume) := by
  have hp : MeasurePreserving (fun q : ℝ×ℝ=>(q.1+q.2,q.2))
      (volume.prod volume) (volume.prod volume) := by
    have hp0 := measurePreserving_prod_add_swap (volume : Measure ℝ) (volume : Measure ℝ)
    have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
    simpa only [Function.comp_def,Prod.swap,add_comm] using! hp1
  exact hp.integrable_comp_of_integrable ((gaussianMoment_integrable J).mul_prod cauchy_integrable)

lemma szProfile_norm (W0 : SchwartzMap ℝ ℂ) (σ r : ℝ) (q : ℝ×ℝ) :
    ‖szProfile W0 σ r q‖=Real.exp ((σ+r-1)^2)*Real.exp (-((q.1+q.2)^2))*
      ‖mellin (paperRadialFourier W0) ((r:ℂ)+q.2*I)‖ := by
  unfold szProfile
  rw [norm_mul,Complex.norm_exp]
  have hr : ((((σ:ℂ)+q.1*I)+((r:ℂ)+q.2*I)-1)^2).re=
      (σ+r-1)^2+(-((q.1+q.2)^2)) := by simp [pow_two];ring
  rw [hr,Real.exp_add]

lemma szProfile_continuous (W0 : SchwartzMap ℝ ℂ) (σ r : ℝ) (hr : 0< r) :
    Continuous (szProfile W0 σ r) := by
  have hR : Continuous (fun t : ℝ=> mellin (paperRadialFourier W0) ((r:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t;simpa using hr)
  exact (by fun_prop : Continuous (fun q : ℝ×ℝ=>
    Complex.exp ((((σ:ℂ)+q.1*I)+((r:ℂ)+q.2*I)-1)^2))).mul (hR.comp continuous_snd)

lemma szProfile_moment_majorant (W0 : SchwartzMap ℝ ℂ) (J : ℕ)
    {slo shi rlo rhi σ r C : ℝ} (hσ : σ∈Icc slo shi) (hr : r∈Icc rlo rhi)
    (hC : 0≤ C)
    (hR : ∀v : ℝ,height v^(J+2)*‖mellin (paperRadialFourier W0) ((r:ℂ)+v*I)‖≤ C)
    (q : ℝ×ℝ) :
    jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖≤
      (realGaussianBound slo shi rlo rhi*2^J*C)*szEnvelope J q := by
  have hb := weighted_coupled_cauchy J q.1 q.2 0
    ‖mellin (paperRadialFourier W0) ((r:ℂ)+q.2*I)‖ 1 C 1
    (norm_nonneg _) (by norm_num) hC (by norm_num) (hR _) (by simp [height])
  simp only [mul_one,cauchy,zero_pow (by decide : 2≠0),add_zero,inv_one] at hb
  rw [szProfile_norm]
  calc
    _ = Real.exp ((σ+r-1)^2)*(jointHeight q.1 q.2 0^J*
        Real.exp (-((q.1+q.2)^2))*‖mellin (paperRadialFourier W0) ((r:ℂ)+q.2*I)‖) := by ring
    _ ≤ realGaussianBound slo shi rlo rhi*((2:ℝ)^J*C*szEnvelope J q) :=
      mul_le_mul (realGaussian_le hσ hr) hb (by
        have hh := (jointHeight_pos q.1 q.2 0).le
        positivity)
        (realGaussianBound_pos _ _ _ _).le
    _ = _ := by ring

theorem szProfile_uniform_moments (W0 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0< a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (slo shi rlo rhi : ℝ) (hrlo : 0< rlo) (J : ℕ) :
    ∃C : ℝ,0< C ∧ ∀σ∈Icc slo shi,∀r∈Icc rlo rhi,
      Integrable (fun q : ℝ×ℝ=> jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖ ∂(volume.prod volume))≤ C := by
  obtain ⟨D,hD,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 rlo rhi hrlo (J+2)
  let A := realGaussianBound slo shi rlo rhi*2^J*D
  have hA : 0< A := by dsimp [A];exact mul_pos (mul_pos (realGaussianBound_pos _ _ _ _) (by positivity)) hD
  refine ⟨A*(1+|∫q,szEnvelope J q ∂(volume.prod volume)|),by positivity,?_⟩
  intro σ hσ r hr
  have hb := szProfile_moment_majorant W0 J hσ hr hD.le (hR r hr)
  have hc := szProfile_continuous W0 σ r (hrlo.trans_le hr.1)
  have hi : Integrable (fun q : ℝ×ℝ=> jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖) (volume.prod volume) := by
    apply ((szEnvelope_integrable J).const_mul A).mono'
    · exact ((by unfold jointHeight;fun_prop : Continuous (fun q : ℝ×ℝ=> jointHeight q.1 q.2 0^J)).mul
        hc.norm).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro q
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _))]
      exact hb q
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫q,A*szEnvelope J q ∂(volume.prod volume) :=
      integral_mono hi ((szEnvelope_integrable J).const_mul A) hb
    _ = A*(∫q,szEnvelope J q ∂(volume.prod volume)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [le_abs_self (∫q,szEnvelope J q ∂(volume.prod volume))]) hA.le

lemma sourceSZWeight_norm (W0 : SchwartzMap ℝ ℂ) (X Z σ r : ℝ)
    (hX : 0< X) (hZ : 0< Z) (q : ℝ×ℝ) :
    ‖sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)‖=
      X^(1/2-r)*Z^(σ+r-1)*‖szProfile W0 σ r q‖ := by
  simp only [sourceSZWeight,szProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,mul_zero,zero_mul,sub_zero,add_zero]
  norm_num
  ring

/-- Any proved numerator bound can be integrated with no loss in the contour height. -/
theorem sourceSZ_uniform_integral_bound (W0 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0< a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (slo shi rlo rhi : ℝ) (hrlo : 0< rlo) (J : ℕ) :
    ∃C : ℝ,0< C ∧ ∀σ∈Icc slo shi,∀r∈Icc rlo rhi,
      ∀X Z : ℝ,0< X→0< Z→∀H A : ℝ,0≤ A→∀G : (ℝ×ℝ)→ℂ,
      IntegrableOn (fun q=> sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*G q)
        (szRectangle H) (volume.prod volume)→
      (∀q∈szRectangle H,‖G q‖≤ A*jointHeight q.1 q.2 0^J)→
      ‖∫q in szRectangle H,sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*G q
        ∂(volume.prod volume)‖≤ C*X^(1/2-r)*Z^(σ+r-1)*A := by
  obtain ⟨C,hC,hprofile⟩ := szProfile_uniform_moments W0 a0 b0 ha0 hW0 slo shi rlo rhi hrlo J
  refine ⟨C,hC,?_⟩
  intro σ hσ r hr X Z hX hZ H A hA G hG hbound
  obtain ⟨hp,hpbound⟩ := hprofile σ hσ r hr
  let scale : ℝ := X^(1/2-r)*Z^(σ+r-1)
  have hs : 0 ≤ scale := by dsimp [scale];positivity
  have hi := hp.const_mul (scale*A)
  have hn : ∀q : ℝ×ℝ,0≤(scale*A)*(jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖) := by
    intro q
    exact mul_nonneg (mul_nonneg hs hA)
      (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _))
  calc
    _ ≤ ∫q in szRectangle H,‖sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*G q‖
        ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ ≤ ∫q in szRectangle H,(scale*A)*(jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖)
        ∂(volume.prod volume) := by
      apply integral_mono_ae hG.norm hi.integrableOn
      filter_upwards [ae_restrict_mem (szRectangle_measurable H)] with q hq
      rw [norm_mul,sourceSZWeight_norm W0 X Z σ r hX hZ]
      calc
        _ ≤ (scale*‖szProfile W0 σ r q‖)*(A*jointHeight q.1 q.2 0^J) :=
          mul_le_mul_of_nonneg_left (hbound q hq) (mul_nonneg hs (norm_nonneg _))
        _ = _ := by ring
    _ ≤ ∫q,(scale*A)*(jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖)
        ∂(volume.prod volume) := setIntegral_le_integral hi (Filter.Eventually.of_forall hn)
    _ = (scale*A)*(∫q,jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖ ∂(volume.prod volume)) :=
      integral_const_mul _ _
    _ ≤ (scale*A)*C := mul_le_mul_of_nonneg_left hpbound (mul_nonneg hs hA)
    _ = _ := by dsimp [scale];ring

end Cycle25.Weighted.FullWContour
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.SourceSZBound -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCollected ; sha256 4fa961e930f14f25d4567262636b362300052804c2be761a190770182b2978a6 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_nonfloor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤ dmax)
    (hmuMargin : 2*margin≤μ) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,∀C0 : ℝ,0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(13/16+ζ)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u≤ n ∧ grid u≤ m ∧ grid u≠0 ∧ 51/100+e*grid u≤1) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*idx u:ℕ)*Z^τ)) →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell (fun j y=>(W j y:ℂ)) Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) Δ
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y)
        (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu+dyadCost) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ :=
    actual_normalized_nonfloor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu counts
  have hellpos (j : Fin N) : 0< ell j := (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,
    sourceDyad_geometry_eventually dmin dmax margin (13/16+ζ) hdmin hdmin1 hmargin hconductor,
    eventually_gt_atTop (1:ℝ)] with Z hb hn hg hZ
  intro C0 hC0 rows hrows idx grid hlabels hnext hcurrent hmom
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := nonfloorPoolOutside M H S N c b Y
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu)
  have hD : 0≤ D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun R a H=>
    finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(13/16+ζ)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤ D := by
    let Rk := rows∩dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij⊆Rk := Finset.filter_subset _ _
    have hsub : Rij⊆rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hgeo := hg rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
        (hne'.mono hsubk)
      obtain ⟨u,hu⟩ := hne'
      have huj : grid u=j := ((mem_cubeBinRows Rk idx grid i j u).mp hu).2.2
      have hju : j≠0 := huj ▸ (hlabels u (hsub hu)).2.2.1
      have ha : 51/100<51/100+e*j := by
        have hjp : (0:ℝ)< j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith
      have ha' : 51/100+e*j≤1 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^τ)<51/100+e*j+2*e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+e*j≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hbounded := hb (sourceDyadConductor Z margin k) hgeo.2.2.1 hgeo.2.2.2.1
        (sourceDyadExponent Z k) (51/100+e*j) C0 hgeo.1 hgeo.2.1
        (by unfold sourceDyadConductor;linarith) ha ha' hC0 Rij
        (fun u hu=>⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
          (hrows u (hsub hu)).2.2.1,hgeo.2.2.2.2.2 u (hsubk hu)⟩)
        (fun u hu=> hgeo.2.2.2.2.1 u (hsubk hu)) i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        hnext' hcurrent' (fun t ht=> hmom k hk i hi j hj ⟨u,hu⟩ t ht)
      exact hbounded.2
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(13/16+ζ)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(13/16+ζ)),(n+1:ℕ)*(m+1:ℕ)*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (Z^τ) idx grid n m
        (fun u hu=>⟨(hlabels u (Finset.mem_inter.mp hu).1).1,(hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
      change ‖F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
      dsimp only [F]
      rw [hpart,Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=> hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(13/16+ζ))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
    _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
      mul_le_mul_of_nonneg_right (hdyad Z (13/16+ζ) hZ.le (by linarith)) (by positivity)
    _ = _ := by dsimp [D];rw [Real.rpow_add hZp (3/16+Δ-saving+nu) dyadCost];ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCollected -/

/- BEGIN ORIGINAL MODULE Analytic.ActualBufferedUniform ; sha256 c047092d9baac9d4da9fb2f22f0c9e4eae53a5713dcfb171705710824b0ba684 -/
section


/-!
Actual buffered-row counting, with witness construction and both moment
inputs discharged. The remaining hypotheses are literal arithmetic
coefficient identities, nonprincipality, conductor bounds and buffered
zero maxima for the finite row set being counted.
-/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRawFiber HeckeDetectorInverseFiberCount
open HeckeDetectorProfiles HeckeDetectorRowwisePolynomial
open ProbeHighRowFamily LocalMoment

local notation "O" => HeckeFamily.O

/-- A literal buffered-zero row set obeys the balanced density exponent.

Unlike a conditional moment interface, this theorem takes neither a
moment estimate nor a detector witness as input. Both are constructed
from the existing source theorems. The height is quantified after the
eventual row threshold.
-/
theorem actual_buffered_row_count_uniform_geometry {Label : Type*} [Fintype Label]
    (η : Label → Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : ∀ label, Q ≤ (η label).modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ J : ℕ, ∃ C K₀ : ℝ, 0 < C ∧ 0 ≤ K₀ ∧
      ∀ (τ ε e κaux ηaux : ℝ) (I : ℕ)
        (hτ : 0 < τ) (hτzero : τ < 1/2)
    (hτheight : 4*τ < ηaux) (hε : 0 < ε) (hεsmall : ε ≤ 1/1000)
    (he : 0 < e) (hesmall : e < 1/1000)
    (hκ : 0 < κaux) (hκone : κaux ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κaux+2*ηaux ≤ ε/2),
      ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (rows : Finset FreeRow) (family : rows → Label → Character)
        (reverse : Label → Bool) (hχ : ∀ u j, (family u j).residue ≠ 1),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      (∀ u : rows, ∀ j, ∀ R : Ideal O, idealCoeff (family u j) R =
        if reverse j then starRingEnd ℂ
          (idealCoeff ((momentData (η j)).character
            ⟨u.val.val, u.val.property.1⟩) R)
        else idealCoeff ((momentData (η j)).character
          ⟨u.val.val, u.val.property.1⟩) R) →
      ∀ (a height : ℝ) (i : ℕ), i ≤ I → 51/100 < a → a ≤ 7/8 →
      (∀ u, HeckeDetectorZeros.zeroMaximum (family u) (hχ u)
        (3*(i+1 : ℕ)*U^τ) < a+2*e) →
      (∀ u, a ≤ HeckeDetectorZeros.zeroMaximum (family u) (hχ u)
        ((3*i : ℕ)*U^τ)) →
      (∀ u j, (family u j).modulus.absNorm ≤ U) →
      0 ≤ height → 2*Real.pi*U^(τ/2)+(3*i : ℕ)*U^τ ≤ height →
      (rows.card : ℝ) ≤ (Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2 *
        fiberConstant (C*(1+height)^J) height K₀ *
          U^(unmarkedDensity (2*a-1)+156*ε+εm) := by
  obtain ⟨J, C, K₀, hC, hK, hcount⟩ := actual_unmarked_batch_count
    η Q hQtop hQ72 hQη hβ M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨J, C, K₀, hC, hK, ?_⟩
  intro τ ε e κaux ηaux I hτ hτzero hτheight hε hεsmall he hesmall hκ hκone hη hbudget
  obtain ⟨U₀, hwitness⟩ := actual_supported_witness_family
    1 1 τ ε e κaux ηaux I (by norm_num) le_rfl hτ hτzero
    (by simpa only [one_mul] using hτheight) hε he hesmall hκ hκone hη hbudget
  filter_upwards [hcount, eventually_ge_atTop U₀] with U hcount hU₀
  refine ⟨hcount.1, ?_⟩
  intro rows family reverse hχ hrow hcoeff a height i hi ha ha' hnext hcurrent hQ hh hf
  have hCheight : 0 ≤ C*(1+height)^J := by positivity
  have hconst := (fiberConstant_bounds (C*(1+height)^J) height K₀ hCheight hh hK).1
  by_cases hne : rows.Nonempty
  · have hcut := unmarkedCutoff_bounds (δ := 2*a-1) (by linarith) (by linarith)
    have hrow' : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U^(1 : ℝ) := by
      simpa only [Real.rpow_one] using hrow
    have hQ' : ∀ u j, (family u j).modulus.absNorm ≤ U^(1 : ℝ) := by
      simpa only [Real.rpow_one] using hQ
    have hw : Nonempty (∀ u : rows, SupportedWitness (family u) U a ε
        (unmarkedCutoff (2*a-1)) (U^τ) (U^(τ/2)) i) := by
      have hw0 := hwitness U hU₀ 1 le_rfl le_rfl family hχ a i hi
          (by linarith) (by linarith) hnext hcurrent hQ'
          (unmarkedCutoff (2*a-1)) hcut.1 hcut.2
      rw [Real.rpow_one, mul_one] at hw0
      exact hw0
    obtain ⟨w⟩ := hw
    obtain ⟨u₀, hu₀⟩ := hne
    let B := UnmarkedBatch.ofSupportedRows rows ⟨u₀, hu₀⟩ family w hrow
      (fun label => momentData (η label)) reverse hcoeff
    have hb := hcount.2 a ε (U^τ) (U^(τ/2)) height i (by linarith)
      (by linarith) hε.le hεsmall hh hf B rfl
    exact hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hconst)
      (Real.rpow_nonneg (zero_lt_one.trans hcount.1).le _)

#print axioms actual_buffered_row_count_uniform_geometry

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualBufferedUniform -/

/- BEGIN ORIGINAL MODULE Analytic.BufferedPartition ; sha256 22bca8922ebe71a0f2105f518bfe2733ab15b09467bf6c8a14d90872bb3a3e83 -/
section


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDetectorZeros HeckeInverseAmplification LocalMoment

/-- Every actual nonprincipal row has a buffer bin in one fixed finite index set. -/
theorem exists_bounded_buffered_bins {Row Label : Type*} [Fintype Label]
    (χ : Row → Label → Character) (hχ : ∀ u j, (χ u j).residue ≠ 1)
    (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (N : ℕ) (hN : 0 < N) (hwidth : (49/100 : ℝ) ≤ N*e) :
    ∃ bin : Row → Fin (N+1) × Fin (N+1), ∀ u,
      1 ≤ (bin u).1.val ∧
      let a : ℝ := 51/100+e*((bin u).2.val : ℝ)
      a ≤ 1 ∧ a ≤ zeroMaximum (χ u) (hχ u) ((3*(bin u).1.val : ℕ)*T) ∧
      zeroMaximum (χ u) (hχ u) ((3*(bin u).1.val : ℕ)*T) < a+e ∧
      zeroMaximum (χ u) (hχ u) ((3*((bin u).1.val+1) : ℕ)*T) < a+2*e := by
  choose i k hi hin hp using fun u =>
    exists_actual_buffered_bin (χ u) (hχ u) T e hT he N hN hwidth
  have hk (u : Row) : k u ≤ N := by
    have htop : 51/100+e*(k u : ℝ) ≤ 1 := (hp u).1
    have hreal : (k u : ℝ) ≤ N := by nlinarith
    exact_mod_cast hreal
  let bin : Row → Fin (N+1) × Fin (N+1) := fun u =>
    (⟨i u, Nat.lt_succ_of_le (hin u)⟩, ⟨k u, Nat.lt_succ_of_le (hk u)⟩)
  refine ⟨bin, ?_⟩
  intro u
  refine ⟨hi u, (hp u).1, ?_, ?_, ?_⟩
  · simpa only [bin, Nat.cast_mul, Nat.cast_ofNat] using (hp u).2.1
  · simpa only [bin, Nat.cast_mul, Nat.cast_ofNat] using (hp u).2.2.1
  · simpa only [bin, Nat.cast_mul, Nat.cast_ofNat] using (hp u).2.2.2.1

/-- Exact finite population decomposition; no separate label count is hidden. -/
theorem card_eq_sum_buffered_fibers {Row Index : Type*} [DecidableEq Row]
    [Fintype Index] [DecidableEq Index] (rows : Finset Row) (bin : Row → Index) :
    rows.card = ∑ b : Index, (rows.filter (fun u => bin u = b)).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s := rows) (t := Finset.univ)
    (f := bin) (by intro u hu; exact Finset.mem_univ _)
  simpa only using hh

/-- The mesh loss used in the written density assembly is uniform. -/
theorem unmarkedDensity_buffer_loss (d b e : ℝ)
    (hd : d ≤ 3/4) (hb : b ≤ 3/4) (he : 0 ≤ e) (hgap : d-b ≤ 2*e) :
    unmarkedDensity b ≤ unmarkedDensity d+3*e := by
  have hx : 7/2 ≤ 5-2*b := by linarith
  have hy : 7/2 ≤ 5-2*d := by linarith
  have hxpos : 0 < 5-2*b := by linarith
  have hypos : 0 < 5-2*d := by linarith
  have hden : 0 < 3*(5-2*b)*(5-2*d) := by positivity
  have hdenlow : 147/4 ≤ 3*(5-2*b)*(5-2*d) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hid : unmarkedDensity b-unmarkedDensity d =
      50*(d-b)/(3*(5-2*b)*(5-2*d)) := by
    unfold unmarkedDensity
    field_simp [hxpos.ne', hypos.ne', show 5-b*2 ≠ 0 by nlinarith,
      show 5-d*2 ≠ 0 by nlinarith]
    <;> ring
  have hpay : 50*(d-b) ≤ 3*e*(3*(5-2*b)*(5-2*d)) := by
    nlinarith [mul_le_mul_of_nonneg_left hdenlow he]
  have hquot : 50*(d-b)/(3*(5-2*b)*(5-2*d)) ≤ 3*e :=
    (div_le_iff₀ hden).mpr hpay
  linarith

theorem zeroMaximum_le_seven_eighths {Label : Type*} [Fintype Label]
    (χ : Label → Character) (hχ : ∀ j, (χ j).residue ≠ 1) (T : ℝ)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8) :
    zeroMaximum χ hχ T ≤ 7/8 := by
  by_cases hlarge : (51/100 : ℝ) < zeroMaximum χ hχ T
  · obtain ⟨j, s, hz, ht, hs⟩ := maximum_attained χ hχ T hlarge
    have hspos : 0 < s.re := by rw [hs]; linarith
    have hb := HeckeZeroSupremum.zero_re_le_beta (χ j) hspos (Or.inr (hχ j)) hz
    rw [← hs]
    exact hb.trans hβupper
  · linarith

theorem buffered_count_of_bin_counts
    {Label : Type*} [Fintype Label]
    (χ : FreeRow → Label → Character)
    (hχ : ∀ u j, (χ u j).residue ≠ 1)
    (rows : Finset FreeRow) (U T e K E a₀ : ℝ) (I : ℕ)
    (hU : 1 < U) (hT : 2 < T) (he : 0 < e) (hesmall : e < 1 / 1000)
    (hI : 0 < I) (hwidth : (49 / 100 : ℝ) ≤ (I : ℝ) * e)
    (hK : 0 ≤ K) (hβupper : HeckeZeroSupremum.beta ≤ 7 / 8)
    (ha₀ : 167 / 200 ≤ a₀) (ha₀upper : a₀ ≤ 7 / 8)
    (hinitial : ∀ u ∈ rows, a₀ ≤ zeroMaximum (χ u) (hχ u) T)
    (hcount : ∀ s : Finset FreeRow, s ⊆ rows → ∀ a : ℝ, ∀ i : ℕ,
      i ≤ I → 51 / 100 < a → a ≤ 7 / 8 →
      (∀ u ∈ s, zeroMaximum (χ u) (hχ u) (3 * ((i : ℝ) + 1) * T) < a + 2 * e) →
      (∀ u ∈ s, a ≤ zeroMaximum (χ u) (hχ u) (3 * (i : ℝ) * T)) →
      (s.card : ℝ) ≤ K * U ^ (unmarkedDensity (2 * a - 1) + E)) :
    (rows.card : ℝ) ≤ ((I : ℝ) + 1) ^ 2 *
      (K * U ^ (unmarkedDensity (2 * a₀ - 1) + E + 3 * e)) := by
  obtain ⟨bin, hbin⟩ := exists_bounded_buffered_bins χ hχ T e hT he I hI hwidth
  let Index := Fin (I + 1) × Fin (I + 1)
  let fiber (b : Index) : Finset FreeRow := rows.filter (fun u => bin u = b)
  let final := K * U ^ (unmarkedDensity (2 * a₀ - 1) + E + 3 * e)
  have hfinal : 0 ≤ final := mul_nonneg hK (le_of_lt (Real.rpow_pos_of_pos (by linarith) _))
  have hfiber : ∀ b : Index, ((fiber b).card : ℝ) ≤ final := by
    intro b
    by_cases hne : (fiber b).Nonempty
    · let a : ℝ := 51 / 100 + e * (b.2.val : ℝ)
      have hp : ∀ u ∈ fiber b,
          1 ≤ b.1.val ∧ a ≤ 1 ∧
          a ≤ zeroMaximum (χ u) (hχ u) (3 * (b.1.val : ℝ) * T) ∧
          zeroMaximum (χ u) (hχ u) (3 * (b.1.val : ℝ) * T) < a + e ∧
          zeroMaximum (χ u) (hχ u) (3 * ((b.1.val : ℝ) + 1) * T) < a + 2 * e := by
        intro u hu
        have hub : bin u = b := (Finset.mem_filter.mp hu).2
        simpa [a, hub, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hbin u
      obtain ⟨u₀, hu₀⟩ := hne
      have hi : 1 ≤ b.1.val := (hp u₀ hu₀).1
      have hiI : b.1.val ≤ I := Nat.le_of_lt_succ b.1.isLt
      have hiR : (1 : ℝ) ≤ b.1.val := by exact_mod_cast hi
      have hmono := zeroMaximum_mono (χ u₀) (hχ u₀)
        (show T ≤ 3 * (b.1.val : ℝ) * T by nlinarith)
      have hstart := hinitial u₀ (Finset.mem_filter.mp hu₀).1
      have hgap : a₀ < a + e := lt_of_le_of_lt (hstart.trans hmono) (hp u₀ hu₀).2.2.2.1
      have ha : 51 / 100 < a := by linarith
      have hamax : a ≤ 7 / 8 := (hp u₀ hu₀).2.2.1.trans
        (zeroMaximum_le_seven_eighths (χ u₀) (hχ u₀) _ hβupper)
      have hb := hcount (fiber b) (by intro u hu; exact (Finset.mem_filter.mp hu).1)
        a b.1.val hiI ha hamax
        (by intro u hu; exact (hp u hu).2.2.2.2)
        (by intro u hu; exact (hp u hu).2.2.1)
      have hrho : unmarkedDensity (2 * a - 1) ≤
          unmarkedDensity (2 * a₀ - 1) + 3 * e := by
        apply unmarkedDensity_buffer_loss <;> linarith
      have hpow : U ^ (unmarkedDensity (2 * a - 1) + E) ≤
          U ^ (unmarkedDensity (2 * a₀ - 1) + E + 3 * e) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hU) (by linarith)
      exact hb.trans (mul_le_mul_of_nonneg_left hpow hK)
    · have hempty : fiber b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simpa [hempty] using hfinal
  have hcard : (rows.card : ℝ) = ∑ b : Index, ((fiber b).card : ℝ) := by
    exact_mod_cast card_eq_sum_buffered_fibers rows bin
  calc
    (rows.card : ℝ) = ∑ b : Index, ((fiber b).card : ℝ) := hcard
    _ ≤ ∑ _b : Index, final := Finset.sum_le_sum (fun b _ => hfiber b)
    _ = ((I : ℝ) + 1) ^ 2 * final := by
      simp [Index, Fintype.card_prod, Fintype.card_fin, Nat.cast_add, Nat.cast_mul, pow_two]

theorem extend_nonprincipal_supported_family
    {Label : Type*} (rows : Finset FreeRow) (hne : rows.Nonempty)
    (family : rows → Label → Character)
    (hfamily : ∀ u j, (family u j).residue ≠ 1) :
    ∃ χ : FreeRow → Label → Character,
      (∀ u j, (χ u j).residue ≠ 1) ∧
      ∀ u : rows, ∀ j, χ u.val j = family u j := by
  obtain ⟨u₀, hu₀⟩ := hne
  let retract (u : FreeRow) : rows :=
    if hu : u ∈ rows then ⟨u, hu⟩ else ⟨u₀, hu₀⟩
  refine ⟨(fun u => family (retract u)), ?_, ?_⟩
  · intro u j
    exact hfamily (retract u) j
  · intro u j
    simp [retract, u.property]

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.BufferedPartition -/

/- BEGIN ORIGINAL MODULE Analytic.CancellationMasks ; sha256 9a5c5569808b6a3029d6b4f2a6ae6493d441a18214300a237ef0ab20e75be4d2 -/
section



/-! The zero residues in the signed reconstruction are precisely finite
Euler deletions. These identities do not replace a natural character by
its primitive associate, and hold at every ideal and every height. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open HeckeFamily CenteredMomentSecondHeightFamily CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentNaturalRowSource CompletedGauss
open CenteredMomentSupportedCorrelation

local notation "O" => ActualEisensteinCubic.O

def canceledFactor (C D : Ideal O) (k : ℕ) : O :=
  ∏ i : ActiveIndex C D, if activeExponent C D i = k then activePrimary C D i else 1

def canceledIdeal (C D : Ideal O) (k : ℕ) : Ideal O :=
  Ideal.span {canceledFactor C D k}

theorem canceledFactor_ne_zero (C D : Ideal O) (hC : Supported C) (k : ℕ) :
    canceledFactor C D k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs
  · exact supported_element_ne_zero _ (activePrimary_supported C D hC i)
  · exact one_ne_zero

theorem canceledIdeal_ne_zero (C D : Ideal O) (hC : Supported C) (k : ℕ) :
    canceledIdeal C D k ≠ 0 :=
  Ideal.span_singleton_eq_bot.not.mpr (canceledFactor_ne_zero C D hC k)

theorem canceledFactor_sixth (C D : Ideal O) (k : ℕ) (n : O)
    (hn : Supported (Ideal.span {n})) :
    idealRowHom (canceledFactor C D k ^ 6) (Ideal.span {n}) =
      ∏ i : ActiveIndex C D, if activeExponent C D i = k then
        if IsCoprime n (activePrimary C D i) then (1 : ℂ) else 0 else 1 := by
  unfold canceledFactor
  rw [← Finset.prod_pow, row_argument_product _ _ _ hn]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hk : activeExponent C D i = k
  · simp only [hk, ite_true, idealRowHom_sixth_mask _ _ hn,
      Ideal.isCoprime_span_singleton_iff]
  · simp only [hk, ite_false, one_pow, idealRowHom_one_supported _ hn]

theorem canceled_mask_ideal (C D : Ideal O) (k : ℕ) (I : Ideal O)
    (hI : Supported I) :
    (∏ i : ActiveIndex C D, if activeExponent C D i = k then
      if IsCoprime (primaryGenerator I) (activePrimary C D i) then (1 : ℂ) else 0 else 1) =
      if IsCoprime I (canceledIdeal C D k) then (1 : ℂ) else 0 := by
  have hs := primary_span_supported I hI
  rw [← canceledFactor_sixth C D k _ (hs.symm ▸ hI), hs,
    idealRowHom_sixth_mask _ I hI]
  rfl

theorem naturalRow_height {η : Character} {w : O} (N : NaturalRow η w)
    (t : ℝ) (I : Ideal O) :
    heightCoeff N.character t I = rowWeight η fixedBadMask 1 w t I := by
  simp only [heightCoeff, N.ideal, rowWeight, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, one_mul]

theorem naturalRow_excluded_height {η : Character} {w : O} (N : NaturalRow η w)
    (R : Ideal O) (hR : R ≠ 0) (t : ℝ) (I : Ideal O) :
    heightCoeff (excluded N.character R) t I =
      rowWeight η fixedBadMask 1 w t I *
        (if IsCoprime I R then (1 : ℂ) else 0) := by
  rw [← naturalRow_height N t I]
  simp only [heightCoeff, excluded_ideal N.character R hR I]
  split_ifs <;> ring

theorem naturalRow_canceled_height {η : Character} {w : O} (N : NaturalRow η w)
    (C D : Ideal O) (hC : Supported C) (k : ℕ) (t : ℝ) (I : Ideal O) :
    heightCoeff (excluded N.character (canceledIdeal C D k)) t I =
      rowWeight η fixedBadMask 1 w t I *
        (∏ i : ActiveIndex C D, if activeExponent C D i = k then
          if IsCoprime (primaryGenerator I) (activePrimary C D i) then (1 : ℂ) else 0 else 1) := by
  rw [naturalRow_excluded_height N _ (canceledIdeal_ne_zero C D hC k)]
  by_cases hI : Supported I
  · rw [canceled_mask_ideal C D k I hI]
  · rw [rowWeight_zero_of_not_supported η fixedBadMask 1 w t
      (dvd_mul_right goodLambda 2) (dvd_mul_left 2 goodLambda) I hI]
    simp only [zero_mul]

#print axioms canceled_mask_ideal
#print axioms naturalRow_canceled_height

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.CancellationMasks -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorHomogeneous ; sha256 ab676a79a77a34c6ea421ecb6e034c5e2a64de236878be1c3144bd1f356c8a09 -/
section



/-! Refined powers for the actual extracted Gaussian source. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem refined_error_homogeneous
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(hbPlain:0≤ b)
    (L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∃Z₀:ℝ,1< Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (refinedErrorDeficit prime Z (k+1) sigma (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    refined_error_power_from_bands (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  have hlo:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain
  obtain ⟨Uprofile,Jheight,hweights⟩:=
    CenteredMomentEnergyFirstGaussianProfileWeights.actual_weights (a:=a) (b:=b)
      N upper (max 1 b) (max 1 b) ((max 1 Mslot)^N)
      (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a)
      Cm Ce Cd Ct Cc cost εsrc δsrc θsrc Bcap J (dc+degree+4*n) (dc+degree+4*n)
      Sp T Sf CenteredMomentFirstAmplificationChoice.ballProfile
      (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)) (by positivity) hlo
      hCm.le hCe hCd.le hCt.le hCc.le (zero_le_one.trans hcost)
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hwbound⟩:=hweights (internalQ Q η₀) Kc hKc.le
  refine ⟨Cbound,hCbound,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  let Scols:=finiteColumns (Fintype.piFinset input.pools)
  let β:=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β rfl rfl
  have hg:=hbound 1 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hz:0< Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hmass:mass src≤(max 1 Mslot)^N:=
    CenteredMomentEnergyOriginalProfileControl.slot_product_le src N (max 1 Mslot)
      (le_max_left _ _) hcard (fun i=>(hMs i).trans (le_max_right _ _))
  have hnseed:1≤(seed.absNorm:ℝ):=norm_ge_one seed hseed0
  have hh:=hwbound p Z v0 height (mass src) (seed.absNorm:ℝ) C₀ C₁
    hz hheight (mass_nonneg src) hmass hnseed hC₀ hC₁
  dsimp only at hh
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos input).le _)
  apply mul_le_mul_of_nonneg_right (hh j)
  fin_cases j <;> simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold errorCommonRadius
  all_goals positivity

#print axioms refined_error_homogeneous
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorHomogeneous -/
