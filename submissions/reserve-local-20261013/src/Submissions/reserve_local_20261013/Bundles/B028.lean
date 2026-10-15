/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.reserve_local_20261013.Bundles.B023
import Submissions.reserve_local_20261013.Bundles.B025
import Submissions.reserve_local_20261013.Bundles.B026
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinSubset
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SectorLocalization

/- BEGIN ORIGINAL MODULE Endpoint.GlobalRange ; sha256 014f523e4d3aefb526829426c003913870397309714cfff860fdaf8fce473810 -/
section


/-! Exact scalar bounds over the full retained row range. -/
noncomputable section
namespace Submission20261012.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 4000

def dmin : ℝ := 1 / 200
def zeta : ℝ := 1 / 10000000000

/-- The literal numerator ledger, including the breakpoint at `d = y`. -/
def sourceGlobalRowExponent (κ d c δ p : ℝ) : ℝ :=
  (1 + δ) / 2 + h * (13 / 75) - y / 2 - ell / 2 + ell * (δ * p)
    + d * (1 / 4 + 3 * Cycle25.Arithmetic.rowExponent κ δ p / 4 - 17 / 50)
    - δ * p * min d (2 * y - d) / (2 * c)

/-- Only the short top interval uses the new local numerator cost. -/
def sourcePiecewiseRowExponent (κ d δ p : ℝ) : ℝ :=
  if junction ≤ d then sourceLocalRowExponent κ d δ p
    else sourceGlobalRowExponent κ d (6 * κ) δ p


lemma sourceGlobalRowExponent_eq_high (κ d c δ p : ℝ) (hd : y ≤ d) :
    sourceGlobalRowExponent κ d c δ p = sourceHighRowExponent κ d c δ p := by
  unfold sourceGlobalRowExponent sourceHighRowExponent
  rw [min_eq_right (by linarith)]

lemma source_row_le_one (δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    Cycle25.Arithmetic.rowExponent kappa δ p ≤ 1 := by
  have hk : (7:ℝ)/10 ≤ kappa := by norm_num [kappa]
  have hC0 := (Cycle25.Arithmetic.countingCoefficient_pos hk ⟨hp0,hp1⟩).le
  have hD : 0 < Cycle25.Arithmetic.countingDen kappa p := by
    linarith [Cycle25.Arithmetic.countingDen_lower hk ⟨hp0,hp1⟩]
  have hC1 : Cycle25.Arithmetic.countingCoefficient kappa p ≤ 1 := by
    apply (div_le_iff₀ hD).mpr
    unfold Cycle25.Arithmetic.countingDen
    norm_num [kappa]
    nlinarith [sq_nonneg p]
  have hS := Cycle25.Arithmetic.rowDen_pos hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith) ⟨hp0,hp1⟩
  have hV : 0 ≤ (5:ℝ)/6-δ := by linarith
  have hSV : (5:ℝ)/6-δ ≤ Cycle25.Arithmetic.rowDen kappa δ p := by
    unfold Cycle25.Arithmetic.rowDen
    nlinarith [mul_nonneg hδ0 hC0]
  have hCV : Cycle25.Arithmetic.countingCoefficient kappa p*((5:ℝ)/6-δ) ≤ (5:ℝ)/6-δ :=
    mul_le_of_le_one_left hV hC1
  have hnum : δ*Cycle25.Arithmetic.countingCoefficient kappa p*((5:ℝ)/6-δ) ≤
      δ*(2*Cycle25.Arithmetic.rowDen kappa δ p) := by
    have hm := mul_le_mul_of_nonneg_left hCV hδ0
    have hs := mul_le_mul_of_nonneg_left hSV hδ0
    nlinarith [mul_nonneg hδ0 hS.le]
  have hfrac := (div_le_iff₀ (show 0 < 2*Cycle25.Arithmetic.rowDen kappa δ p by positivity)).mpr hnum
  unfold Cycle25.Arithmetic.rowExponent
  linarith

private lemma affine_interval_le (A B a b d T : ℝ) (ha : a ≤ d) (hb : d ≤ b)
    (hleft : A+B*a ≤ T) (hright : A+B*b ≤ T) : A+B*d ≤ T := by
  by_cases hB : 0 ≤ B
  · linarith [mul_le_mul_of_nonneg_left hb hB]
  · have hB' : B ≤ 0 := le_of_not_ge hB
    linarith [mul_le_mul_of_nonpos_left ha hB']

/-- A negative nonnegative multiple of `min d (D-d)` is convex in `d`. -/
private lemma min_affine_interval_le (A B C D a b d T : ℝ)
    (hC : 0 ≤ C) (ha : a ≤ d) (hb : d ≤ b)
    (hleft : A+B*a-C*min a (D-a) ≤ T)
    (hright : A+B*b-C*min b (D-b) ≤ T) :
    A+B*d-C*min d (D-d) ≤ T := by
  have hl₁ : A+(B-C)*a ≤ T := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left a (D-a)) hC]
  have hr₁ : A+(B-C)*b ≤ T := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left b (D-b)) hC]
  have hl₂ : (A-C*D)+(B+C)*a ≤ T := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right a (D-a)) hC]
  have hr₂ : (A-C*D)+(B+C)*b ≤ T := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right b (D-b)) hC]
  rcases le_total d (D-d) with h | h
  · rw [min_eq_left h]
    nlinarith [affine_interval_le A (B-C) a b d T ha hb hl₁ hr₁]
  · rw [min_eq_right h]
    nlinarith [affine_interval_le (A-C*D) (B+C) a b d T ha hb hl₂ hr₂]

lemma source_global_interpolate (κ c δ p a b d T : ℝ)
    (hc : 0 < c) (hδ0 : 0 ≤ δ) (hp0 : 0 ≤ p) (ha : a ≤ d) (hb : d ≤ b)
    (hleft : sourceGlobalRowExponent κ a c δ p ≤ T)
    (hright : sourceGlobalRowExponent κ b c δ p ≤ T) :
    sourceGlobalRowExponent κ d c δ p ≤ T := by
  unfold sourceGlobalRowExponent at *
  have hs := min_affine_interval_le
    ((1+δ)/2+h*(13/75)-y/2-ell/2+ell*(δ*p))
    (1/4+3*Cycle25.Arithmetic.rowExponent κ δ p/4-17/50) (δ*p/(2*c)) (2*y)
    a b d T (by positivity) ha hb
    (by convert hleft using 1 <;> ring)
    (by convert hright using 1 <;> ring)
  convert hs using 1 <;> ring

lemma source_minimum_endpoint (δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    sourceGlobalRowExponent kappa dmin (6*kappa) δ p ≤ theta-1/10 := by
  have hq0 : 0 ≤ δ*p := mul_nonneg hδ0 hp0
  have hq1 : δ*p ≤ (3:ℝ)/8 := by
    nlinarith [mul_le_mul hδ1 hp1 hp0 (by norm_num : (0:ℝ) ≤ 3/4)]
  have hR := source_row_le_one δ p hδ0 hδ1 hp0 hp1
  have hgain : 0 ≤ δ*p*min dmin (2*y-dmin)/(2*(6*kappa)) := by
    have hm : 0 ≤ min dmin (2*y-dmin) := by norm_num [dmin,y,h,ell]
    have hk : 0 < kappa := by norm_num [kappa]
    positivity
  have hqell := mul_le_mul_of_nonneg_left hq1 (show 0 ≤ ell by norm_num [ell])
  unfold sourceGlobalRowExponent
  norm_num [dmin,theta,h,y,ell] at hgain hqell ⊢
  nlinarith

lemma source_old_range (d δ p : ℝ) (hdlo : dmin ≤ d) (hdhi : d ≤ junction)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    sourceGlobalRowExponent kappa d (6*kappa) δ p ≤ theta-1/10000 := by
  have hc : 0 < 6*kappa := by norm_num [kappa]
  have hhalf : sourceGlobalRowExponent kappa (1/2) (6*kappa) δ p ≤ theta-1/100 := by
    rw [sourceGlobalRowExponent_eq_high _ _ _ _ _ (by norm_num [y,h,ell])]
    exact source_half_endpoint δ p hδ0 hδ1 hp0 hp1
  by_cases hd : d ≤ 1/2
  · apply source_global_interpolate kappa (6*kappa) δ p dmin (1/2) d _ hc hδ0 hp0 hdlo hd
    · linarith [source_minimum_endpoint δ p hδ0 hδ1 hp0 hp1]
    · linarith
  · apply source_global_interpolate kappa (6*kappa) δ p (1/2) junction d _ hc hδ0 hp0
      (le_of_not_ge hd) hdhi
    · linarith
    · rw [sourceGlobalRowExponent_eq_high _ _ _ _ _ (by norm_num [y,h,ell,junction])]
      exact source_junction_endpoint δ p hδ0 hδ1 hp0 hp1

lemma source_local_junction (δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    sourceLocalRowExponent kappa junction δ p ≤ theta-1/10000 := by
  have hq : 0 ≤ δ*p := mul_nonneg hδ0 hp0
  have hold := source_junction_endpoint δ p hδ0 hδ1 hp0 hp1
  apply le_trans _ hold
  unfold sourceHighRowExponent sourceLocalRowExponent
  norm_num [kappa,junction,y,h,ell]
  nlinarith

lemma source_local_slope (δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    1/4+3*Cycle25.Arithmetic.rowExponent kappa δ p/4-17/50+
      δ*p*(1-1/250)/9 ≤ 1 := by
  have hR := source_row_le_one δ p hδ0 hδ1 hp0 hp1
  have hq : δ*p ≤ (3:ℝ)/8 := by
    nlinarith [mul_le_mul hδ1 hp1 hp0 (by norm_num : (0:ℝ) ≤ 3/4)]
  norm_num
  nlinarith

lemma source_local_interpolate (κ δ p a b d T : ℝ)
    (ha : a ≤ d) (hb : d ≤ b)
    (hleft : sourceLocalRowExponent κ a δ p ≤ T)
    (hright : sourceLocalRowExponent κ b δ p ≤ T) :
    sourceLocalRowExponent κ d δ p ≤ T := by
  unfold sourceLocalRowExponent at *
  have hs := affine_interval_le
    ((1+δ)/2+h*(13/75)-y/2-ell/2+ell*(δ*p)-δ*p*(2*y)/9)
    (1/4+3*Cycle25.Arithmetic.rowExponent κ δ p/4-17/50+δ*p*(1-1/250)/9)
    a b d T ha hb
    (by convert hleft using 1 <;> ring)
    (by convert hright using 1 <;> ring)
  convert hs using 1 <;> ring

lemma source_local_range (d δ p : ℝ) (hdlo : junction ≤ d) (hdhi : d ≤ h+zeta)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    sourceLocalRowExponent kappa d δ p ≤ theta-1/3000000 := by
  have htop := source_top_endpoint δ p hδ0 hδ1 hp0 hp1
  by_cases hd : d ≤ h
  · apply source_local_interpolate kappa δ p junction h d _ hdlo hd
    · linarith [source_local_junction δ p hδ0 hδ1 hp0 hp1]
    · linarith
  · have hd' : h ≤ d := le_of_not_ge hd
    have hdiff : sourceLocalRowExponent kappa d δ p -
        sourceLocalRowExponent kappa h δ p =
        (d-h)*(1/4+3*Cycle25.Arithmetic.rowExponent kappa δ p/4-17/50+
          δ*p*(1-1/250)/9) := by
      unfold sourceLocalRowExponent
      ring
    have hs := mul_le_mul_of_nonneg_left (source_local_slope δ p hδ0 hδ1 hp0 hp1)
      (sub_nonneg.mpr hd')
    norm_num [zeta] at hdhi
    nlinarith [hdiff]

/-- The complete scalar row certificate. This theorem makes no analytic assertion. -/
theorem source_global_range (d δ p : ℝ) (hdlo : dmin ≤ d) (hdhi : d ≤ h+zeta)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    sourcePiecewiseRowExponent kappa d δ p ≤ theta-1/3000000 := by
  unfold sourcePiecewiseRowExponent
  split_ifs with hd
  · exact source_local_range d δ p hd hdhi hδ0 hδ1 hp0 hp1
  · linarith [source_old_range d δ p hdlo (le_of_not_ge hd) hδ0 hδ1 hp0 hp1]

end Submission20261012.Endpoint
#print axioms Submission20261012.Endpoint.source_global_range
end
/- END ORIGINAL MODULE Endpoint.GlobalRange -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyFixedHigh ; sha256 1bc465b2b62cc50a3ad6a8c701ba1944691b2d2e41652f13e36e608b64d629bf -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound (hβ : (7/8:ℝ)< HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-7/8)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ)
    (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2) (hτcost : 4*τ<(1/200:ℝ)*D.cost)
    (hτt : τ< D.t) (hτ2 : 2*τ≤ D.t) (hτeps : τ*(2+4*D.eps)< D.t) :
    ∃C : ℝ,0< C ∧ ∀η : Character,∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,
      ∀C0 : ℝ,0≤ C0 → SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(HeckeZeroSupremum.beta-11/16-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : (13/16:ℝ)+D.t+2*D.t≤7/8 := by linarith
  obtain ⟨n,hn,C,hC,hbound⟩ := actual_high_probe_from_raw_moments F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=> F.w) (fun _=> F.support) (fun _=> F.smooth) (fun _=> F.bounded)
    (fun _=> F.compact) (fun _=> F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by nlinarith [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t D.t (2*τ) D.t ht ht ht (by linarith)
    D.t (2*D.t) D.t ht (by linarith) (by positivity) D.count_budget (by nlinarith [D.central_budget])
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by positivity) (D.t/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le
    D.sigma D.sigma_pos D.geometric_budget D.principal_budget D.window_budget D.floor_budget D.high_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.t (13/16+D.t)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+D.t))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^(13/16+D.t) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  obtain ⟨u,hu⟩ := hne
  have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
  have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
  have ha : (51/100:ℝ)<51/100+D.e*j := by
    have hjp : (0:ℝ)< j := by exact_mod_cast Nat.pos_of_ne_zero hjne
    nlinarith [D.e_pos]
  have ha' : (51/100:ℝ)+D.e*j≤1 := by simpa only [huj] using (hbins u).2.1
  have hrow' : ∀v∈rows',v.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm v ∧
      (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
      rowNorm v≤ Z^(sourceDyadConductor Z D.t k-D.t) := by
    intro v hv
    exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,hg.2.2.2.2.2 v (hsub hv)⟩
  have hi' : (i:ℝ)≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight : (3*i+1:ℕ)*Z^τ≤ Z^(2*τ) := by
    have hZp : 0< Z := zero_lt_one.trans hZ
    calc
      _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
      _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
  apply hmom rows' (sourceDyadConductor Z D.t k) (51/100+D.e*j) hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
    ((17/50:ℂ)+t.1.2*Complex.I)
  · simp
  · simpa using htheight.2.trans hheight

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyFixedHigh -/

/- BEGIN ORIGINAL MODULE Analytic.DensityArithmetic ; sha256 1d1b05357744aabd47e5233a31e2495b91fa1d31675f3d84fd4db3df294a84d7 -/
section


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeDetectorRawFiber

lemma density_geometry_parameters (ω : ℝ) (hω : 0 < ω) (J : ℕ) :
    ∃ (τ ε e κaux ηaux : ℝ) (I : ℕ),
      0 < τ ∧ τ < 1/2 ∧ 4*τ < ηaux ∧
      0 < ε ∧ ε ≤ 1/1000 ∧ 0 < e ∧ e < 1/1000 ∧
      0 < κaux ∧ κaux ≤ 1 ∧ 0 ≤ ηaux ∧
      12*e*((22 : ℝ)+2)+8*κaux+2*ηaux ≤ ε/2 ∧
      0 < I ∧ (49/100 : ℝ) ≤ (I : ℝ)*e ∧
      156*ε+ω/8+3*e+ω/8+τ*((J : ℝ)+1) ≤ ω := by
  let ε : ℝ := min (1/2000) (ω/1248)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεsmall : ε ≤ 1/2000 := min_le_left _ _
  have hεloss : ε ≤ ω/1248 := min_le_right _ _
  let e : ℝ := min (ε/2304) (min (ω/24) (1/2000))
  have he : 0 < e := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hebudget : e ≤ ε/2304 := min_le_left _ _
  have heloss : e ≤ ω/24 := (min_le_right _ _).trans (min_le_left _ _)
  have hesmall : e ≤ 1/2000 := (min_le_right _ _).trans (min_le_right _ _)
  let κaux : ℝ := min (ε/64) (1/2)
  have hκ : 0 < κaux := lt_min (by positivity) (by norm_num)
  have hκbudget : κaux ≤ ε/64 := min_le_left _ _
  have hκone : κaux ≤ 1/2 := min_le_right _ _
  let ηaux : ℝ := ε/16
  have hη : 0 < ηaux := by dsimp [ηaux]; positivity
  let τ : ℝ := min (1/4) (min (ηaux/8) (ω/(16*((J : ℝ)+1))))
  have hτ : 0 < τ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hτzero : τ ≤ 1/4 := min_le_left _ _
  have hτheight : τ ≤ ηaux/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hτloss : τ ≤ ω/(16*((J : ℝ)+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτloss' : τ*(16*((J : ℝ)+1)) ≤ ω :=
    (le_div_iff₀ (by positivity)).mp hτloss
  obtain ⟨I, hI⟩ := exists_nat_gt ((49/100 : ℝ)/e)
  have hIpos : 0 < I := by
    have hz : (0 : ℝ) < I := (div_pos (by norm_num) he).trans hI
    exact_mod_cast hz
  have hwidth : (49/100 : ℝ) ≤ (I : ℝ)*e :=
    le_of_lt ((div_lt_iff₀ he).mp hI)
  refine ⟨τ, ε, e, κaux, ηaux, I, hτ, by linarith, by linarith,
    hε, by linarith, he, by linarith, hκ, by linarith, hη.le, ?_,
    hIpos, hwidth, ?_⟩
  · dsimp [ηaux]
    linarith
  · nlinarith

lemma density_internal_height (U τ : ℝ) (I : ℕ) (hU : 1 ≤ U) (hτ : 0 ≤ τ) :
    1+(2*Real.pi*U^(τ/2)+((3*I : ℕ) : ℝ)*U^τ) ≤
      (1+2*Real.pi+3*(I : ℝ))*U^τ := by
  have hp : 1 ≤ U^τ := Real.one_le_rpow hU hτ
  have hhalf : U^(τ/2) ≤ U^τ := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hpi : 0 < Real.pi := Real.pi_pos
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

lemma density_fiber_height (U τ C K₀ : ℝ) (I J : ℕ)
    (hU : 1 ≤ U) (hτ : 0 ≤ τ) (hC : 0 ≤ C) :
    let h := 2*Real.pi*U^(τ/2)+((3*I : ℕ) : ℝ)*U^τ
    fiberConstant (C*(1+h)^J) h K₀ ≤
      (192*C*max 1 K₀*(1+2*Real.pi+3*(I : ℝ))^(J+1)) *
        U^(τ*((J : ℝ)+1)) := by
  dsimp only
  let h := 2*Real.pi*U^(τ/2)+((3*I : ℕ) : ℝ)*U^τ
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hc : 0 ≤ 192*C*max 1 K₀ := by positivity
  have hp := pow_le_pow_left₀ (show 0 ≤ 1+h by positivity)
    (density_internal_height U τ I hU hτ) (J+1)
  have hpow : (U^τ)^(J+1) = U^(τ*((J : ℝ)+1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hU)]
    simp
  calc
    fiberConstant (C*(1+h)^J) h K₀ = (192*C*max 1 K₀)*(1+h)^(J+1) := by
      unfold fiberConstant
      rw [pow_succ]
      ring
    _ ≤ (192*C*max 1 K₀)*((1+2*Real.pi+3*(I : ℝ))*U^τ)^(J+1) :=
      mul_le_mul_of_nonneg_left hp hc
    _ = _ := by rw [mul_pow, hpow]; ring

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.DensityArithmetic -/

/- BEGIN ORIGINAL MODULE Analytic.DensityLargeHeight ; sha256 f20df469a15eb99b84ed6045765d5c834f937e20a094c975dec48a47df08458f -/
section


set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.Local44.Analytic

/-- For heights above the internal strip, a fixed polynomial height factor
already pays the elementary lattice count. -/
theorem row_scale_le_large_height_power (U τ T : ℝ) (A : ℕ)
    (hU : 1 ≤ U) (hτA : 1 ≤ τ * (A : ℝ)) (hT : U^τ < T) :
    U ≤ (1+|T|)^A := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hbase : U^τ ≤ 1+|T| := by linarith [le_abs_self T]
  calc
    U = U^(1 : ℝ) := (Real.rpow_one U).symm
    _ ≤ U^(τ*(A : ℝ)) := Real.rpow_le_rpow_of_exponent_le hU hτA
    _ = (U^τ)^A := by rw [Real.rpow_mul hU0.le, Real.rpow_natCast]
    _ ≤ (1+|T|)^A := pow_le_pow_left₀ (Real.rpow_nonneg hU0.le _) hbase A

open HeckeInverseAmplification ProbeHighRowFamily

theorem free_row_large_height_count (rows : Finset FreeRow) (U τ T ρ : ℝ) (A : ℕ)
    (hU : 1 ≤ U) (hτA : 1 ≤ τ*(A : ℝ)) (hT : U^τ < T) (hρ : 0 ≤ ρ)
    (hrows : ∀ u ∈ rows, rowNorm u ≤ U) :
    (rows.card : ℝ) ≤ 128*(1+|T|)^A*U^ρ := by
  have hscale := row_scale_le_large_height_power U τ T A hU hτA hT
  have hpow : 1 ≤ U^ρ := Real.one_le_rpow hU hρ
  calc
    (rows.card : ℝ) ≤ 128*U := freeRow_count rows U hU hrows
    _ ≤ 128*(1+|T|)^A := mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ ≤ 128*(1+|T|)^A*U^ρ :=
      le_mul_of_one_le_right (by positivity) hpow

#print axioms free_row_large_height_count
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.DensityLargeHeight -/

/- BEGIN ORIGINAL MODULE Analytic.JointCancellationNorm ; sha256 9940f3ad59b93a49908b0623eb288c3e26274a7b96b6d0b3a30f4631f5acb82d -/
section





/-! The canceled first primes are absent from the effective row factor.
Their fifth powers and that effective factor therefore fit inside the
fifth power of the actual active conductor. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open CenteredMomentSectorLocalization CenteredMomentFirstSourceConductorCaps
open CenteredMomentSupportedCorrelation CenteredMomentFirstCanonicalFamily
local notation "O" => ActualEisensteinCubic.O

private def cancellationNormHom : O →* ℝ where
  toFun := normValue
  map_one' := by simp [normValue]
  map_mul' := normValue_mul

private lemma cancellation_norm_prod {ι : Type*} [Fintype ι] (f : ι → O) :
    normValue (∏ i,f i) = ∏ i,normValue (f i) :=
  map_prod cancellationNormHom f Finset.univ

private lemma cancellation_norm_pow (x : O) (n : ℕ) :
    normValue (x^n) = normValue x^n := map_pow cancellationNormHom x n

lemma active_conductor_norm_product (C D : Ideal O) (hC : Supported C) :
    normValue (activeConductor C D) = ∏ i : ActiveIndex C D,normValue (activePrimary C D i) := by
  obtain ⟨u,hu⟩ := prime_modulus_unit_product (activePrime C D) (activePrimary C D)
    (activePrimary_span C D hC)
  change activeConductor C D = _ at hu
  have hunit : normValue (u : O) = 1 := by
    simp only [normValue,Ideal.span_singleton_eq_top.mpr u.isUnit,Ideal.absNorm_top,Nat.cast_one]
  rw [hu,normValue_mul,hunit,one_mul,cancellation_norm_prod]

lemma left_effective_norm_product (C D : Ideal O) :
    normValue (leftEffectiveFactor C D) =
      ∏ i : ActiveIndex C D,normValue (activePrimary C D i)^((1+activeExponent C D i)%6) := by
  simp only [leftEffectiveFactor,cancellation_norm_prod,cancellation_norm_pow]

lemma canceled_ideal_norm_product (C D : Ideal O) (k : ℕ) :
    ((canceledIdeal C D k).absNorm : ℝ) =
      ∏ i : ActiveIndex C D,if activeExponent C D i=k then normValue (activePrimary C D i) else 1 := by
  change normValue (canceledFactor C D k) = _
  rw [canceledFactor,cancellation_norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp [normValue]

/-- Each active prime contributes at most five; a canceled prime contributes
zero to the effective factor and five to the deletion factor. -/
theorem left_effective_canceled_norm (C D : Ideal O) (hC : Supported C) :
    normValue (leftEffectiveFactor C D)*((canceledIdeal C D 5).absNorm : ℝ)^5 ≤
      normValue (activeConductor C D)^5 := by
  rw [left_effective_norm_product,canceled_ideal_norm_product,active_conductor_norm_product C D hC,
    ← Finset.prod_pow,← Finset.prod_mul_distrib,← Finset.prod_pow]
  apply Finset.prod_le_prod₀
  · intro i _
    have hn : 0 ≤ normValue (activePrimary C D i) := by unfold normValue; positivity
    positivity
  · intro i _
    have hn := normValue_ge_one _ (supported_element_ne_zero _ (activePrimary_supported C D hC i))
    by_cases h : activeExponent C D i=5
    · simp only [h,ite_true]
      norm_num
    · simp only [h,ite_false,one_pow,mul_one]
      exact pow_le_pow_right₀ hn (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))

/-- The exact logarithmic cancellation budget. It applies unchanged to the
swapped first pair, hence to either physical first side. -/
theorem left_effective_canceled_log (C D : Ideal O) (hC : Supported C)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (normValue (leftEffectiveFactor C D)) ≤
      5*(Real.logb Z (normValue (activeConductor C D))-
        Real.logb Z ((canceledIdeal C D 5).absNorm : ℝ)) := by
  have hF := normValue_pos _ (show leftEffectiveFactor C D ≠ 0 from active_product_pow_ne_zero C D hC _)
  have hR := normValue_pos _ (canceledFactor_ne_zero C D hC 5)
  change 0 < ((canceledIdeal C D 5).absNorm : ℝ) at hR
  have hh := Real.logb_le_logb_of_le hZ (mul_pos hF (pow_pos hR 5))
    (left_effective_canceled_norm C D hC)
  rw [Real.logb_mul hF.ne' (pow_pos hR 5).ne',Real.logb_pow,Real.logb_pow] at hh
  norm_num at hh
  linarith only [hh]

/-- Nonnegative actual coordinates, together with their cancellation budget. -/
theorem left_cancellation_coordinates (C D : Ideal O) (hC : Supported C)
    (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ Real.logb Z (normValue (leftEffectiveFactor C D)) ∧
    0 ≤ Real.logb Z ((canceledIdeal C D 5).absNorm : ℝ) ∧
    Real.logb Z ((canceledIdeal C D 5).absNorm : ℝ) ≤
      Real.logb Z (normValue (activeConductor C D)) ∧
    Real.logb Z (normValue (leftEffectiveFactor C D)) ≤
      5*(Real.logb Z (normValue (activeConductor C D))-
        Real.logb Z ((canceledIdeal C D 5).absNorm : ℝ)) := by
  have hF := Real.logb_nonneg hZ (normValue_ge_one _
    (show leftEffectiveFactor C D ≠ 0 from active_product_pow_ne_zero C D hC _))
  have hR := Real.logb_nonneg hZ (normValue_ge_one _ (canceledFactor_ne_zero C D hC 5))
  change 0 ≤ Real.logb Z ((canceledIdeal C D 5).absNorm : ℝ) at hR
  have hh := left_effective_canceled_log C D hC Z hZ
  exact ⟨hF,hR,by linarith only [hF,hh],hh⟩

/-- Fixed caps for the two extra first-sector coordinates come from the
literal supported first common ideal. No size premise on either factor is needed. -/
theorem left_cancellation_sector_caps (C D : Ideal O) (hC : Supported C)
    (Z B : ℝ) (hZ : 1 < Z) (hCcap : (C.absNorm : ℝ) ≤ Z^B) :
    0 ≤ Real.logb Z ((canceledIdeal C D 5).absNorm : ℝ) ∧
    Real.logb Z ((canceledIdeal C D 5).absNorm : ℝ) ≤ B ∧
    0 ≤ Real.logb Z (normValue (leftEffectiveFactor C D)) ∧
    Real.logb Z (normValue (leftEffectiveFactor C D)) ≤ 5*B := by
  have hcoords := left_cancellation_coordinates C D hC Z hZ
  have hactive : normValue (activeConductor C D) ≤ Z^B := by
    rw [normValue_eq_embedding]
    exact ((original_factor_caps C D hC ∅).2).trans hCcap
  have hactive₀ := normValue_pos _ (supported_element_ne_zero _ (activeConductor_supported C D hC))
  have hlog := Real.logb_le_logb_of_le hZ hactive₀ hactive
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hlog
  refine ⟨hcoords.2.1,hcoords.2.2.1.trans hlog,hcoords.1,?_⟩
  linarith only [hcoords.2.1,hcoords.2.2.2,hlog]

#print axioms left_effective_canceled_norm
#print axioms left_effective_canceled_log
#print axioms left_cancellation_sector_caps
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCancellationNorm -/

/- BEGIN ORIGINAL MODULE Analytic.JointSupport ; sha256 14a3f0b0aeac1109d905127a1c90dd4a69d45c7142f340f34bbdb57d1967b35e -/
section




/-! Concrete support reconstruction for the joint first-label/second-row map.
The first projector is retained in the second common radical. -/

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger
open CenteredMomentCompleteCommon CenteredMomentRankinRadical
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem joint_primeSupport_mono {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    primeSupport I ⊆ primeSupport J := by
  intro P hP
  have hp := support_prime hP
  have hd := (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)).trans hIJ
  simpa only [primeSupport, Multiset.mem_toFinset, mem_normalizedFactors_iff hJ,
    hp, true_and] using hd

theorem joint_prime_mem_support {P I : Ideal O} (hI : I ≠ 0) (hP : Prime P)
    (hd : P ∣ I) : P ∈ primeSupport I := by
  simpa only [primeSupport, Multiset.mem_toFinset, mem_normalizedFactors_iff hI,
    hP, true_and] using hd

def jointMissingRadical (C : Ideal O) (w : O) : Ideal O :=
  ∏ P ∈ primeSupport C \ primeSupport (Ideal.span {w}), P

theorem jointMissingRadical_ne_zero (C : Ideal O) (w : O) :
    jointMissingRadical C w ≠ 0 := support_product_ne_zero Finset.sdiff_subset

theorem jointMissingRadical_squarefree (C : Ideal O) (w : O) :
    Squarefree (jointMissingRadical C w) := squarefree_support_product Finset.sdiff_subset

theorem jointMissingRadical_support (C : Ideal O) (w : O) :
    primeSupport (jointMissingRadical C w) =
      primeSupport C \ primeSupport (Ideal.span {w}) := by
  change (normalizedFactors (∏ P ∈ primeSupport C \ primeSupport (Ideal.span {w}), P)).toFinset = _
  rw [factors_support_product Finset.sdiff_subset]
  exact Finset.val_toFinset _

/-- The missing radical and the row support determine the support of both
first common labels, without imposing any bound on their valuations. -/
theorem joint_first_support (C D : Ideal O) (w : O) (hw : w ≠ 0)
    (hCD : primeSupport C = primeSupport D) :
    primeSupport C ⊆ primeSupport (jointMissingRadical C w * Ideal.span {w}) ∧
    primeSupport D ⊆ primeSupport (jointMissingRadical C w * Ideal.span {w}) := by
  have hwI : Ideal.span {w} ≠ (0 : Ideal O) := by simpa using hw
  have hQ := mul_ne_zero (jointMissingRadical_ne_zero C w) hwI
  have hleft : primeSupport C ⊆
      primeSupport (jointMissingRadical C w * Ideal.span {w}) := by
    intro P hP
    by_cases hpw : P ∈ primeSupport (Ideal.span {w})
    · exact joint_primeSupport_mono hQ (dvd_mul_left _ _) hpw
    · apply joint_primeSupport_mono hQ (dvd_mul_right _ _)
      rw [jointMissingRadical_support]
      exact Finset.mem_sdiff.mpr ⟨hP, hpw⟩
  exact ⟨hleft, hCD ▸ hleft⟩

theorem commonRadical_dvd_frequency (C D : Ideal O) (hC : Supported C) :
    commonRadical C D ∣ Ideal.span {commonFrequencyGenerator C D} := by
  rw [commonFrequencyGenerator, span_finset_product]
  simp_rw [← Ideal.span_singleton_pow, commonPrime_span C D hC]
  have he : commonRadical C D = ∏ P : CommonIndex C D, P.val := by
    exact (Finset.prod_coe_sort (s := commonSupport C D) (f := id)).symm
  rw [he]
  apply Finset.prod_dvd_prod_of_dvd
  intro P _
  simpa only [pow_one] using pow_dvd_pow P.val
    (show 1 ≤ min (leftExponent C D P) (rightExponent C D P) from
      le_min (leftExponent_pos C D P) (rightExponent_pos C D P))

/-- The squarefree FIRST residual projector divides the actual second
frequency, through the minimum-exponent common frequency generator. -/
theorem joint_first_projector_dvd (I J L : Ideal O) (hI : Supported I)
    (hJ : Supported J) (hL : Squarefree L) (hLI : L ∣ I) (hLJ : L ∣ J)
    (V h a : O) :
    L ∣ Ideal.span {a * (commonFrequencyGenerator (commonPart I J)
      (commonPart J I) * V * h)} := by
  have hd := old_mask_dvd_commonRadical L I J hL hI.1 hJ.1 hLI hLJ
  rw [← extracted_commonRadical I J] at hd
  apply (hd.trans (commonRadical_dvd_frequency _ _ (commonPart_supported I J hI))).trans
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
  exact (dvd_mul_right _ V |>.trans (dvd_mul_right _ h)).trans (dvd_mul_left _ a)

def jointLeftRow (C₁ D₁ C₂ D₂ : Ideal O)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O) : O :=
  primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E *
    (u : O) * leftEffectiveFactor C₁ D₁ *
    (commonFrequencyGenerator C₂ D₂ * nonunitFrequencyGenerator C₂ D₂ U * h)

theorem jointLeftRow_injective (C₁ D₁ C₂ D₂ : Ideal O)
    (hC₁ : Supported C₁) (hC₂ : Supported C₂)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) :
    Function.Injective (jointLeftRow C₁ D₁ C₂ D₂ E u U) := by
  have he := primeSubsetGenerator_ne_zero (fun P : CommonIndex C₁ D₁ => P.val) E
  have hF : leftEffectiveFactor C₁ D₁ ≠ 0 := active_product_pow_ne_zero C₁ D₁ hC₁ _
  have hG := commonFrequencyGenerator_ne_zero C₂ D₂ hC₂
  have hV := nonunitFrequencyGenerator_ne_zero C₂ D₂ hC₂ U
  intro h k heq
  unfold jointLeftRow at heq
  exact mul_left_cancel₀ hV (mul_left_cancel₀ hG
    (by simpa only [mul_assoc] using
      mul_left_cancel₀ (mul_ne_zero (mul_ne_zero he u.ne_zero) hF) heq))

theorem joint_second_support (C₁ D₁ C₂ D₂ : Ideal O) (hC₂ : Supported C₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (hw : jointLeftRow C₁ D₁ C₂ D₂ E u U h ≠ 0) :
    primeSupport C₂ ⊆ primeSupport (Ideal.span {jointLeftRow C₁ D₁ C₂ D₂ E u U h}) ∧
    primeSupport D₂ ⊆ primeSupport (Ideal.span {jointLeftRow C₁ D₁ C₂ D₂ E u U h}) := by
  have hwI : Ideal.span {jointLeftRow C₁ D₁ C₂ D₂ E u U h} ≠ (0 : Ideal O) := by
    simpa using hw
  have hd : commonRadical C₂ D₂ ∣ Ideal.span {jointLeftRow C₁ D₁ C₂ D₂ E u U h} := by
    apply (commonRadical_dvd_frequency C₂ D₂ hC₂).trans
    apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
    exact (dvd_mul_right _ _ |>.trans (dvd_mul_right _ h)).trans (dvd_mul_left _ _)
  have hs := joint_primeSupport_mono hwI hd
  rw [commonRadical_support, ← hCD₂, Finset.inter_self] at hs
  exact ⟨hs, hCD₂ ▸ hs⟩

/-- The exact first transform only sums principal-support mask divisors. -/
theorem actual_first_mask_disjoint_active (C D : Ideal O)
    (E : Finset (CommonIndex C D))
    (hE : E ∈ (principalSupport Finset.univ (leftExponent C D)
      (rightExponent C D)).powerset) :
    Disjoint E (activeSupport Finset.univ (leftExponent C D) (rightExponent C D)) := by
  apply Finset.disjoint_left.mpr
  intro P hP hA
  have hp := (Finset.mem_filter.mp ((Finset.mem_powerset.mp hE) hP)).2
  exact (Finset.mem_filter.mp hA).2 hp

theorem joint_mask_prime_dvd (C₁ D₁ C₂ D₂ : Ideal O)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (P : CommonIndex C₁ D₁) (hP : P ∈ E) :
    P.val ∣ Ideal.span {jointLeftRow C₁ D₁ C₂ D₂ E u U h} := by
  have he : P.val ∣ Ideal.span
      {primeSubsetGenerator (fun Q : CommonIndex C₁ D₁ => Q.val) E} := by
    rw [primeSubsetGenerator, span_idealGenerator]
    exact Finset.dvd_prod_of_mem _ hP
  apply he.trans
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
  exact (dvd_mul_right _ _ |>.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)

theorem joint_active_prime_dvd (C₁ D₁ C₂ D₂ : Ideal O) (hC₁ : Supported C₁)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (P : ActiveIndex C₁ D₁) (hP : activeExponent C₁ D₁ P ≠ 5) :
    P.val.val ∣ Ideal.span {jointLeftRow C₁ D₁ C₂ D₂ E u U h} := by
  have ht := activeExponent_pos C₁ D₁ P
  have ht6 := activeExponent_lt C₁ D₁ P
  have hexp : 1 ≤ (1 + activeExponent C₁ D₁ P) % 6 := by omega
  have hfactor : P.val.val ∣ Ideal.span {leftEffectiveFactor C₁ D₁} := by
    rw [leftEffectiveFactor, span_finset_product]
    simp_rw [← Ideal.span_singleton_pow, activePrimary_span C₁ D₁ hC₁]
    have hd : P.val.val ∣ P.val.val ^ ((1 + activeExponent C₁ D₁ P) % 6) := by
      simpa only [pow_one] using pow_dvd_pow P.val.val hexp
    exact hd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ P))
  apply hfactor.trans
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
  exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)

def jointMissingIndices (C D : Ideal O) (w : O) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P => ¬ P.val ∣ Ideal.span {w})

def jointLeftCanceledIndices (C D : Ideal O) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P => netExponent (leftExponent C D P) (rightExponent C D P) = 5)

/-- Every actually missing first common prime is either an unselected
principal-support prime or a canceled active prime with exponent five. -/
theorem joint_missing_indices_subset (C₁ D₁ C₂ D₂ : Ideal O) (hC₁ : Supported C₁)
    (E : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (U : Finset (CommonIndex C₂ D₂)) (h : O) :
    jointMissingIndices C₁ D₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h) ⊆
      (principalSupport Finset.univ (leftExponent C₁ D₁) (rightExponent C₁ D₁) \ E) ∪
        jointLeftCanceledIndices C₁ D₁ := by
  intro P hP
  have hnd := (Finset.mem_filter.mp hP).2
  have hnotE : P ∉ E := fun hp => hnd (joint_mask_prime_dvd C₁ D₁ C₂ D₂ E u U h P hp)
  by_cases ht : netExponent (leftExponent C₁ D₁ P) (rightExponent C₁ D₁ P) = 0
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, hnotE⟩)
  · have hactive : P ∈ activeSupport Finset.univ (leftExponent C₁ D₁) (rightExponent C₁ D₁) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
    have hcancel : activeExponent C₁ D₁ ⟨P, hactive⟩ = 5 := by
      by_contra hc
      exact hnd (joint_active_prime_dvd C₁ D₁ C₂ D₂ hC₁ E u U h ⟨P, hactive⟩ hc)
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcancel⟩)

/-- The only actual first-transform E labels are disjoint from both the
active radical and its canceled subset. This is the source of the −E gain. -/
theorem actual_first_mask_disjoint_canceled (C D : Ideal O)
    (E : Finset (CommonIndex C D))
    (hE : E ∈ (principalSupport Finset.univ (leftExponent C D)
      (rightExponent C D)).powerset) : Disjoint E (jointLeftCanceledIndices C D) := by
  apply Finset.disjoint_left.mpr
  intro P hP hcancel
  have hz := (Finset.mem_filter.mp ((Finset.mem_powerset.mp hE) hP)).2
  have hc := (Finset.mem_filter.mp hcancel).2
  omega

#print axioms joint_first_support
#print axioms joint_first_projector_dvd
#print axioms joint_second_support
#print axioms jointLeftRow_injective
#print axioms joint_missing_indices_subset
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSupport -/
