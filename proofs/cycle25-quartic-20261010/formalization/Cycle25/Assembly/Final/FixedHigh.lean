import Cycle25.Assembly.Transport.HighAssembly
import Cycle25.Assembly.Weighted.FullWCellInput
import Cycle25.Assembly.Count.OriginalMomentInput
import Cycle25.Assembly.Low.SourceProbe
import Cycle25.Assembly.Final.Geometry
/-! Fixed-data specialization of the genuine high transport and mixed cell
estimate. Adapted from weighted upstream HighRows/FixedHigh, revision
2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0 attribution retained. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.Cycle25WeightedHighFinalAssembly
open ProbeFinalAssembly Cycle25ProbeFinalAssembly Cycle25HighRowFamily
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound_of_fullW (hβ : Cycle25.theta < HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (D : Cycle25.HighParameters.HighData (HeckeZeroSupremum.beta-Cycle25.theta))
    (F : WeightedSourceData D.toMomentData)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ)
    (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2) (hτcost : 4*τ<(1/200:ℝ)*D.cost)
    (hτt : τ < D.t) (hτ2 : 2*τ ≤ D.t) (hτeps : τ*(2+4*D.eps) < D.t) :
    ∃n : ℕ,0 < n ∧ ∃C : ℝ,0 < C ∧ ∀η : Character,∃Ct : ℝ,0 < Ct ∧ ∀ᶠZ : ℝ in atTop,
      ∀C0 : ℝ,1 ≤ C0 → ∀weightedC : ℝ,0 ≤ weightedC → old_sourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      FullWCellsAt D F η Z τ n weightedC C0 →
      ‖sourceProbe D F η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-(4+Cycle25.b)/6) Z‖≤
        (Ct+C*(2+weightedC)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(HeckeZeroSupremum.beta-(4+Cycle25.b)/6-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : Cycle25.h+D.t+2*D.t≤7/8 := by linarith [Cycle25.h_interval.2]
  have hcoeff : (16-6*Cycle25.ly)*D.e ≤ ((13243:ℝ)/1000+1)*D.e := by
    nlinarith [Cycle25.ly_coarse.1,D.e_pos]
  have hfinal : (159*D.ε+D.t+D.t+7*D.t)+(12*D.e+D.eps*(D.N+8))+
      (D.t+2*τ+D.t+D.t+D.t*Cycle25.ell+(16-6*Cycle25.ly)*D.e)+2*D.t ≤ 1/4000 := by
    have hbase := D.central_budget
    have hdet := D.detector_budget
    have heps := D.epsilon_small
    have hcost := D.cost_pos
    have hkap := D.kappa_pos
    have htheta := Cycle25.LowGeometry.theta_coarse
    nlinarith only [hbase,hdet,heps,hcost,hkap,hβhi,hcoeff,hτ2,htheta]
  obtain ⟨n,hn,C,hC,hbound⟩ := actual_high_probe_from_moments_and_fullW F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=>F.w) (fun _=>F.support) (fun _=>F.smooth) (fun _=>F.bounded)
    (fun _=>F.compact) (fun _=>F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by nlinarith [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t D.t (2*τ) D.t ht ht ht (by linarith)
    D.t (2*D.t) ht (by linarith)
    (by linarith only [D.weighted_top])
    hfinal
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    Cycle25.weightedTarget (D.t/8) (Cycle25.FinalAssembly.weighted_target_lower hβ.le)
    (by positivity) (D.t/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le hβhi
    D.sigma D.sigma_pos D.geometric_budget D.principal_budget D.window_budget D.floor_budget
    (Cycle25.FinalAssembly.weighted_target_saving D hβ) counts
  refine ⟨n,hn,C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.t (Cycle25.h+D.t)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 weightedC hweightedC hmom hcells
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0 weightedC hweightedC
  · intro k hk i hi j hj
    dsimp only
    intro hne t htheight
    let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(Cycle25.h+D.t))) grid
    let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
    have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
    have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
    have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ Z^(Cycle25.h+D.t) := by
      intro u hu
      have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
      exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
    have hg := hgeo rows hrows k (hne.mono hsub)
    obtain ⟨u,hu⟩ := hne
    have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
    have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
    have ha : (51/100:ℝ)<51/100+D.e*j := by
      have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hjne
      nlinarith [D.e_pos]
    have ha' : (51/100:ℝ)+D.e*j≤7/8 := by simpa only [huj] using (hbins u).2.1
    have hrow' : ∀v∈rows',v.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm v ∧
        (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
        rowNorm v ≤ Z^(sourceDyadConductor Z D.t k-D.t) := by
      intro v hv
      exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
        ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,hg.2.2.2.2.2 v (hsub hv)⟩
    have hi' : (i:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hheight : (3*i+1:ℕ)*Z^τ ≤ Z^(2*τ) := by
      have hZp : 0 < Z := zero_lt_one.trans hZ
      calc
        _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
        _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
        _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
    have hdelta : 2*((51/100:ℝ)+D.e*j)-1 ≤ 5/6 := by linarith only [ha']
    simp only [ite_eq_left hdelta]
    apply hmom rows' (sourceDyadConductor Z D.t k) (51/100+D.e*j) hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
      ((17/50:ℂ)+t.1.2*Complex.I)
    · simp
    · simpa using htheight.2.trans hheight
  · have hc := hcells idx grid
      (by
        intro u hu
        exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,(hbins u).2.1⟩)
      (by
        intro u hu
        exact (hbins u).2.2.2.2.1)
      (by
        intro u hu
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1)
    intro k hk i hi j hj
    dsimp only
    intro hne hd hdelta hcap
    exact hc k hk i hi j hj hne hd hdelta (by linarith only [hcap])

end SevenEighths.Cycle25WeightedHighFinalAssembly

end

end OAI
