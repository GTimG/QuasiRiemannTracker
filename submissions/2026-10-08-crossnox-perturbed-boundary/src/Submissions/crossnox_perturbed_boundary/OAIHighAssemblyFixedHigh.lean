/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighAssemblyFixedHigh.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighAssemblyHigh
import Submissions.crossnox_perturbed_boundary.OAIHighAssemblyMomentInput

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open AsymmetricGeometry
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_perturbed_high_bound
    (hβ : (boundary:ℝ)<HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (D : PerturbedHighData (HeckeZeroSupremum.beta-(boundary)))
    (F : PerturbedSourceData D)
    (counts : CountParameters F.modulus ⊤ D.small) (τ : ℝ)
    (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2) (hτcost : 4*τ<(1/200:ℝ)*D.cost)
    (hτt : τ<D.small) (hτ2 : 2*τ≤D.small) (hτeps : τ*(2+4*D.eps)<D.small) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      ∀C0 : ℝ,0≤C0 → PerturbedSourceMomentBound F counts η Z τ (C0*Z^D.small) (Z^(2*τ)) →
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) signalOffset Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(HeckeZeroSupremum.beta+signalOffset-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.small_pos
  have ht1 := D.small_cap
  have hβfloor : (51/100:ℝ)≤HeckeZeroSupremum.beta :=
    (by norm_num [boundary] : (51/100:ℝ)≤boundary).trans hβ.le
  have hconductor : (rowBase:ℝ)+3*perturbedSlotLengthShift/2+
      D.small+2*D.small≤7/8 := by linarith [D.row_threshold]
  let slotMesh := (1+6*perturbedSlotLengthShift)*D.small
  have hslotMesh : 0≤slotMesh := by
    dsimp [slotMesh, perturbedSlotLengthShift]
    positivity
  obtain ⟨n,hn,C,hC,hbound⟩ := actual_high_probe_from_count_moments_on_perturbed_boundary F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 slotMesh (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.small D.small D.small perturbedSlotLengthShift
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    hslotMesh (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.correction_tail F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=>F.w) (fun _=>F.support) (fun _=>F.smooth) (fun _=>F.bounded)
    (fun _=>F.compact) (fun _=>F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by nlinarith [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.small D.small D.small (2*τ) D.small ht ht ht (by linarith)
    D.small (2*D.small) D.small ht (by linarith) (by positivity)
    (by dsimp [perturbedSlotLengthShift]; norm_num)
    (by dsimp [perturbedSlotLengthShift]; norm_num)
    (by simpa only [slotMesh] using D.count_budget)
    (by nlinarith [D.central_budget, hτ2])
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.small/8) (by positivity) (D.small/8) (by positivity) (by norm_num) hconductor
    (by linarith) hβ hβhi
    D.sigma D.sigma_pos (by linarith [D.geometric_budget])
    (by linarith [D.principal_budget])
    D.window_budget
    (by linarith [D.high_saving, D.small_cap])
    (by linarith [D.floor_budget]) D.high_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.small
    (rowBase+3*perturbedSlotLengthShift/2+D.small)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^((rowBase:ℝ)+3*perturbedSlotLengthShift/2+D.small))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^(rowBase+3*perturbedSlotLengthShift/2+D.small) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  obtain ⟨u,hu⟩ := hne
  have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
  have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
  have ha : (51/100:ℝ)<51/100+D.e*j := by
    have hjp : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hjne
    nlinarith [D.e_pos]
  have ha' : (51/100:ℝ)+D.e*j≤7/8 := by
    have hdet := detectorMaximum_le_beta
      (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u))
      (3*idx u*Z^τ) hβfloor
    have hlabel := (hbins u).2.2.1
    simpa only [huj] using hlabel.trans (hdet.trans hβhi)
  have hrow' : ∀v∈rows',v.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm v ∧
      (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
      rowNorm v≤Z^(sourceDyadConductor Z D.small k-D.small) := by
    intro v hv
    exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,hg.2.2.2.2.2 v (hsub hv)⟩
  have hi' : (i:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight : (3*i+1:ℕ)*Z^τ≤Z^(2*τ) := by
    have hZp : 0<Z := zero_lt_one.trans hZ
    calc
      _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _≤Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
      _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
  apply hmom rows' (sourceDyadConductor Z D.small k) (51/100+D.e*j) hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
    ((17/50:ℂ)+t.1.2*Complex.I)
  · simp
  · simpa using htheight.2.trans hheight

end SevenEighths.ProbeFinalAssembly

end

end OAI
