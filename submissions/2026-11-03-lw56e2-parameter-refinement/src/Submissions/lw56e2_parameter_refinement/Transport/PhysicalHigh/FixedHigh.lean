/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/FixedHigh.lean
Original SHA-256: 59f20caef77a983316d4284efef7f42ceac86cfd303b0499b97c39bb4a0f1cf1
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.HighProbe
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.MomentBound
import Submissions.lw56e2_parameter_refinement.Transport.DataProbe


/-! Actual high bound for the fixed tuned data, following OpenAI
FinalAssemblyFixedHigh.lean (pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
The moment fields refer to actual arithmetic fibers and are produced separately. -/

namespace LW56e2.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
open OAI OAI.SevenEighths
open ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound (hβ : TunedCandidate.B<HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta≤7/8)
    {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)
    {Δ : ℝ} {seed : HighData Δ} (F : SourceData seed)
    (hfirst : FirstTail (4*D.P.e) F.S)
    (counts : CountParameters F.modulus ⊤ reservedLoss) (τ : ℝ)
    (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2) (hτcost : 4*τ<(1/200:ℝ)*D.P.cost)
    (hτt : τ<reservedLoss) (hτ2 : 2*τ≤reservedLoss) (hτeps : τ*(2+4*D.P.eps)<reservedLoss) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      ∀C0 : ℝ,0≤C0 → TunedSourceMomentBound F D counts η Z τ (C0*Z^reservedLoss) (Z^(2*τ)) →
      ‖LW56e2.Transport.dataProbe F D η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (TunedCandidate.signal 0) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.P.eps))*Z^(TunedCandidate.signal HeckeZeroSupremum.beta-D.P.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := reservedLoss_pos
  have ht1 := reservedLoss_le_one
  have hconductor : TunedCandidate.h+TunedCandidate.zeta+2*reservedLoss≤conductorCap := le_rfl
  obtain ⟨n,hn,C,hC,hbound⟩ := actual_high_probe_from_raw_moments F.modulus ⊤ le_top D.K
    D.P.e D.P.eps 1 2 1 reservedLoss (1/200) conductorCap D.rmin τ D.P.ε D.P.κ D.P.cost reservedLoss reservedLoss reservedLoss
    D.P.e_pos D.P.e_small D.P.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) conductorCap_pos.le conductorCap_ge_dmin D.rmin_pos hτ D.P.epsilon_pos D.P.kappa_pos
    D.P.cost_pos.le ht D.P.phase_budget D.P.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions hfirst F.maximal D.ell D.slots_injective
    D.slot_conductor_lower D.slots_upper
    (fun _=>F.w) (fun _=>F.support) (fun _=>F.smooth) (fun _=>F.bounded)
    (fun _=>F.compact) (fun _=>F.nonzero) D.slots_sum
    conductorCap_supply conductorCap_le_one D.P.epsilon_small D.P.kappa_small hτd hτcost (by nlinarith [D.P.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    reservedLoss reservedLoss reservedLoss (2*τ) reservedLoss ht ht ht (by linarith)
    (2*reservedLoss) reservedLoss (by positivity) (D.high_budget (2*τ) hτ2)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (reservedLoss/8) (by positivity) (reservedLoss/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le hceiling
    D.P.sigma D.P.sigma_pos D.geometric_budget D.principal_budget (by simpa only [D.conductor_minimum] using D.window_budget) D.floor_budget D.central_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) conductorCap reservedLoss (TunedCandidate.h+TunedCandidate.zeta)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(TunedCandidate.h+TunedCandidate.zeta))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^(TunedCandidate.h+TunedCandidate.zeta) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  have hi' : (i:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight : (3*i+1:ℕ)*Z^τ≤Z^(2*τ) := by
    have hZp : 0<Z := zero_lt_one.trans hZ
    calc
      _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _≤Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
      _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
  apply hmom rows' (fun v hv=>(hrows v (hsubr hv)).2.1)
    (sourceDyadConductor Z reservedLoss k) hg.2.2.1
    (51/100+D.P.e*j) conductorCap reservedLoss reservedLoss i
    ((17/50:ℂ)+t.1.2*Complex.I)
  · simp
  · simpa using htheight.2.trans hheight

end
end LW56e2.Transport.PhysicalHigh
