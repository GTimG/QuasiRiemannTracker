import QRH.Detector.CompleteNonfloorRowsData
import QRH.Detector.OptimizedTransportBudget
import QRH.PrimeRows.OptimizedNonfloorTransport

/-! The actual optimized high probe, with every analytic moment and compatible
parameter choice discharged. The sole hypothesis is the supremum contradiction. -/
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.QRHFinalAssembly
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeFinalAssembly ProbeHighRowFamily ProbeRaySlots PrincipalMellinResidues
open PrincipalSignalComparison ProbePrincipalResidueActual QRHParameters

def optimizedNormalizedProbe {gap:ℝ} {D:Parameters.HighData gap} (S:SourceData D)
    (η:Character) (Z:ℝ):ℂ :=
  let Y:=fun j=>Z^(optimizedLengths D j)
  let T:=fun j=>pool (RayQuotient.identityClass S.modulus ⊤) S.S 1 2 (Y j)
  let normer:=sourceResidueConstant S.W S.W S.modulus *
    (Probe.principalScalar Finset.univ Z QRH.ell
      (slotMass T (residueWeights (fun _=>S.w) Y)):ℂ)
  compensatedPhysicalProbe η (calibrationForSet S.S S.maximal) S.W S.W
    (fun j=>canonicalSlotSupport (T j)) (fun _ y=>(S.w y:ℂ)) Y
    (Z^QRH.lx) (Z^QRH.ly) Z/normer

theorem exists_actual_optimized_high (hβ:QRH.tightTheta<HeckeZeroSupremum.beta):
    ∃D:Parameters.HighData (HeckeZeroSupremum.beta-QRH.tightTheta),∃S:SourceData D,
    ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
      ‖optimizedNormalizedProbe S η Z-
        HeckeSignal.signal (η.excludePrimes S.S S.exclusions.prime)
          (sourceCorrection η S.S) (QRH.C 0) Z‖≤
        C*Z^(QRH.C HeckeZeroSupremum.beta-D.sigma/8) := by
  have hgap:0<HeckeZeroSupremum.beta-QRH.tightTheta:=sub_pos.mpr hβ
  have hgap1:HeckeZeroSupremum.beta-QRH.tightTheta≤(1-QRH.kappa0)/2:=by
    dsimp [QRH.kappa0];linarith [HeckeZeroSupremum.beta_le_one]
  have hκbeta:2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*(HeckeZeroSupremum.beta-QRH.tightTheta):=by
    dsimp [QRH.kappa0];linarith
  have hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta:=by
    have hh:(51/100:ℝ)<QRH.tightTheta:=by linarith [QRH.NumericFacts.theta_lower]
    linarith
  obtain ⟨D,S,τ,hτ,hτd,hτcost,ht,hε,he,heps,hsmall,hτeps,hrows⟩:=
    QRHUniformDetectorMoment.exists_optimized_nonfloor_rows_bound_with_parameters
      _ hgap hgap1 hκbeta hbeta
  obtain ⟨hgeo,hprincipal,hwindow,hlarge,hfloor,hcap⟩:=optimized_transport_budgets D he heps
  have hepos:=D.e_pos
  have hspos:=D.sigma_pos
  have htpos:=D.t_pos
  have hrpos:=D.rmin_pos
  obtain ⟨n,hn,htransport⟩:=QRHPhysicalTails.actual_nonfloor_probe_transport S.modulus ⊤ le_top
    D.N D.e (1/4) 1 2 1 D.t 1 τ (D.rmin/2) (D.sigma/16)
    D.e_pos D.e_small (by norm_num) (by norm_num) (by linarith [D.t_pos,D.t_small])
    (by linarith [D.t_pos,D.t_small]) hτ (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by positivity) hβ.le S.S S.exclusions S.maximal S.first
    (optimizedLengths D) (fun j=>by linarith [optimizedLengths_lower D j])
    (optimizedLengths_injective D) (optimizedLengths_sum D)
    (fun _=>S.w) (fun _=>S.smooth) (fun _=>S.compact) (fun _=>S.support)
    (fun _=>S.bounded) (fun _=>S.nonzero) S.W S.W 1 2 1 2 (by norm_num) (by norm_num)
    S.complex_support S.complex_support S.real S.real S.nonnegative S.nonnegative
    S.complex_nonzero S.complex_nonzero (D.sigma/8) (by positivity) hgeo hprincipal hwindow hlarge
    D.eps D.t (1/200) (7/8) D.rmin D.ε D.κ D.cost D.t D.t D.t
    D.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos
    D.epsilon_pos D.kappa_pos D.cost_pos.le D.t_pos D.t_pos
    D.phase_budget D.epsilon_gap (by linarith) hτeps hcap
    (optimizedLengths_lower D) (fun j=>by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hsmall j) hfloor
  refine ⟨D,S,?_⟩
  intro η
  obtain ⟨Ct,hCt,htail⟩:=htransport η
  obtain ⟨Cr,hCr,hcentral⟩:=hrows n ⌊(49/100:ℝ)/D.e⌋₊ η
  refine ⟨Ct+Cr*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [htail,hcentral] with Z ht hc
  have hZ:1≤Z:=hc.1.le
  dsimp only at ht
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩:=ht
  let rows:=supportedNonfloorRows S.S S.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^(QRH.h+D.t))) grid
  have hrange:∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S.S S.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(QRH.h+D.t):=by
    intro u hu
    rcases (mem_supportedNonfloorRows S.S S.maximal _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh:=mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel:∀u∈rows,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/D.e⌋₊ ∧ grid u≠0 ∧
      51/100+D.e*grid u≤1:=by
    intro u hu
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,
      ((mem_supportedNonfloorRows S.S S.maximal _ grid u).mp hu).2.2,(hbins u).2.1⟩
  have hnext:∀u∈rows,detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^τ)<51/100+D.e*grid u+2*D.e:=
    fun u _=>(hbins u).2.2.2.2.1
  have hcurrent:∀u∈rows,51/100+D.e*grid u≤detectorMaximum
      (sourceDetectorFamily S.S S.exclusions.prime η u (rayCubeFamily S.modulus ⊤ le_top u))
      ((3*idx u:ℕ)*Z^τ):=by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hb:=(hc.2 rows hrange idx grid hlabel hnext hcurrent).2
  have hid:QRH.tightTheta+(HeckeZeroSupremum.beta-QRH.tightTheta)=HeckeZeroSupremum.beta:=by ring
  rw [hid] at hb
  have hp:Z^(QRH.C HeckeZeroSupremum.beta-D.sigma/4)≤Z^(QRH.C HeckeZeroSupremum.beta-D.sigma/8):=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcentral':=hb.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  have hsum:=(norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,SourceData.modulus,sub_add_cancel,add_mul,optimizedNormalizedProbe] using hsum

end SevenEighths.QRHFinalAssembly
end
end OAI
