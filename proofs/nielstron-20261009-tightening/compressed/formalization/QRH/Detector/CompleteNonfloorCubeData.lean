import QRH.NumericFacts
import QRH.Detector.ActualNormalizedNonfloorCube
import QRH.Detector.OptimizedData

/-! A fully instantiated optimized nonfloor central-cube estimate. Compatible
slots and small scales are proved to exist; the tail follows the height degree. -/
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHUniformDetectorMoment
open HeckeFamily ProbePhysical ProbeFinalAssembly HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily QRHDynamicMomentInput
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem exists_optimized_nonfloor_cube_bound_with_parameters (gap:ℝ) (hgap:0<gap)
    (hgap1:gap≤(1-QRH.kappa0)/2)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*gap)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta):
    ∃D:Parameters.HighData gap,∃S:SourceData D,∃τ:ℝ,0<τ ∧
    τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧
    D.t<(1/10000000000000000000000000000:ℝ) ∧ 2000*D.ε≤D.t ∧ 2000*D.e≤D.t ∧
    ((D.N:ℝ)+8)*D.eps≤D.t ∧
    (∀j,QRHParameters.optimizedLengths D j≤D.t/200) ∧ τ*(2+4*D.eps)<D.t ∧
    ∀n:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀d:ℝ,(1/200:ℝ)≤d→d≤7/8→∀(v a:ℝ)(i:ℕ),i≤n→
      0≤v→v≤QRH.h+QRH.zeta→d-v≤2*D.t→51/100<a→a≤1→
    ∀rows:Finset FreeRow,rows.Nonempty→
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S.S S.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t))→
    (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v)→
    (∀u∈rows,detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*D.e)→
    (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ))→
    let Y:Fin D.N→ℝ:=fun j=>Z^(QRHParameters.optimizedLengths D j);
    let T:Fin D.N→Finset ProbePhysical.PrimeIdeal:=fun j=>ProbeRaySlots.pool
      (RayQuotient.identityClass S.modulus ⊤) S.S 1 2 (Y j);
    let hT:∀j P,P∈T j→P.val∉S.S:=fun j P hP=>
      (ProbeRaySlots.mem_pool _ S.S 1 2 (Y j) P).mp hP |>.2.2.2;
    let normer:=PrincipalMellinResidues.sourceResidueConstant S.W S.W S.modulus*
      (Probe.principalScalar Finset.univ Z QRH.ell
        (PrincipalSignalComparison.slotMass T
          (ProbePrincipalResidueActual.residueWeights (fun _=>S.w) Y)):ℂ);
    normer≠0 ∧ ‖finiteCentralCubeRows S.S S.exclusions S.maximal η rows T hT
      (fun _ x=>(S.w x:ℂ)) Y S.W S.W (Z^QRH.lx) (Z^QRH.ly) Z D.e
      (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤C*(η.modulus.absNorm:ℝ)^(2*D.eps)*
      Z^(QRH.C (QRH.tightTheta+gap)-D.sigma/2) := by
  obtain ⟨D,ht,hsmall,hfine,hε,he,heps⟩:=QRHParameters.exists_optimized_data gap hgap
  obtain ⟨S⟩:=exists_source_data D
  obtain ⟨J,hcube⟩:=actual_uniform_normalized_nonfloor_cube S D.N (QRHParameters.optimizedLengths D)
    (QRHParameters.optimizedLengths_pos D) (QRHParameters.optimizedLengths_injective D)
    (QRHParameters.optimizedLengths_sum D) hsmall (QRHParameters.optimizedLengths_lower D) hbeta hfine
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩:=D.height_choice (J:ℝ) (Nat.cast_nonneg J)
  have hbudget:=QRHParameters.optimized_central_budget D ht hε he heps J τ hτ hτJ
  refine ⟨D,S,τ,hτ,hτd,hτcost,ht,hε,he,heps,hsmall,hτeps,?_⟩
  intro n η
  obtain ⟨C,hC,hcube⟩:=hcube n τ D.t (2*τ) D.t D.t QRH.zeta (2*D.t) D.sigma
    hτ hτd hτcost D.t_pos (by linarith) hτeps D.t_pos (by norm_num [QRH.zeta])
    (by linarith [D.t_pos]) D.sigma_pos D.count_budget hbudget η
  refine ⟨C,hC,?_⟩
  filter_upwards [hcube] with Z hc
  refine ⟨hc.1,?_⟩
  intro d hd hd1 v a i hi hv hv' hdv ha ha1 rows hne hrows hnorm hnext hcurrent
  have hv1:v≤1:=by
    have hh:QRH.h+QRH.zeta≤1:=by linarith [QRH.NumericFacts.h_zeta_upper]
    exact hv'.trans hh
  exact hc.2 gap hgap.le hgap1 hκbeta d hd hd1 v a i hi hv hv' hv1 hdv ha ha1 rows hne hrows hnorm hnext hcurrent

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
