import QRH.Detector.ActualNonfloorCubeNorm
import QRH.PrimeRows.CubeNormalizer
/-! Counts for the actual amplitude partition of source rows at the optimized
cutoff and slot total. Supported witnesses and all moment estimates are proved.
The natural-number height degree precedes every tail-parameter choice. -/
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHUniformDetectorMoment
open HeckeFamily ProbePhysical ProbeFinalAssembly HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily QRHDynamicMomentInput
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem actual_uniform_normalized_nonfloor_cube {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)(hinj:Function.Injective lengths)
    (hsum:∑j,lengths j=QRH.ell)(hsmall:∀j,lengths j≤D.t/200)
    (hmin:∀j,(7/8:ℝ)*D.rmin≤lengths j)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,lengths j≤dynamicMesh D.t/200):
    ∃J:ℕ,∀(n:ℕ)(τ logCost heightCost loss ν ζ μ saving:ℝ),
      0<τ→τ<(1/200:ℝ)/2→4*τ<(1/200:ℝ)*D.cost→
      0<logCost→τ<heightCost→τ*(2+4*D.eps)<loss→0<ν→0≤ζ→0≤μ→0<saving→
      159*D.ε+D.t+D.t+7*ν≤1/32→
      QRH.h*(159*D.ε+D.t+D.t+7*ν)+2*ζ+(3/2)*μ+
        (26*D.e+(nslots+8)*D.eps+loss+D.t*QRH.ell)+
        (logCost+heightCost+heightCost*(J:ℝ))+saving≤(1/1000000000000000000000000:ℝ)→
    ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀gap:ℝ,0≤gap→gap≤(1-QRH.kappa0)/2→
      2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*gap→
    ∀d:ℝ,(1/200:ℝ)≤d→d≤7/8→∀(v a:ℝ)(i:ℕ),i≤n→
      0≤v→v≤QRH.h+ζ→v≤1→d-v≤μ→51/100<a→a≤1→
    ∀rows:Finset FreeRow,rows.Nonempty→
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S.S S.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t))→
    (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v)→
    (∀u∈rows,detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*D.e)→
    (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ))→
    let Y:Fin nslots→ℝ:=fun j=>Z^(lengths j);
    let T:Fin nslots→Finset ProbePhysical.PrimeIdeal:=fun j=>ProbeRaySlots.pool
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
      Z^(QRH.C (QRH.tightTheta+gap)-saving/2) := by
  obtain ⟨J,hcube⟩ := actual_uniform_nonfloor_cube_norm S nslots lengths hpos hinj hsum hsmall hmin hbeta hfine
  refine ⟨J,?_⟩
  intro n τ logCost heightCost loss ν ζ μ saving hτ hτd hτcost hl hh hloss hν hζ hμ hsaving hcount hbudget
  obtain ⟨A,hA,hnorm⟩ := actual_ray_normalizer_inverse_optimized S.modulus ⊤ le_top S.S S.exclusions
    1 2 (by norm_num) (by norm_num) lengths hpos hsum (fun _=>S.w)
    (fun _=>S.smooth) (fun _=>S.compact) (fun _=>S.support) (fun _ y=>(S.bounded y).1) (fun _=>S.nonzero)
    S.W S.W 1 2 1 2 (by norm_num) (by norm_num) S.complex_support S.complex_support
    S.real S.real S.nonnegative S.nonnegative S.complex_nonzero S.complex_nonzero (saving/2) (by positivity)
  intro η
  obtain ⟨C,hC,hcube⟩ := hcube n τ logCost heightCost loss ν ζ μ saving hτ hτd hτcost hl hh hloss
    hν hζ hμ hsaving hcount hbudget η
  refine ⟨C*A,by positivity,?_⟩
  filter_upwards [hcube,hnorm] with Z hc hn
  refine ⟨hc.1,?_⟩
  intro gap hgap hgap1 hκbeta d hd hd1 v a i hi hv hv' hv1 hdv ha ha1 rows hne hrows hnorm hnext hcurrent
    Y T hT normer
  have hb:=hc.2 gap hgap hgap1 hκbeta d hd hd1 v a i hi hv hv' hv1 hdv ha ha1 rows hne hrows hnorm hnext hcurrent
  have hZ:0<Z:=zero_lt_one.trans hc.1
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(C*(η.modulus.absNorm:ℝ)^(2*D.eps)*Z^(QRH.C (QRH.tightTheta+gap)-saving))*(A*Z^(saving/2)):=
      mul_le_mul hb hn.2 (norm_nonneg _) (by positivity)
    _=(C*A)*(η.modulus.absNorm:ℝ)^(2*D.eps)*
        (Z^(QRH.C (QRH.tightTheta+gap)-saving)*Z^(saving/2)):=by ring
    _=_:=by rw [←Real.rpow_add hZ];congr 2;ring

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
