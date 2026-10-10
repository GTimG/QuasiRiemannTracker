import QRH.Detector.ActualCubeArithmeticSaving
import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
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

theorem actual_uniform_nonfloor_cube_norm {Δ:ℝ}{D:Parameters.HighData Δ}
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
        (logCost+heightCost+heightCost*(J:ℝ))+saving≤Δ/4→
    ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀gap:ℝ,0≤gap→Δ≤gap→gap≤(1-QRH.kappa0)/2→
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
    ‖finiteCentralCubeRows S.S S.exclusions S.maximal η rows T hT
      (fun _ x=>(S.w x:ℂ)) Y S.W S.W (Z^QRH.lx) (Z^QRH.ly) Z D.e
      (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤C*(η.modulus.absNorm:ℝ)^(2*D.eps)*
      Z^(QRH.C (QRH.tightTheta+gap)-saving) := by
  obtain ⟨J,harith⟩ := actual_uniform_cube_arithmetic_saving S nslots lengths hpos hinj hsum hsmall hmin hbeta hfine
  obtain ⟨A,hA,hprofile⟩ := actual_common_cube_aggregate_norm S.W S.W 1 2 1 2
    (by norm_num) (by norm_num) S.complex_support S.complex_support
  refine ⟨J,?_⟩
  intro n τ logCost heightCost loss ν ζ μ saving hτ hτd hτcost hl hh hloss hν hζ hμ hsaving hcount hbudget
  intro η
  obtain ⟨C,hC,harith⟩ := harith n τ logCost heightCost loss ν ζ μ saving hτ hτd hτcost hl hh hloss
    hν hζ hμ hsaving hcount hbudget η
  refine ⟨A*C,by positivity,?_⟩
  filter_upwards [harith,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    constant_absorbed_eventually (3*(n:ℝ)+1) (heightCost-τ) (by linarith)] with Z hc hTlarge hheight
  refine ⟨hc.1,?_⟩
  intro gap hgap hΔgap hgap1 hκbeta d hd hd1 v a i hi hv hv' hv1 hdv ha ha1 rows hne hrows hnorm hnext hcurrent Y T hT
  have hZ:0<Z:=zero_lt_one.trans hc.1
  have hhbound : (3*i+1:ℕ)*Z^τ≤Z^heightCost := by
    have hi' : (i:ℝ)≤n := by exact_mod_cast hi
    calc
      _≤(3*(n:ℝ)+1)*Z^τ:=by push_cast;gcongr
      _≤Z^(heightCost-τ)*Z^τ:=mul_le_mul_of_nonneg_right hheight (by positivity)
      _=Z^heightCost:=by rw [←Real.rpow_add hZ];congr 1;ring
  let bound:ℝ:=C*(η.modulus.absNorm:ℝ)^(2*D.eps)*
    Z^(QRH.C (QRH.tightTheta+gap)-saving-
      ((1-QRH.ly)*a+(4/25)*QRH.lx-33/50+(16-6*QRH.ly)*D.e))
  have hb:0≤bound:=by dsimp [bound];positivity
  have hp:=hprofile D.e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i D.e_pos D.e_small ha.le ha1 hTlarge
    (by gcongr;omega) S.S S.exclusions S.maximal S.first η rows (fun u hu=>(hrows u hu).1)
    T hT (rayCubeFamily S.modulus ⊤ le_top) hnext (fun _ x=>(S.w x:ℂ)) Y
    (Z^QRH.lx) (Z^QRH.ly) Z (by positivity) (by positivity) hZ bound hb
    (fun t ht=>hc.2 gap hgap hΔgap hgap1 hκbeta d hd hd1 v a i hi hv hv' hv1 hdv ha ha1 rows hne hrows hnorm
      hnext hcurrent t ht (ht.2.trans hhbound))
  apply hp.trans_eq
  rw [QRHProbeCentralExponent.physical_scale_identity Z a D.e hZ]
  dsimp only [bound]
  calc
    _=(A*C)*(η.modulus.absNorm:ℝ)^(2*D.eps)*
      (Z^((1-QRH.ly)*a+(4/25)*QRH.lx-33/50+(16-6*QRH.ly)*D.e)*
       Z^(QRH.C (QRH.tightTheta+gap)-saving-((1-QRH.ly)*a+(4/25)*QRH.lx-33/50+(16-6*QRH.ly)*D.e))):=by ring
    _=_:=by rw [←Real.rpow_add hZ];congr 2;ring

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
