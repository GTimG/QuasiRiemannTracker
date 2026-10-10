import QRH.Detector.ActualAmplitudeClassCount
import QRH.Detector.OptimizedClassArithmetic
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary

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

theorem actual_uniform_cube_class_bound {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)(hinj:Function.Injective lengths)
    (hsum:∑j,lengths j=QRH.ell)(hsmall:∀j,lengths j≤D.t/200)
    (hmin:∀j,(7/8:ℝ)*D.rmin≤lengths j)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,lengths j≤dynamicMesh D.t/200):
    ∃J:ℕ,∀(n:ℕ)(τ logCost heightCost loss:ℝ),
      0<τ→τ<(1/200:ℝ)/2→4*τ<(1/200:ℝ)*D.cost→
      0<logCost→τ<heightCost→τ*(2+4*D.eps)<loss→
    ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀gap:ℝ,0≤gap→gap≤(1-QRH.kappa0)/2→
      2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*gap→
    ∀d:ℝ,(1/200:ℝ)≤d→d≤7/8→∀(v a ν:ℝ)(i:ℕ),i≤n→
      0≤v→51/100<a→a≤1→0<ν→
    ∀rows:Finset FreeRow,rows.Nonempty→
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S.S S.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t))→
    (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v)→
    (∀u∈rows,detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*D.e)→
    (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ))→
    ∀t:ProbeMellinBoundary.HeightSpace,
      ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ)→
      |t.1.2|≤Z^heightCost→
    let z:ℂ:=(17/50:ℂ)+t.1.2*Complex.I;
    ∀bin:BinLabel (Finset.univ:Finset (Fin nslots)) ((2*a-1)/2) D.t,
    let Q:=HeckeDetectorPhysicalSelection.physical S.modulus ⊤ (fun u:FreeRow=>u.val)
      (fun _ x=>(S.w x:ℂ)) (fun _=>2) (fun j=>lengths j/d) (fun _=>z) (Z^d);
    let rows':=amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>lengths j/d) Q bin;
    let q:=classMean Finset.univ ((2*a-1)/2) D.t (fun j=>lengths j/d) bin;
    let Y:Fin nslots→ℝ:=fun j=>Z^(lengths j);
    let T:Fin nslots→Finset ProbePhysical.PrimeIdeal:=fun j=>ProbeRaySlots.pool
      (RayQuotient.identityClass S.modulus ⊤) S.S 1 2 (Y j);
    let hT:∀j P,P∈T j→P.val∉S.S:=fun j P hP=>
      (ProbeRaySlots.mem_pool _ S.S 1 2 (Y j) P).mp hP |>.2.2.2;
    rows'.Nonempty→‖cubeArithmeticSum S.S S.exclusions S.maximal η rows' T hT
      (fun _ x=>(S.w x:ℂ)) Y a D.e t‖≤C*(η.modulus.absNorm:ℝ)^(2*D.eps)*
      Z^(logCost+heightCost+heightCost*(J:ℝ)+
        d*QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap D.ε D.t D.t ν+
        v*(a-1/2+12*D.e+D.eps*(nslots+8)-17/50)+loss-
        (4/25)*QRH.ell+q*QRH.ell+D.t*QRH.ell) := by
  obtain ⟨J,hcount⟩ := actual_uniform_amplitude_class_count S nslots lengths hpos hinj hsum hsmall hbeta hfine
  refine ⟨J,?_⟩
  intro n τ logCost heightCost loss hτ hτd hτcost hl hh hloss
  obtain ⟨K,hK,hcount⟩ := hcount n τ logCost heightCost hτ hτd hτcost hl hh
  obtain ⟨A,hA,hphysical⟩ := QRHProbeHighRowFamily.actual_class_cube_arithmetic
    S.modulus ⊤ le_top nslots n D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t
    (1/100) D.t loss D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    D.t_pos.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le D.t_pos (by norm_num) D.phase_budget D.epsilon_gap D.t_pos (by linarith) hloss
    S.S S.exclusions S.first S.maximal lengths hinj hmin
    (fun j=>by simpa [div_eq_mul_inv,mul_comm] using hsmall j)
    (fun _ x=>(S.w x:ℂ)) (fun _ x hx=>S.support (by simpa using hx))
    (fun _=>Complex.ofRealCLM.contDiff.comp S.smooth)
    (fun _ x=>by simpa [abs_of_nonneg (S.bounded x).1] using (S.bounded x).2) hsum
  intro η
  obtain ⟨C,hC,hcount⟩ := hcount η
  refine ⟨A*K*C,by positivity,?_⟩
  filter_upwards [hcount,hphysical η] with Z hc hp
  refine ⟨hc.1,?_⟩
  intro gap hgap hgap1 hκbeta d hd hd1 v a ν i hi hv ha ha1 hν rows hne hrows hnorm
    hnext hcurrent t ht hheight z bin Q rows' q Y T hT hne'
  have hZ : 0<Z := zero_lt_one.trans hc.1
  have hd0 : 0<d := by linarith
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hcard := hc.2 gap hgap hgap1 hκbeta d hd hd1 a ν i hi ha ha1 hν rows hne hrows
    hnext hcurrent z (by simp [z]) (by simpa [z] using hheight) bin hne'
  have hbound := hp d hd hd1 v a q (K*C*Z^(logCost+heightCost+heightCost*(J:ℝ)))
    (QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap D.ε D.t D.t ν)
    hv ha.le ha1 (by positivity) rows' (fun u hu=>hrows u (hsub hu))
    (fun u hu=>hnorm u (hsub hu)) hcard i hi (fun u hu=>hnext u (hsub hu)) t ht
    (fun u hu=>source_amplitude_class_mean S.modulus ⊤ lengths (fun _ x=>(S.w x:ℂ))
      Z d 2 a D.t z hZ hd0.ne' D.t_pos rows bin u hu)
  apply hbound.trans_eq
  rw [show logCost+heightCost+heightCost*(J:ℝ)+
      d*QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap D.ε D.t D.t ν+
      v*(a-1/2+12*D.e+D.eps*(nslots+8)-17/50)+loss-
      (4/25)*QRH.ell+q*QRH.ell+D.t*QRH.ell=
      (logCost+heightCost+heightCost*(J:ℝ))+
      (d*QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap D.ε D.t D.t ν+
      v*(a-1/2+12*D.e+D.eps*(nslots+8)-17/50)+loss-
      (4/25)*QRH.ell+q*QRH.ell+D.t*QRH.ell) by ring,
    Real.rpow_add hZ (logCost+heightCost+heightCost*(J:ℝ))]
  ring

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
