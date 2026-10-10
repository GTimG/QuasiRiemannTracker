import QRH.Detector.ActualSourceCount
import QRH.Detector.OptimizedSourceAmplitudeClasses

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

theorem actual_uniform_amplitude_class_count {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)(hinj:Function.Injective lengths)
    (hsum:∑j,lengths j=QRH.ell)(hsmall:∀j,lengths j≤D.t/200)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,lengths j≤dynamicMesh D.t/200):
    ∃J:ℕ,∀(n:ℕ)(τ logCost heightCost:ℝ),
      0<τ→τ<(1/200:ℝ)/2→4*τ<(1/200:ℝ)*D.cost→
      0<logCost→τ<heightCost→
    ∃K:ℝ,0<K ∧ ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀gap:ℝ,0≤gap→gap≤(1-QRH.kappa0)/2→
      2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*gap→
    ∀d:ℝ,(1/200:ℝ)≤d→d≤7/8→∀(a ν:ℝ)(i:ℕ),i≤n→
      51/100<a→a≤1→0<ν→
    ∀rows:Finset FreeRow,rows.Nonempty→
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S.S S.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t))→
    (∀u∈rows,detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*D.e)→
    (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ))→
    ∀z:ℂ,z.re=17/50→|z.im|≤Z^heightCost→
    ∀bin:BinLabel (Finset.univ:Finset (Fin nslots)) ((2*a-1)/2) D.t,
    let Q:=HeckeDetectorPhysicalSelection.physical S.modulus ⊤ (fun u:FreeRow=>u.val)
      (fun _ x=>(S.w x:ℂ)) (fun _=>2) (fun j=>lengths j/d) (fun _=>z) (Z^d);
    let rows':=amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>lengths j/d) Q bin;
    let q:=classMean Finset.univ ((2*a-1)/2) D.t (fun j=>lengths j/d) bin;
    rows'.Nonempty→(rows'.card:ℝ)≤K*C*Z^(logCost+heightCost+heightCost*(J:ℝ))*(Z^d)^
      (QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap D.ε D.t D.t ν) := by
  obtain ⟨J,hcount⟩ := actual_uniform_adaptive_source_count S nslots lengths hpos hinj hbeta hfine
  refine ⟨J,?_⟩
  intro n τ logCost heightCost hτ hτd hτcost hl hh
  obtain ⟨K,hK,hcount⟩ := hcount n (7/8) τ logCost heightCost D.t (by norm_num) hτ hl hh D.t_pos
  refine ⟨K,hK,?_⟩
  intro η
  obtain ⟨C,hC,hcount⟩ := hcount η
  have hbatches := QRHProbeHighRowFamily.actual_source_amplitude_batches S.modulus ⊤ le_top
    S.S S.exclusions S.maximal η (1/200) (7/8) τ D.ε D.e D.κ D.cost D.t D.t D.t n
    (by norm_num) (by norm_num) (by norm_num) hτ hτd hτcost
    D.epsilon_pos D.e_pos D.e_small D.kappa_pos D.kappa_small D.cost_pos.le
    D.t_pos D.t_pos.le D.t_pos (by nlinarith [D.detector_budget])
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,hbatches] with Z hc hb
  refine ⟨hc.1,?_⟩
  intro gap hgap hgap1 hκbeta d hd hd1 a ν i hi ha ha1 hν rows hne hrows hnext hcurrent z hz hzheight
    bin Q rows' q hne'
  have hZ : 0<Z := zero_lt_one.trans hc.1
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (Z^(d-D.t)+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hrows u hu).2.2.2]⟩
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hb d hd hd1 (Z^(d-D.t)+1) rows hne hband
      (fun u hu=>(hrows u hu).2.2.1) (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha1 hnext hcurrent
      nslots lengths hpos (fun j=>by simpa [div_eq_mul_inv,mul_comm] using hsmall j) hsum
      (fun _ x=>(S.w x:ℂ)) (fun _=>2) (fun _=>z) bin hne'
  have hsub : B.rows⊆rows := hBr ▸ Finset.filter_subset _ _
  have hbcount := hc.2 gap hgap hgap1 hκbeta rows (fun u hu=>(hrows u hu).2.1) d hd hd1 a ν q i hi ha ha1 hν B
    hsub (hBr.symm ▸ hne') hBin hMean hBd hW hWidths (fun s=>by rw [hUpper])
    (fun s=>by rw [hExternal];exact hz) (fun s=>by rw [hExternal];exact hzheight)
  simpa only [hBr,hMesh] using hbcount

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
