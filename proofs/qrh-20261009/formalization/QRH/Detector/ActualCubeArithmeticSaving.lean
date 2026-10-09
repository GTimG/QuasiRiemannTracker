import QRH.Detector.ActualCubeClassBound
import QRH.Detector.OptimizedAdaptiveSaving
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

theorem actual_uniform_cube_arithmetic_saving {Δ:ℝ}{D:Parameters.HighData Δ}
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
        (logCost+heightCost+heightCost*(J:ℝ))+saving≤(1/1000000000000:ℝ)→
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
    ∀t:ProbeMellinBoundary.HeightSpace,
      ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ)→
      |t.1.2|≤Z^heightCost→
    let Y:Fin nslots→ℝ:=fun j=>Z^(lengths j);
    let T:Fin nslots→Finset ProbePhysical.PrimeIdeal:=fun j=>ProbeRaySlots.pool
      (RayQuotient.identityClass S.modulus ⊤) S.S 1 2 (Y j);
    let hT:∀j P,P∈T j→P.val∉S.S:=fun j P hP=>
      (ProbeRaySlots.mem_pool _ S.S 1 2 (Y j) P).mp hP |>.2.2.2;
    ‖cubeArithmeticSum S.S S.exclusions S.maximal η rows T hT
      (fun _ x=>(S.w x:ℂ)) Y a D.e t‖≤C*(η.modulus.absNorm:ℝ)^(2*D.eps)*
      Z^(QRH.C (QRH.theta+gap)-saving-
        ((1-QRH.ly)*a+(4/25)*QRH.lx-33/50+(16-6*QRH.ly)*D.e)) := by
  obtain ⟨J,hclass⟩ := actual_uniform_cube_class_bound S nslots lengths hpos hinj hsum hsmall hmin hbeta hfine
  refine ⟨J,?_⟩
  intro n τ logCost heightCost loss ν ζ μ saving hτ hτd hτcost hl hh hloss hν hζ hμ hsaving hcount hbudget
  intro η
  obtain ⟨C,hC,hclass⟩ := hclass n τ logCost heightCost loss hτ hτd hτcost hl hh hloss η
  let cardCost:ℝ:=(HeckeDetectorClassBudget.alphabetBound D.t:ℝ)^nslots
  have hcardCost:0≤cardCost:=by dsimp [cardCost];positivity
  refine ⟨(cardCost+1)*C,by positivity,?_⟩
  filter_upwards [hclass] with Z hc
  refine ⟨hc.1,?_⟩
  intro gap hgap hgap1 hκbeta d hd hd1 v a i hi hv hv' hv1 hdv ha ha1 rows hne hrows hnorm
    hnext hcurrent t ht hheight Y T hT
  have hZ:0<Z:=zero_lt_one.trans hc.1
  have hd0:0<d:=by linarith
  let z:ℂ:=(17/50:ℂ)+t.1.2*Complex.I
  let Q:=HeckeDetectorPhysicalSelection.physical S.modulus ⊤ (fun u:FreeRow=>u.val)
    (fun _ x=>(S.w x:ℂ)) (fun _=>2) (fun j=>lengths j/d) (fun _=>z) (Z^d)
  let bound:ℝ:=C*(η.modulus.absNorm:ℝ)^(2*D.eps)*
    Z^(QRH.C (QRH.theta+gap)-saving-
      ((1-QRH.ly)*a+(4/25)*QRH.lx-33/50+(16-6*QRH.ly)*D.e))
  have hb:0≤bound:=by dsimp [bound];positivity
  have hpart:=cubeArithmeticSum_class_uniform S.S S.exclusions S.maximal η rows T hT
    (fun _ x=>(S.w x:ℂ)) Y a D.e t Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (by linarith) (fun j=>lengths j/d) Q bound hb (by
      intro bin hne'
      have hp:=hc.2 gap hgap hgap1 hκbeta d hd hd1 v a ν i hi hv ha ha1 hν rows hne
        hrows hnorm hnext hcurrent t ht hheight bin hne'
      dsimp only at hp
      let q:=classMean Finset.univ ((2*a-1)/2) D.t (fun j=>lengths j/d) bin
      have hqb:=classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
        (fun j=>lengths j/d) Q bin (by linarith) (fun j _=>div_nonneg (hpos j).le hd0.le)
        (by rw [←Finset.sum_div,hsum];exact div_pos (by norm_num [QRH.ell,QRH.theta]) hd0) hne'
      have hs:=QRHProbeCentralExponent.adaptive_mixed_saving nslots a q gap D.ε D.t D.t ν ζ μ v d
        D.e D.eps loss D.t (logCost+heightCost+heightCost*(J:ℝ)) saving
        (by linarith) ha1 hqb.1 hqb.2 hgap hgap1 D.epsilon_pos.le D.t_pos.le D.t_pos.le hν.le
        hcount hζ hv' hv1 hμ hdv D.e_pos.le D.eps_pos.le hbudget
      have hid:=QRHProbeCentralExponent.central_class_exponent_identity nslots a v d
        (QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap D.ε D.t D.t ν) q D.e D.eps loss D.t
        (logCost+heightCost+heightCost*(J:ℝ))
      apply hp.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hc.1.le
      linarith)
  simp only [Finset.card_univ,Fintype.card_fin] at hpart
  calc
    _≤cardCost*bound:=hpart
    _≤(cardCost+1)*bound:=mul_le_mul_of_nonneg_right (by linarith) hb
    _=_:=by dsimp [bound];ring

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
