import QRH.Detector.ActualAdaptiveBatchCount

/-! Analytic source count with dyadic, alphabet and height costs absorbed. The
height degree is chosen before the tail height and frequency parameters. -/
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHUniformDetectorMoment
open HeckeFamily ProbeFinalAssembly HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily QRHDynamicMomentInput
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst

theorem actual_uniform_adaptive_source_count {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)(hinj:Function.Injective lengths)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,lengths j≤dynamicMesh D.t/200):
    ∃J:ℕ,∀(n:ℕ)(dmax τ logCost heightCost binWidth:ℝ),
      0<dmax→0<τ→0<logCost→τ<heightCost→0<binWidth→
    ∃K:ℝ,0<K ∧ ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀gap:ℝ,0≤gap→gap≤(1-QRH.kappa0)/2→
      2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*gap→
    ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤d→d≤dmax→∀(a ν q:ℝ)(i:ℕ),i≤n→
      51/100<a→a≤1→0<ν→
    ∀B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin nslots)
      (Z^d) a D.ε (QRHAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows→B.rows.Nonempty→B.binWidth=binWidth→
    (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
      (HeckeDetectorPhysicalSelection.physical S.modulus ⊤ (fun u:FreeRow=>u.val)
        B.profile B.upper B.widths B.external (Z^d)) u=q)→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>lengths s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    (∀s,|(B.external s).im|≤Z^heightCost)→
    (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+heightCost*(J:ℝ))*(Z^d)^
      (QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap D.ε D.t B.mesh ν) := by
  obtain ⟨J,K₀,hK₀,hcount⟩ := actual_uniform_adaptive_batch_count S nslots lengths hpos hinj hbeta hfine
  refine ⟨J,?_⟩
  intro n dmax τ logCost heightCost binWidth hdmax hτ hl hh hb
  have hheight : 0≤heightCost := (hτ.trans hh).le
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually
    (Label:=Sum Bool (RayQuotient.Characters S.modulus ⊤))
    nslots (1/200) dmax logCost heightCost (heightCost*(J:ℝ)) binWidth K₀
    (by norm_num) hdmax hl hheight hb
  refine ⟨K,hK,?_⟩
  intro η
  obtain ⟨C,hC,hcount⟩ := hcount η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hcount,hpref,source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh]
    with Z hc hpref hfreq
  refine ⟨hc.1,?_⟩
  intro gap hgap hgap1 hκbeta rows hrows d hd hdmax' a ν q i hi ha ha1 hν
    B hB hne hbin hq hdata hprof hwidth hupper hreal hexternal
  have hZ : 0<Z := zero_lt_one.trans hc.1
  have hcard := hc.2 gap hgap hgap1 hκbeta rows hrows d hd a (Z^τ) ((Z^d)^(τ/(2*dmax))) ν q i
    ha ha1 hν B hB hne hq hdata hprof hwidth hupper hreal (Z^heightCost)
    (by positivity) hexternal (hfreq d hdmax' i hi)
  have hp : 1≤Z^heightCost := Real.one_le_rpow hc.1.le hheight
  have hmoment : C*(1+Z^heightCost)^J≤(C*2^J)*Z^(heightCost*(J:ℝ)) := by
    calc
      _≤C*(2*Z^heightCost)^J := by gcongr;linarith
      _=_ := by rw [mul_pow,Real.rpow_mul_natCast hZ.le];ring
  have hslots : B.slots.card≤nslots := by
    simpa using Finset.card_le_univ (s:=B.slots)
  have hpref' := hpref d hd hdmax' (C*2^J) a D.ε _ _ _ i (by positivity) ha1 B hslots hbin
  simp only [Fintype.card_eq_nat_card] at hcard hpref'
  apply hcard.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Real.rpow_nonneg hZ.le _) _)
  apply le_trans _ hpref'
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold fiberConstant
  gcongr

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
