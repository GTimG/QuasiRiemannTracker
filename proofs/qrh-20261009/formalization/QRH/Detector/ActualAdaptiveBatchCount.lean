import QRH.Detector.UniformAllMoments
import QRH.PrimeRows.DynamicSourceCount

/-! Actual adaptive detector batch count. All four moment fields are discharged
by the analytic theorems, uniformly in the capacity and external height. -/
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHUniformDetectorMoment
open HeckeFamily ProbeFinalAssembly HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily QRHDynamicMomentInput
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst

theorem actual_uniform_adaptive_batch_count {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)(hinj:Function.Injective lengths)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,lengths j≤dynamicMesh D.t/200):
    ∃J:ℕ,∃K:ℝ,0≤K ∧ ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀gap:ℝ,0≤gap→gap≤(1-QRH.kappa0)/2→
      2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*gap→
    ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤d→∀(a T allowance ν q:ℝ)(i:ℕ),
      51/100<a→a≤1→0<ν→
    ∀B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin nslots)
      (Z^d) a D.ε (QRHAdaptiveCutoff.cutoff (2*a-1) q) T allowance i,
    B.rows⊆rows→B.rows.Nonempty→
    (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
      (HeckeDetectorPhysicalSelection.physical S.modulus ⊤ (fun u:FreeRow=>u.val)
        B.profile B.upper B.widths B.external (Z^d)) u=q)→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>lengths s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀height:ℝ,0≤height→(∀s,|(B.external s).im|≤height)→
      2*Real.pi*allowance+(3*i:ℕ)*T≤height→
    (B.rows.card:ℝ)≤(Fintype.card (Sum Bool (RayQuotient.Characters S.modulus ⊤)):ℝ)*
      (dyadicLength (Z^d):ℝ)^2*fiberConstant (C*(1+height)^J) height K*
      (Fintype.card B.Bin:ℝ)*(Z^d)^
      (QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap D.ε D.t B.mesh ν) := by
  obtain ⟨cB,kB,KB,hcB,hcB1,hkB,hKB,hbalanced⟩ :=
    QRHProbeHighRowFamily.balanced_adaptive_count_from_raw_moments
      S.modulus ⊤ le_top S.S S.w S.smooth S.compact S.positive_support (fun y=>(S.bounded y).1) S.nonzero
      1 2 1 (by norm_num) (by norm_num) (by norm_num) S.support (fun y=>(S.bounded y).2) D.t D.t_pos
  obtain ⟨cH,kH,KH,hcH,hcH1,hkH,hKH,hhigh⟩ :=
    QRHProbeHighRowFamily.high_adaptive_count_from_raw_moments
      S.modulus ⊤ le_top S.S S.w S.smooth S.compact S.positive_support (fun y=>(S.bounded y).1) S.nonzero
      1 2 1 (by norm_num) (by norm_num) (by norm_num) S.support (fun y=>(S.bounded y).2) D.t D.t_pos
  obtain ⟨J,hmoment⟩ := actual_uniform_four_moment_fields S nslots lengths hpos hinj
    cB kB cH kH hcB hkB hcH hkH hbeta hfine
  refine ⟨J,max KB KH,le_trans hKB (le_max_left _ _),?_⟩
  intro η
  obtain ⟨C,hC,hmoment⟩ := hmoment η
  refine ⟨C,hC,?_⟩
  filter_upwards [hmoment,
    eventually_all_rpow_ge hbalanced (1/200) (by norm_num),
    eventually_all_rpow_ge hhigh (1/200) (by norm_num)] with Z hm hb hh
  refine ⟨hm.1,?_⟩
  intro gap hgap hgap1 hκbeta rows hrows d hd a T allowance ν q i ha ha1 hν
    B hB hne hq hdata hprof hwidth hupper hreal height hheight hexternal hf
  have hκ : (13/18:ℝ)≤QRH.kappa0+2*gap := by
    have hk0 : (13/18:ℝ)≤QRH.kappa0 := by norm_num [QRH.kappa0,QRH.theta]
    linarith
  have hfields := fun bin label left right hne =>
    hm.2 (QRH.kappa0+2*gap) hκ hκbeta rows hrows d hd a _ T allowance i B
      hB hdata hprof hwidth hupper hreal bin label left right hne height hheight hexternal
  have he : (QRH.kappa0+2*gap-3/4)/2=gap+(QRH.kappa0-3/4)/2 := by ring
  simp only [he] at hfields
  have hU : 1<Z^d := Real.one_lt_rpow hm.1 (by linarith)
  by_cases hδ : 2*a-1≤5/6
  · simp only [if_pos hδ] at hfields
    have hc := hb d hd a D.ε T allowance gap ν (C*(1+height)^J) height q i
      hU ha hδ D.epsilon_pos.le D.epsilon_small hgap hgap1 hν (by positivity) hheight hf B hne hq hfields
    simp only [QRHProbeHighRowFamily.adaptiveRowExponent,if_pos hδ]
    simp only [Fintype.card_eq_nat_card] at hc ⊢
    apply hc.trans
    have hfc : fiberConstant (C*(1+height)^J) height KB ≤
        fiberConstant (C*(1+height)^J) height (max KB KH) := by
      unfold fiberConstant
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact max_le_max_left 1 (le_max_left KB KH)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left hfc (by positivity)
  · simp only [if_neg hδ] at hfields
    have hc := hh d hd a D.ε T allowance gap (C*(1+height)^J) height q i
      hU (lt_of_not_ge hδ) ha1 D.epsilon_pos.le D.epsilon_small (by positivity) hheight hf B hfields
    simp only [QRHProbeHighRowFamily.adaptiveRowExponent,if_neg hδ]
    simp only [Fintype.card_eq_nat_card] at hc ⊢
    apply hc.trans
    have hfc : fiberConstant (C*(1+height)^J) height KH ≤
        fiberConstant (C*(1+height)^J) height (max KB KH) := by
      unfold fiberConstant
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact max_le_max_left 1 (le_max_right KB KH)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left hfc (by positivity)

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
