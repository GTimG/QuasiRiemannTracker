import QRH.Detector.UniformAllMoments
import QRH.Hecke.DynamicCountFromMoments

/-! Actual short/long detector fiber count with all four analytic moment fields
proved, original source objects and arbitrary independent positive distinct slots.
No raw-moment or energy certificate is an input. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHUniformDetectorMoment
open HeckeFamily ProbeFinalAssembly HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily QRHDynamicMomentInput

theorem actual_uniform_detector_fiber_count {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)(hinj:Function.Injective lengths)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,lengths j≤dynamicMesh D.t/200):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀gap:ℝ,0≤gap→gap≤(1-QRH.kappa0)/2→
      2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*gap→
    ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T allowance ν:ℝ)(i:ℕ),
      51/100<a→2*a-1≤5/6→1≤tstar→tstar≤3/2→0<ν→
    ∀B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin nslots)
      (Z^d) a D.ε tstar T allowance i,B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>lengths s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→(∀s,|(B.external s).im|≤height)→
      2*Real.pi*allowance+(3*i:ℕ)*T≤height→
    let F:=B.fiber bin label left right hne;
      (F.rows.card:ℝ)≤C*(1+height)^J*(Z^d)^(
        max (QRHDetectorRowCount.shortExponent (2*a-1) (F.q/(2*a-1)) tstar)
          (QRHDetectorRowCount.longExponent (2*a-1) tstar)+
          (30/169)*gap+159*D.ε+D.t+F.mesh+7*ν) := by
  obtain ⟨c,k,K,hc,hc1,hk,hK,hcount⟩ := QRHDetectorCountFromMoments.count_from_raw_moments
    S.modulus ⊤ le_top S.S S.w S.smooth S.compact S.positive_support (fun y=>(S.bounded y).1) S.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) S.support (fun y=>(S.bounded y).2) D.t D.t_pos
  obtain ⟨J,hmoment⟩ := actual_uniform_four_moment_fields S nslots lengths hpos hinj
    c k 1 1 hc hk (by norm_num) (by norm_num) hbeta hfine
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hcount
  refine ⟨J+1,?_⟩
  intro η
  obtain ⟨C,hC,hmoment⟩ := hmoment η
  refine ⟨192*C*max 1 K,by positivity,?_⟩
  filter_upwards [hmoment,HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
    with Z hm hthreshold
  refine ⟨hm.1,?_⟩
  intro gap hgap hgap1 hκbeta rows hrows d hd a tstar T allowance ν i ha haδ ht ht1 hν
    B hB hdata hprof hwidth hupper hreal bin label left right hne height hh hexternal hf F
  have hκ : (13/18:ℝ)≤QRH.kappa0+2*gap := by
    have hk0 : (13/18:ℝ)≤QRH.kappa0 := by norm_num [QRH.kappa0,QRH.theta]
    linarith
  have hfields := hm.2 (QRH.kappa0+2*gap) hκ hκbeta rows hrows d hd a tstar T allowance i B
    hB hdata hprof hwidth hupper hreal bin label left right hne height hh hexternal
  have he : (QRH.kappa0+2*gap-3/4)/2=gap+(QRH.kappa0-3/4)/2 := by ring
  simp only [he,if_pos haδ] at hfields
  have hU : 1<Z^d := Real.one_lt_rpow hm.1 (by linarith)
  have hb := hU₀ (Z^d) (hthreshold d hd) a D.ε tstar T allowance gap ν (C*(1+height)^J) height i
    hU ha haδ D.epsilon_pos.le D.epsilon_small ht ht1 hgap hgap1 hν (by positivity) hh hf F hfields
  convert hb using 1
  unfold fiberConstant
  rw [pow_succ]
  ring

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
