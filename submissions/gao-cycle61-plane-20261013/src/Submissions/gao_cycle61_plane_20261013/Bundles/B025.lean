/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B000
import Submissions.gao_cycle61_plane_20261013.Bundles.B024
import Mathlib.Tactic.Ring
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGramScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Dirichlet
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalIdentity

/- BEGIN ORIGINAL Cycle61.Assembly.Final.Height; sha256 53325e57d2bcaf07c29834acf600311e696e4c1cd30c35d433a7baa5434efdf0 -/
section
                                        
                                          

set_option autoImplicit false
namespace Cycle61.FinalAssembly
noncomputable section
open scoped Classical
open Filter
open OAI.SevenEighths Cycle61DetectorCount HeckeFamily

def HeightAdmissible (D : BaselineData) (P : TransportParameters D) (J τ : ℝ) : Prop :=
  0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧ 2*τ≤D.t ∧
    τ*(2+4*P.eps)<D.t ∧ 2*τ*(1+J)≤D.t

theorem choose_height (D : BaselineData) (P : TransportParameters D)
    (J : ℝ) (hJ : 0≤J) : ∃τ : ℝ,HeightAdmissible D P J τ := by
  have ht:=D.t_pos
  have hcost:=D.cost_pos
  have heps:=P.eps_pos
  let τ : ℝ := min ((1/200:ℝ)*D.cost/16)
    (min (1/800) (min (D.t/(8*(J+1))) (D.t/(4*(2+4*P.eps)))))
  have hp : 0<τ := lt_min (by positivity)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hc : τ≤(1/200:ℝ)*D.cost/16 := min_le_left _ _
  have hd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hj : τ≤D.t/(8*(J+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he : τ≤D.t/(4*(2+4*P.eps)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hjm : τ*(8*(J+1))≤D.t := (le_div_iff₀ (by positivity)).mp hj
  have hem : τ*(4*(2+4*P.eps))≤D.t := (le_div_iff₀ (by positivity)).mp he
  refine ⟨τ,hp,by linarith,by linarith,?_,by nlinarith,by nlinarith⟩
  nlinarith [mul_nonneg hp.le hJ]

/-- The common height follows every fixed polynomial degree. -/
theorem height_admissible_mono {D : BaselineData} {P : TransportParameters D}
    {J J' τ : ℝ} (h : HeightAdmissible D P J τ) (hle : J'≤J) :
    HeightAdmissible D P J' τ := by
  rcases h with ⟨ht,hd,hc,hs,he,hJ⟩
  exact ⟨ht,hd,hc,hs,he,(mul_le_mul_of_nonneg_left (by linarith : 1+J'≤1+J)
    (by linarith : 0≤2*τ)).trans hJ⟩

/-- The same height absorbs a genuine count degree and any fixed source degree. -/
theorem actual_joint_height (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D)
    (counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200)
    (Jw : ℝ) (hJw : 0≤Jw) :
    ∃τ : ℝ,HeightAdmissible D P Jw τ ∧
      ∀η : Character,∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound D.toData (baselineSource D F) counts η Z τ
          (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩ := actual_baseline_source_moments D F counts hβ hκβ hfine
  obtain ⟨τ,hheight⟩ := choose_height D P (J+Jw) (by positivity)
  have hw : HeightAdmissible D P Jw τ := height_admissible_mono hheight (by linarith)
  have hc : HeightAdmissible D P J τ := height_admissible_mono hheight (by linarith)
  refine ⟨τ,hw,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨max 1 (C*2^J),le_max_left _ _,?_⟩
  filter_upwards [hbound τ hc.1 (by linarith [hc.2.1]),eventually_ge_atTop (1:ℝ)] with Z hm hZ
  apply hm.mono_constant (by linarith)
  apply (ProbeFinalAssembly.polynomial_height_absorption C Z τ J D.t hC.le hZ hc.1.le hJ
    (by linarith [hc.2.2.2.2.2])).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
end
end Cycle61.FinalAssembly

end
/- END ORIGINAL Cycle61.Assembly.Final.Height -/

/- BEGIN ORIGINAL Cycle25.Assembly.Continuation; sha256 225fc957beb9ef7a221c8acd7a940fe97260969b7d40aba0c40af3a88e16cdfc -/
section
                                                       
                                                          
                                                  

/-!
The continuation and actual L-function transfer for a variable boundary.
These are infrastructure lemmas: their probe hypotheses must be discharged
by the physical estimates before they yield a new zero-free theorem.
-/

noncomputable section
open Filter Asymptotics
open scoped Classical
open OAI.SevenEighths

namespace Cycle25

def continuationMargin (θ β ω σ : ℝ) : ℝ := min (β - θ - ω) σ

theorem continuationMargin_pos {θ β ω σ : ℝ}
    (hω : ω < β - θ) (hσ : 0 < σ) :
    0 < continuationMargin θ β ω σ :=
  lt_min (sub_pos.mpr hω) hσ

theorem continuation_boundary_gt {θ β ω σ : ℝ} (hω : 0 < ω) :
    θ < β - continuationMargin θ β ω σ := by
  have h : continuationMargin θ β ω σ ≤ β - θ - ω := min_le_left _ _
  linarith

theorem max_signal_exponents (θ β ω σ c : ℝ) :
    max (θ + c + ω) (β + c - σ) =
      (β - continuationMargin θ β ω σ) + c := by
  unfold continuationMargin
  rcases le_total (β - θ - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

theorem nonzero_of_probe_bounds (χ : HeckeFamily.Character)
    (H : ℂ → ℂ) (J : ℝ → ℂ) (θ β ω σ c : ℝ)
    (hθ0 : 0 < θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (hβ : β ≤ 1) (hω0 : 0 < ω) (hω : ω < β - θ) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | θ < s.re})
    (hb : ∀ s : ℂ, θ < s.re → ‖H s - 1‖ ≤ 1/2)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (θ+c+ω)))
    (herror : (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
      (fun x : ℝ => x ^ (β+c-σ)))
    {ρ : ℂ} (hρ : β - continuationMargin θ β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : HeckeFamily.LFunction χ ρ ≠ 0 := by
  let a := β - continuationMargin θ β ω σ
  have hθa : θ < a := continuation_boundary_gt hω0
  have ha2 : a < 2 := by
    have hp := continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have hH7 : AnalyticOnNhd ℂ H {s : ℂ | (7/8 : ℝ) < s.re} :=
    hH.mono (fun _ hs => hθ7.trans_lt hs)
  have hb7 : ∀ s : ℂ, (7/8 : ℝ) < s.re → ‖H s - 1‖ ≤ 1/2 :=
    fun s hs => hb s (hθ7.trans_lt hs)
  have htop : HeckeSignal.signal χ H c =O[atTop]
      (fun x : ℝ => x ^ (a+c)) := by
    simpa only [max_signal_exponents, a] using
      Continuation.common_signal_bound J (HeckeSignal.signal χ H c)
        (θ+c+ω) (β+c-σ) hJ herror
  have hHa : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH.mono (fun _ hs => hθa.trans hs)
  apply Continuation.nonzero_of_regularized_signal a 1 c
    (HeckeFamily.LFunction χ) (HeckeSignal.regularL χ)
    (HeckeSignal.targetRegularizer χ) (Continuation.gaussianMultiplier H)
    (HeckeSignal.signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
    (Continuation.gaussianMultiplier_analytic hHa)
    (HeckeSignal.signal_locallyIntegrable χ H hH7.differentiableOn hb7 c)
    htop (HeckeSignal.signal_rapidDecayAtZero χ H hH7.differentiableOn hb7 c)
    ?_ hρ ?_ (HeckeSignal.targetRegularizer_ne_zero χ hpole)
    (Continuation.gaussianMultiplier_ne_zero (hb ρ (hθa.trans hρ)))
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
      HeckeSignal.signalMellin_eq_amplitude χ H hH7.differentiableOn hb7
        c a ha2 htop hs]
    unfold HeckeSignal.amplitude HeckeSignal.quotient Continuation.gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := HeckeFamily.LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply HeckeSignal.regularL_eq χ _ hpole
    intro h
    rw [h] at hρ
    norm_num at hρ
    linarith

def PrimitiveProbeContract (θ c ω σ : ℝ) : Prop :=
  ∀ η : HeckeFamily.Character,
    FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : HeckeFamily.Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, HeckeFamily.idealCoeff χ I =
        if IsCoprime I χ.modulus then HeckeFamily.idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | θ < s.re} ∧
      (∀ s : ℂ, θ < s.re → ‖H s - 1‖ ≤ 1/2) ∧
      J =O[atTop] (fun x : ℝ => x ^ (θ+c+ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
        (fun x : ℝ => x ^ (HeckeZeroSupremum.beta+c-σ))

def UniformCommonProbe (θ c : ℝ) : Prop :=
  θ < HeckeZeroSupremum.beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < HeckeZeroSupremum.beta - θ ∧ 0 < σ ∧
      PrimitiveProbeContract θ c ω σ

theorem beta_le_of_common_probe {θ c : ℝ}
    (hθ : (1/2 : ℝ) ≤ θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (h : UniformCommonProbe θ c) : HeckeZeroSupremum.beta ≤ θ := by
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := h (lt_of_not_ge hn)
  have hmargin := continuationMargin_pos hω hσ
  have hboundary := continuation_boundary_gt
    (θ := θ) (β := HeckeZeroSupremum.beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc => hη
        ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : HeckeFamily.LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith) hχpole, hz, zero_mul]
  exact (nonzero_of_probe_bounds χ H J θ HeckeZeroSupremum.beta ω σ c
    (by linarith) hθ7 HeckeZeroSupremum.beta_le_one hω0 hω hσ
    hH hb hJ herr hnear hχpole) hzχ

theorem hecke_ne_zero_of_common_probe {θ c : ℝ}
    (hθ : (1/2 : ℝ) ≤ θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (h : UniformCommonProbe θ c) (χ : HeckeFamily.Character) (s : ℂ)
    (hs : θ < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_of_common_probe hθ hθ7 h).trans_lt hs) hpole

theorem dirichlet_of_hecke {θ : ℝ} (hθ : 0 < θ)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), θ < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : θ < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  have h := hH (HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_of_hecke {θ : ℝ} (hθ : 0 < θ)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), θ < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    (s : ℂ) (hs : θ < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_of_hecke hθ hH (1 : DirichletCharacter ℂ 1) s hs
    (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end Cycle25

/- Adapted unchanged from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Assembly.Continuation -/

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Geometry; sha256 5e094448ae1479677472fa95d097c7aad14f460bf6d2f0e72a04e398c1c79da1 -/
section
                                
                          

set_option autoImplicit false

/-! Exact low-probe geometry. All lengths refer to Cycle61, including the total ray length. -/
namespace Cycle61.Assembly.LowGeometry
noncomputable section
open Cycle61.Arithmetic

theorem x_pos : 0 < x := by linarith [ell_pos, ell_lt_x]
theorem b_pos : 0 < y-x := by linarith [x_lt_y]
theorem signal_pos : 0 < signal theta := by
  rw [signal_at_boundary]
  linarith [x_pos, b_pos]
theorem scale_square : (2*x-y)+y=2*x := by ring
theorem gram_power (δ : ℝ) :
    x+(y-x)*(1/6)+y*δ = 2*signal theta+y*δ := by
  rw [signal_at_boundary]
  ring
theorem gram_sqrt_power (δ : ℝ) :
    (2*signal theta+y*δ)*(1/2) = signal theta+(y/2)*δ := by ring
theorem dilation_gap : 0 < 2*x-y-ell := by
  rw [show 2*x-y-ell = -(y-2*x+ell) by ring, marked_short_margin]
  norm_num
theorem dilation_le_y : 2*x-y ≤ y := by linarith [x_lt_y]
theorem tuple_margin_neg : 1+3*ell-2*(x+y) < 0 := by
  rw [marked_tuple_margin]
  norm_num
end
end Cycle61.Assembly.LowGeometry

end
/- END ORIGINAL Cycle61.Assembly.Low.Geometry -/

/- BEGIN ORIGINAL Cycle61.Assembly.Low.Detector.LowGramScale; sha256 c2e8d1c4c9a2ad693f0b843e7262a4d12fc4b920ee337b8ea50c1ee7d746f529 -/
section
                                    
                                                        

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGramScale.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace OAI

noncomputable section
namespace SevenEighths.Cycle61ProbeLow
open ProbePhysical

lemma compensated_gram_ratio (q X Y L : ℝ) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hL : 0<L) :
    (Y/L)^2/(q*(X/L)*(Y/L))=Y/(q*X) := by
  field_simp

lemma compensated_gram_scale_bound (q X Y L δ : ℝ)
    (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hL : 1≤L) (hδ : 0≤δ)
    (hP : q*X≤Y) (htail : L*Y≤q^2*X^2) :
    (q*(X/L)*(Y/L)/(Y/L))*
      (1+((Y/L)^2/(q*(X/L)*(Y/L)))^(1/6:ℝ)+
        ((Y/L)^2/(q*(X/L)*(Y/L)))^2/(Y/L))*(Y/L)^δ ≤
      3*(q*X/L)*(Y/(q*X))^(1/6:ℝ)*Y^δ := by
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hp : 1≤Y/(q*X) := (le_div_iff₀ (mul_pos hq hX)).mpr (by simpa using hP)
  have hr : 1≤(Y/(q*X))^(1/6:ℝ) := Real.one_le_rpow hp (by norm_num)
  have ht : (Y/(q*X))^2/(Y/L)≤1 := by
    have he : (Y/(q*X))^2/(Y/L)=L*Y/(q^2*X^2) := by field_simp
    rw [he]
    exact (div_le_one (by positivity)).mpr htail
  have hys : (Y/L)^δ≤Y^δ := Real.rpow_le_rpow (by positivity)
    ((div_le_self hY.le hL)) hδ
  rw [compensated_gram_ratio q X Y L hq hX hY hl]
  have he : q*(X/L)*(Y/L)/(Y/L)=q*X/L := by field_simp
  rw [he]
  calc
    _≤(q*X/L)*(3*(Y/(q*X))^(1/6:ℝ))*Y^δ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hys
        (by positivity) (by positivity)
    _=_ := by ring

lemma source_gram_power (Z δ : ℝ) (hZ : 0<Z) :
    Z^(Cycle61.Arithmetic.x:ℝ)*(Z^((Cycle61.Arithmetic.y-Cycle61.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Cycle61.Arithmetic.y:ℝ))^δ=
      Z^((2*Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+(Cycle61.Arithmetic.y)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  exact Cycle61.Assembly.LowGeometry.gram_power δ

lemma source_gram_sqrt_power (Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^((2*Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+(Cycle61.Arithmetic.y)*δ:ℝ))=Z^((Cycle61.Assembly.signal Cycle61.Arithmetic.theta)+((Cycle61.Arithmetic.y/2))*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

end SevenEighths.Cycle61ProbeLow
end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Low.Detector.LowGramScale -/
