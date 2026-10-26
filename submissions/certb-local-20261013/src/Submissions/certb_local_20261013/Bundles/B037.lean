/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B033
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.GlobalCorrection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGramScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowReflectedLength
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersDetectorScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowCaps

/- BEGIN ORIGINAL MODULE Global.HighDataFine ; sha256 5ae4e52a1f40bc950f7ade36d52d5e2ec277fa21b08c1564b9782bbb7a60ae1f -/
section




/-! Fine high-row data for the new endpoint. The constructor works for every
positive mesh function, and its choice of t also pays the smaller row extension. -/

noncomputable section
open scoped BigOperators

namespace Submission20261012.Global.HighParameters
open OAI.SevenEighths.Parameters

theorem exists_high_data_fine (Δ:ℝ)(hΔ:0<Δ)
    (kap : ℝ) (hkaplo : 7/10 ≤ kap) (hkaphi : kap ≤ 3/4)
    (hkapbeta : 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1 ≤ kap)
    (hkapexact : kap = 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (mesh:ℝ→ℝ)
    (hmesh:∀t:ℝ,0 < t→0 < mesh t):
    ∃D:HighData Δ,∀j,D.ell j ≤ mesh D.t/200:=by
  let t := min (Δ/100000) (min (1/100000000) (Submission20261012.Global.rowExtension/3))
  have hrow : 0 < Submission20261012.Global.rowExtension := by
    norm_num [Submission20261012.Global.rowExtension, Submission20261012.Endpoint.zeta]
  have ht : 0 < t := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have htΔ : t < Δ/4 := by
    have hh : t ≤ Δ/100000 := min_le_left _ _
    linarith only [hh,hΔ]
  have htgap : t ≤ Δ/100000 := min_le_left _ _
  have ht1 : t ≤ 1/100000000 := (min_le_right _ _).trans (min_le_left _ _)
  have htrow : t ≤ Submission20261012.Global.rowExtension/3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    Submission20261012.Global.HighParameters.exists_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t (by norm_num) (by norm_num)
      (lt_min ht (hmesh t ht)) ht
  let allowance := t/((N:ℝ)+2000)
  have ha : 0 < allowance := div_pos ht (by positivity)
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0 < small := lt_min ha (div_pos ht (by positivity))
  have hsa : small ≤ allowance := min_le_left _ _
  have hst : small ≤ t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small ≤ t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0 < eps := by dsimp [eps];positivity
  have hepss : eps ≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have heN : ((N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  have het : 2000*e ≤ t := by linarith only [hea, hst0]
  have hεt : 2000*ε ≤ t := by linarith only [hεa,hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t/2 := min_le_left _ _
  have hsell : sigma ≤ ellMin/4 := min_le_right _ _
  refine ⟨{
    momentKappa:=kap,momentKappa_lo:=hkaplo,momentKappa_hi:=hkaphi,momentKappa_beta:=hkapbeta,
    momentKappa_exact:=hkapexact,
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_gap:=htgap,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,central_budget:=by
      have hell := Submission20261012.Global.ell_lt_one_fifth
      have hprod := mul_le_mul_of_nonneg_left hell.le ht.le
      nlinarith only [hεt,het,he8,ht1,htgap,hprod,ht]
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by
      change sigma+e ≤ Submission20261012.Global.theta*ellMin
      have hc := mul_le_mul_of_nonneg_right Submission20261012.Global.theta_gt_half.le hmin.le
      linarith only [hsell,heell,hmin,hc]
    floor_budget:=by
      have hprod := mul_le_mul_of_nonneg_left Submission20261012.Global.ell_lt_one_fifth.le ht.le
      linarith only [hst2,het,he8,ht1,hprod]
    high_saving:=by linarith only [hst2,htgap,ht]
    weighted_top:=by linarith only [htrow]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    change ell j ≤ mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring

theorem fine_slot_widths {Δ:ℝ}(D:HighData Δ)(mesh:ℝ→ℝ)
    (hmesh:0 < mesh D.t)(hfine:∀j,D.ell j ≤ mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ) ≤ d)(j:Fin D.N):
    0 < D.ell j/d ∧ D.ell j/d ≤ mesh D.t:=by
  have hd0:0 < d:=by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  have hh:=hfine j
  nlinarith

end Submission20261012.Global.HighParameters

end


/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

#print axioms Submission20261012.Global.HighParameters.exists_high_data_fine
#print axioms Submission20261012.Global.HighParameters.fine_slot_widths
end
/- END ORIGINAL MODULE Global.HighDataFine -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowGramScale ; sha256 6460e49c95d6dc446a668dc545a7634d4a59d438d96909ef63972d99d6fce7b7 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGramScale.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
namespace LowProbe
open ProbePhysical

lemma compensated_gram_ratio (q X Y L : ℝ) (hq : 0< q) (hX : 0< X) (hY : 0< Y) (hL : 0< L) :
    (Y/L)^2/(q*(X/L)*(Y/L))=Y/(q*X) := by
  field_simp

lemma compensated_gram_scale_bound (q X Y L δ : ℝ)
    (hq : 0< q) (hX : 0< X) (hY : 0< Y) (hL : 1≤ L) (hδ : 0≤δ)
    (hP : q*X≤ Y) (htail : L*Y≤ q^2*X^2) :
    (q*(X/L)*(Y/L)/(Y/L))*
      (1+((Y/L)^2/(q*(X/L)*(Y/L)))^(1/6:ℝ)+
        ((Y/L)^2/(q*(X/L)*(Y/L)))^2/(Y/L))*(Y/L)^δ ≤
      3*(q*X/L)*(Y/(q*X))^(1/6:ℝ)*Y^δ := by
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  have hp : 1≤ Y/(q*X) := (le_div_iff₀ (mul_pos hq hX)).mpr (by simpa using hP)
  have hr : 1≤(Y/(q*X))^(1/6:ℝ) := Real.one_le_rpow hp (by norm_num)
  have ht : (Y/(q*X))^2/(Y/L)≤1 := by
    have he : (Y/(q*X))^2/(Y/L)=L*Y/(q^2*X^2) := by field_simp
    rw [he]
    exact (div_le_one (by positivity)).mpr htail
  have hys : (Y/L)^δ≤ Y^δ := Real.rpow_le_rpow (by positivity)
    ((div_le_self hY.le hL)) hδ
  rw [compensated_gram_ratio q X Y L hq hX hY hl]
  have he : q*(X/L)*(Y/L)/(Y/L)=q*X/L := by field_simp
  rw [he]
  calc
    _≤(q*X/L)*(3*(Y/(q*X))^(1/6:ℝ))*Y^δ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hys
        (by positivity) (by positivity)
    _=_ := by ring

lemma source_gram_power (Z δ : ℝ) (hZ : 0< Z) :
    Z^(Submission20261012.Global.lx:ℝ)*(Z^(Submission20261012.Global.b:ℝ))^(1/6:ℝ)*(Z^(Submission20261012.Global.ly:ℝ))^δ=
      Z^((2*Submission20261012.Global.signal Submission20261012.Global.theta)+(Submission20261012.Global.ly)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  exact Submission20261012.Global.LowGeometry.gram_power δ

lemma source_gram_sqrt_power (Z δ : ℝ) (hZ : 0< Z) :
    Real.sqrt (Z^((2*Submission20261012.Global.signal Submission20261012.Global.theta)+(Submission20261012.Global.ly)*δ:ℝ))=Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+((Submission20261012.Global.ly/2))*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowGramScale -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowReflectedLength ; sha256 8ff29d1e1f4eda262e4f8dfb91ac5fc362063b60e5761da64adb3ebf1b96ad54 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowReflectedLength.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflected
open ProbeLowReflected
open InverseTerminalWidths

theorem compensated_reflected_exponent_with_length (d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0≤ d) (_hd1 : d≤ Submission20261012.Global.ell) (hε : 0≤ε)
    (hO : -ε≤ O₀) (hH : H≤((1-Submission20261012.Global.ell)-2*d)-O₀+ε)
    (hA : 2*A₀≤ O₀+ε) (hN : 0≤ N₀) (hNA : N₀≤ A₀)
    (hS : 0≤ S₀) (hB : 0≤ B₀) (hell : ell₀≤ Submission20261012.Global.ell-d+ε) (hz : za≤ ell₀+ε)
    (hv : -ε≤ v) (hl : -ε≤ ell) (he : -ε≤ el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀)≤(1-Submission20261012.Global.ell)-d+40*ε := by
  let Td := 2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀
  have hθlo : -ε≤θ := (abs_le.mp hθ).1
  have hθhi : θ≤ε := (abs_le.mp hθ).2
  have hTd : Td≤ H-3*d+6*ε := by dsimp [Td];linarith
  have hcol : v+ell≤ H+10*ε := by dsimp [Td] at hTd;linarith
  have hmax : max H (v+ell)≤ H+10*ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  by_cases hu : hybridSaving v za=za
  · unfold reflectedExponent
    rw [hu]
    change O₀/2+max H (v+ell)-S₀-B₀+za-za-ell-2*el/3-max 0 (Td-v-3*ell-el)/2≤_
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*ε/12≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el)=Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td≤
        O₀/2+H-S₀-B₀+za-Td/4+(10+17/12)*ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td≤_
    apply hbound.trans
    dsimp [Td]
    linarith [Submission20261012.Global.ell_lt_one_fifth]

end LowReflected

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowReflectedLength -/

/- BEGIN ORIGINAL MODULE Global.Low.Normalizer ; sha256 503fb1d4caa660d17d4eb16b96c9a812f922b25b7aad5da5911da6acca427264 -/
section



/-! Adapted from OpenAI/math family003, pinned original module PrimeRows.CubeNormalizer.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace LowNormalizer
open ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0< c) (hcb : c≤ b)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤ W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
          (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤ C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=> Z^(ell j))) Z (Submission20261012.Global.ell) hZ (fun j _=> hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
        (slotMass (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=> Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end LowNormalizer

end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Normalizer -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowCaps ; sha256 ca05c8cb6f97d5df3421438f762fd466417191ccc2e3f4fc0669acea6c3a6912 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowCaps.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma low_actual_scale_caps (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀))
    (Z Ck d ell0 shift η QK QP : ℝ) (hZ : 2≤ Z) (hCkp : 0< Ck) (hCk : Ck≤ Z)
    (hQn : (Ideal.absNorm Q:ℝ)≤ Z) (hd : 0≤ d) (hell : 0≤ ell0)
    (hellcap : ell0≤ Submission20261012.Global.ell-d+η) (hshift : |shift|≤η) (hη : η≤1)
    (hIn : (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d))
    (hK : QK≤2*Ck*Z^((1-Submission20261012.Global.ell)-2*d)) (hP : QP/2≤ Z^ell0) :
    (Ideal.absNorm I:ℝ)≤ Z^2 ∧
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b):ℝ)≤ Z^(8:ℝ) ∧
      QK≤ Z^(8:ℝ) ∧ QP≤ Z^(8:ℝ) ∧ (Z^(1+ell0+shift))⁻¹≤ Z^(8:ℝ) := by
  have hgeom := Submission20261012.Global.ell_interval
  have hz : 0< Z := by linarith
  have hz1 : 1≤ Z := by linarith
  have hcp : Ck*Z^((1-Submission20261012.Global.ell)-2*d)≤ Z^2 := by
    calc
      _ ≤ Z*Z^((1-Submission20261012.Global.ell)-2*d) := mul_le_mul_of_nonneg_right hCk (Real.rpow_nonneg hz.le _)
      _ = Z^(1+((1-Submission20261012.Global.ell)-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := by
        rw [←Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num; linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth])
  have hi := hIn.trans hcp
  refine ⟨hi,?_,?_,?_,?_⟩
  · calc
      _ ≤ (Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := original_pool_restricted_norm J I Q Q₀ hJ hI hQ hpower hmask A
      _ ≤ Z^2*Z := mul_le_mul hi hQn (Nat.cast_nonneg _) (sq_nonneg _)
      _ = Z^(3:ℝ) := by norm_num;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  · calc
      QK ≤ 2*(Ck*Z^((1-Submission20261012.Global.ell)-2*d)) := by linarith
      _ ≤ Z*Z^2 := mul_le_mul hZ hcp (by positivity) hz.le
      _ = Z^(3:ℝ) := by norm_num;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  · calc
      QP ≤ 2*Z^ell0 := by linarith
      _ ≤ Z*Z^ell0 := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+ell0) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num; linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth])
  · rw [←Real.rpow_neg hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1 (by have hs := (abs_le.mp hshift).1;linarith)

lemma low_reflection_parameters (η : ℝ) (hη : 0<η) :
    0<η/(200*(1+η)) ∧
    η/(200*(1+η))*(8+8+2*(η/2+57+η))+η/2≤2*η := by
  have hp : 0<200*(1+η) := by positivity
  constructor
  · positivity
  · apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    nlinarith [sq_nonneg η]
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowCaps -/

/- BEGIN ORIGINAL MODULE Global.Low.RegionalCorrection ; sha256 e40d7f139561d776ad6ff617516bcf4d43053f0fd389162aad5844b4597f9bf9 -/
section



/-!
Extension of the original OpenAI local Euler estimates to the narrower
w,z region and the improved x boundary. Proof structure follows
Detector/GlobalRegion.lean, GlobalHolomorphic.lean and GlobalCorrection.lean.
The local factors and the global infinite product are the original objects.
-/

noncomputable section
namespace Submission20261012.Global.LowCorrection
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeEuler OAI.SevenEighths.ProbePhysical

theorem weighted_unramified_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : theta ≤ x.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hθ := Submission20261012.Global.LowGeometry.theta_coarse
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(99/100:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(223/100:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(19/20:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-theta) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(82/100:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num <;> linarith))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num <;> linarith))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num <;> linarith))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(19/20:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num <;> linarith))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num <;> linarith)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num <;> linarith)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num <;> linarith)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num <;> linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num <;> linarith)
      _ = _ := by ring
  nlinarith

lemma weighted_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : theta≤ x.re) (hz : 33/200≤ z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hθ := Submission20261012.Global.LowGeometry.theta_coarse
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem weighted_unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 33/200≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedClosed Q A eta v x w z) {x : ℂ|theta< x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := weighted_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem weighted_unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : theta≤ x.re) (hz : 33/200≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedClosed Q A eta v x w z) {w : ℂ|19/20< w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := weighted_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem weighted_unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : theta≤ x.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedClosed Q A eta v x w z) {z : ℂ|33/200< z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := weighted_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt


local notation "Id" => Ideal ActualEisensteinCubic.O

lemma weighted_idealClosedCorrection_bound (η : HeckeFamily.Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hP : 4≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : theta≤ x.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤ globalPrimeDefectBound P := by
  apply weighted_unramified_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem weighted_globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : theta≤ x.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=> weighted_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma weighted_globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : theta≤ x.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    Multipliable (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z
  let B := fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    weighted_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem weighted_globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> globalClosedCorrection η S x w z) {x : ℂ|theta< x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply weighted_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact weighted_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem weighted_globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : theta≤ x.re) (hz : 33/200≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> globalClosedCorrection η S x w z) {w : ℂ|19/20< w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply weighted_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact weighted_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem weighted_globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : theta≤ x.re) (hw : 19/20≤ w.re) :
    AnalyticOnNhd ℂ (fun z=> globalClosedCorrection η S x w z) {z : ℂ|33/200< z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply weighted_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact weighted_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


end Submission20261012.Global.LowCorrection
end

#print axioms Submission20261012.Global.LowCorrection.weighted_globalClosedCorrection_analytic_x
#print axioms Submission20261012.Global.LowCorrection.weighted_globalClosedCorrection_bound
end
/- END ORIGINAL MODULE Global.Low.RegionalCorrection -/
