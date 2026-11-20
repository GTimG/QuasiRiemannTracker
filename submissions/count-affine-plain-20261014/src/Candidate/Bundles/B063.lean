/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B050
import Candidate.Bundles.B052
import Candidate.Bundles.B062
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength

/- BEGIN ORIGINAL Cycle25.Energy.Physical.RetainedGeometry; sha256 f6342630d58980faf523ab39a2eff5b43a784fbe0e82cdc2c6f638178d71f66b -/
section
                                           
                                              
                                                                   

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily CenteredMomentRetainedWeightedSource CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentNaturalPrimitive CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectionTailMass
open CenteredMomentReflectionRetainedLength CenteredMomentSectorLocalization

/-- All natural primitive/deletion scales obey the combined conductor bound;
no individual deletion factor is charged a second time. -/
lemma actual_dual_scale_bound (τ ψ : Character) (X B : ℝ) (hX : 0 < X)
    (hcap : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes τ ψ,P):ℝ) ≤ B*X)
    (D : (sourcePrimes τ ψ).powerset) (I : SmoothIdeal (sourcePrimes τ ψ)) :
    dualScale τ ψ X D I ≤ B := by
  have hQ : 0 < (ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact (dual_scale_bounds (sourcePrimes τ ψ) D.val (redundantSet_prime _ _)
    (Finset.mem_powerset.mp D.property) I _ X B hQ hX hcap).2

/-- A uniform logarithmic scale interval for every retained annulus and every
rowwise coefficient dilation, under only its combined-scale bound. -/
theorem eventually_retained_log_interval (C xi : ℝ) (hC : 0 < C) (hxi : 0 < xi) :
    ∀ᶠU:ℝ in atTop, 1 < U ∧ ∀(τ ψ:Character) (X m:ℝ), 0 < X →
      (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes τ ψ,P):ℝ) ≤ C*U^m*X →
      ∀a:CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes τ ψ),
      ∀hY:0 < dualScale τ ψ X a.1.1 a.1.2,
      a.2 ∈ retainedAnnuli (U^(xi/4)) (dualScale τ ψ X a.1.1 a.1.2) hY →
      Real.log (dyadicScale a.2*dualScale τ ψ X a.1.1 a.1.2) ∈
        Set.Icc 0 ((m+xi)*Real.log U) := by
  have hc : ∀ᶠU:ℝ in atTop, 4*C ≤ U^(3*xi/4) :=
    (tendsto_rpow_atTop (by linarith:0 < 3*xi/4)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with U hc hU
  refine ⟨hU,?_⟩
  intro τ ψ X m hX hcap a hY ha
  have hz := zero_lt_one.trans hU
  have hlow := retained_scale_lower _ _ hY _ ha
  have hdual := actual_dual_scale_bound τ ψ X (C*U^m) hX hcap a.1.1 a.1.2
  have hscale : dyadicScale a.2 ≤ 4*U^(xi/4) :=
    retained_scale_le _ _ ((retainedAnnuli_mem _ _ hY _).mp ha).1
  have hupper : dyadicScale a.2*dualScale τ ψ X a.1.1 a.1.2 ≤ U^(m+xi) := by
    calc
      _ ≤ (4*U^(xi/4))*(C*U^m) :=
        mul_le_mul hscale hdual hY.le (by positivity)
      _ = (4*C)*U^(xi/4)*U^m := by ring
      _ ≤ U^(3*xi/4)*U^(xi/4)*U^m := by gcongr
      _ = U^(m+xi) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  refine ⟨Real.log_nonneg hlow,?_⟩
  calc
    _ ≤ Real.log (U^(m+xi)) := Real.log_le_log (zero_lt_one.trans_le hlow) hupper
    _ = _ := by rw [Real.log_rpow hz]

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.RetainedGeometry -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.CertifiedRetained; sha256 13e69af4aa7063e2c57915c8841716ab43e85a3d17d61ded9cf60b7183ea8068 -/
section
                                            
                                               
                                           
                                                            

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open Cycle25WeightedNumeratorReflection
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceLowWindow CenteredMomentNaturalPrimitive
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 1000000

/-- Certified fourth moment of the actual natural primitive restoration. The
original scale X, presentation τ, primitive ψ and profile may vary independently
with the row. All dependence on that choice is controlled by the combined
conductor/scale bound and the stated profile seminorm. The selected family can
also be empty, in which case the zero-slot endpoint covers lengths up to U². -/
theorem certified_actual_retained_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (epsilon Cscale xi : ℝ) (hepsilon : 0 < epsilon) (hCscale : 0 < Cscale) (hxi : 0 < xi) :
    ∃degree:ℕ, ∃H:Finset (ℕ×ℕ), ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (G:rows→𝓢(ℝ,ℂ)) (X:rows→ℝ) (m B Rcap:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 → 0 < B →
      (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ B) →
      1 ≤ Rcap → (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Rcap) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      (2*(m+xi)+6*κ*(∑i,width i) ≤ 1 ∨ T=∅) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) (G i) (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*Rcap^epsilon*B^4*(1+2*((m+xi)*Real.log U))^2*
          (1+height)^degree*U^(1+D.t) := by
  obtain ⟨degree,Jp,Cp,hCp,hpositive⟩ := certified_reflected_fourier_moment F κ hκlo hκhi hbeta hκbeta
  obtain ⟨Jz,Cz,hCz,hzero⟩ := certified_reflected_zero_fourier_moment F
  obtain ⟨H,Cr,hCr,hretained⟩ := actual_retained_uniform_fourth epsilon hepsilon 2 (Jp+Jz) (by norm_num)
  refine ⟨degree,H,Cr*(Cp+Cz),by positivity,?_⟩
  filter_upwards [hpositive,hzero,eventually_retained_log_interval Cscale xi hCscale hxi]
    with U hp hz hg
  have hκpos : 0 < κ := by linarith
  have hU := hp.1
  have hUpos := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ G X m B Rcap he hX hm hmmax hB hG hRcap hR
    hcombined T width z height hw hwmax hreal hheight hzim hcapacity
  let n := m+xi
  have hn : 0 ≤ n := by dsimp [n]; linarith
  let P (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let E := (Cp+Cz)*(1+height)^degree*U^(1+D.t)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinterval : 0 ≤ n*Real.log U := mul_nonneg hn (Real.log_pos hU).le
  have hgeom (i:rows) (a:CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes (τ i) (ψ i)))
      (hY:0 < dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
      (ha:a.2∈CenteredMomentReflectedTruncation.retainedAnnuli (U^(xi/4))
        (dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2) hY) :
      Real.log (dyadicScale a.2*dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
        ∈ Set.Icc 0 (n*Real.log U) := hg.2 (τ i) (ψ i) (X i) m (hX i) (hcombined i) a hY ha
  have hpoly (i:rows) (W:ℝ→ℂ) (x freq:ℝ) :
      polynomial (τ i).inverse false W x 0 freq =
        polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false W x 0 freq :=
    (Cycle25.Weighted.RowConductor.polynomial_eq_of_elementCoeff_eq _ _
      (Cycle25.Weighted.RowConductor.inverse_elementCoeff_eq _ _ (he i)) false W x 0 freq).symm
  have hmoment (v w:ℝ) (j k:Fin 2) (x:ℝ) (hx:x∈Set.Icc 0 (n*Real.log U))
      (y:ℝ) (hy:y∈Set.Icc 0 (n*Real.log U)) :
      (∑i:rows, ‖polynomial (τ i).inverse false (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (2*Real.pi*v) *
        polynomial (τ i).inverse false (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k)
        (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
        ≤ E*((1+‖v‖)^(Jp+Jz))^2*((1+‖w‖)^(Jp+Jz))^2 := by
    have hxlen := reflection_window_length U n x hU hn hx
    have hylen := reflection_window_length U n y hU hn hy
    simp_rw [hpoly]
    rcases hcapacity with hcap | hempty
    · have hsum : 0 ≤ ∑s,width s := Finset.sum_nonneg (fun s _=>hw s)
      have hn1 : n ≤ 1 := by dsimp [n]; nlinarith
      have hexp : U^n ≤ U := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le hn1
      have hcap' : length U (Real.exp x)+length U (Real.exp y)+6*κ*(∑s,width s) ≤ 1 := by
        dsimp [n] at hxlen hylen
        linarith [hxlen.1,hylen.1]
      have hb := hp.2 rows hrows T width z height hw hwmax hreal hheight hzim
        (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
        (hxlen.2.trans hexp) (hylen.2.trans hexp) hcap' j k v w
      have hsumBound : (∑i:rows, ‖polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k) (Real.exp y) 0 (2*Real.pi*w) * P i‖^2) ≤
          (Cp*(1+height)^degree*U^(1+D.t))*((1+‖v‖)^Jp)^2*((1+‖w‖)^Jp)^2 := by
        rw [←Finset.sum_coe_sort rows] at hb
        simpa only [P] using hb
      apply hsumBound.trans
      dsimp [E]
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w,abs_nonneg v,abs_nonneg w] | omega
    · have hslot (i:rows) : P i = 1 := by subst T; simp [P]
      simp only [hslot,mul_one]
      have hexp : U^n ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU.le hmmax
      have hb := hz.2 rows hrows (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
        (hxlen.2.trans hexp) (hylen.2.trans hexp) j k v w
      have hsumBound : (∑i:rows, ‖polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false
          (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k) (Real.exp y) 0 (2*Real.pi*w)‖^2) ≤
          (Cz*U^(1+D.t))*((1+‖v‖)^Jz)^2*((1+‖w‖)^Jz)^2 := by
        rw [←Finset.sum_coe_sort rows] at hb
        exact hb
      apply hsumBound.trans
      have hfac : Cz ≤ (Cp+Cz)*(1+height)^degree := by
        apply (show Cz ≤ Cp+Cz by linarith).trans
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))
      dsimp [E]
      gcongr <;> first | exact hfac | linarith [norm_nonneg v,norm_nonneg w,abs_nonneg v,abs_nonneg w] | omega
  have hresult := hretained G τ ψ P X (fun _=>U^(xi/4)) 0 (n*Real.log U) B E Rcap
    hX hinterval hgeom hB hE hG hRcap hR hmoment
  convert hresult using 1 <;> dsimp [E,n] <;> ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.CertifiedRetained -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.RetainedFixed; sha256 a1b0113420a0c6626dd430777a8e6228406b5f078d6341d0e4ef39bec41f13f6 -/
section
                                                

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 800000

lemma eventually_retained_log_cost (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠU:ℝ in atTop, 1 < U ∧ ∀n:ℝ, 0 ≤ n → n ≤ 2 →
      (1+2*(n*Real.log U))^2 ≤ 25*U^(loss/2) := by
  have hlog := (isLittleO_log_rpow_atTop (by linarith:0 < loss/4)).bound (by norm_num:(0:ℝ)<1)
  filter_upwards [hlog,eventually_gt_atTop (1:ℝ)] with U hlog hU
  have hUpos := zero_lt_one.trans hU
  have hlog0 := (Real.log_pos hU).le
  have hh : Real.log U ≤ U^(loss/4) := by
    simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hUpos.le _)] using hlog
  refine ⟨hU,?_⟩
  intro n hn hn2
  have hpow : 1 ≤ U^(loss/4) := Real.one_le_rpow hU.le (by linarith)
  have hbase : 1+2*(n*Real.log U) ≤ 5*U^(loss/4) := by
    have hm := mul_le_mul_of_nonneg_right hn2 hlog0
    nlinarith
  have hnonneg : 0 ≤ 1+2*(n*Real.log U) := by positivity
  calc
    _ ≤ (5*U^(loss/4))^2 := pow_le_pow_left₀ hnonneg hbase 2
    _ = _ := by
      rw [mul_pow,←Real.rpow_natCast (U^(loss/4)) 2,←Real.rpow_mul hUpos.le]
      norm_num
      congr 1
      ring

/-- Fixed source profile version with all restoration and logarithmic losses
absorbed into any prescribed positive exponent loss. The constant is independent
of rowwise coefficient choices and all amplitude/count constants. -/
theorem certified_retained_fixed_profile {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (G:𝓢(ℝ,ℂ)) (loss Cscale Ccond xi:ℝ)
    (hloss:0 < loss) (hCscale:0 < Cscale) (hCcond:0 < Ccond) (hxi:0 < xi) :
    ∃degree:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (X:rows→ℝ) (m:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 →
      (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      (2*(m+xi)+6*κ*(∑i,width i) ≤ 1 ∨ T=∅) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) G (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,H,Cr,hCr,hr⟩ := certified_actual_retained_fourth F κ hκlo hκhi hbeta hκbeta (loss/2) Cscale xi
    (by linarith) hCscale hxi
  let B := 1+H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G
  let K := max 1 Ccond
  have hB : 0 < B := by have := apply_nonneg (H.sup (schwartzSeminormFamily ℝ ℝ ℂ)) G; dsimp [B]; linarith
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨degree,25*Cr*K^(loss/2)*B^4,by positivity,?_⟩
  filter_upwards [hr,eventually_retained_log_cost loss hloss] with U hr hl
  have hU := hr.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ X m he hX hm hmmax hred hcombined T width z height
    hw hwmax hreal hh him hcapacity
  have hRcap : 1 ≤ K*U := by nlinarith
  have hred' (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ K*U :=
    (hred i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hUp.le)
  have hGB (i:rows) : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ B := by dsimp [B]; linarith
  have hb := hr.2 rows hrows τ ψ (fun _=>G) X m B (K*U) he hX hm hmmax hB hGB
    hRcap hred' hcombined T width z height hw hwmax hreal hh him hcapacity
  have hlog := hl.2 (m+xi) (by linarith) hmmax
  apply hb.trans
  calc
    _ ≤ Cr*(K*U)^(loss/2)*B^4*(25*U^(loss/2))*(1+height)^degree*U^(1+D.t) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hKpos.le hUp.le]
      calc
        _ = (25*Cr*K^(loss/2)*B^4)*(1+height)^degree*
            (U^(loss/2)*U^(loss/2)*U^(1+D.t)) := by ring
        _ = _ := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]; congr 2; ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.RetainedFixed -/

/- BEGIN ORIGINAL Cycle61.Moment.InitialState; sha256 489e3676d18af9f969ba91f15b0b1d3ba2de0805341b74f6087a919a7b37fa0e -/
section
                                                                     
                                                                          

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical SchwartzMap
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- A fixed parent has no moving anchor. The existing state API records the
fixed conductor by its exact logarithmic width rather than setting it to zero. -/
def fixedParentState (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (bΦ Z M : ℝ) (hZ : 1 < Z) (hM : 0 ≤ M)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀ x, 0 ≤ (Φ x).re) : NaturalState Z 0 bΦ where
  character := η
  fixedModulus := Q
  puncture := 1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := Z^M
    scale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    nonneg := fun _ => hp _ }
  rowWidth := M
  characterWidth := Real.logb Z (η.modulus.absNorm : ℝ)
  base_ge_one := hZ.le
  row_nonneg := hM
  character_nonneg := Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
  scale_eq := rfl
  modulus_bound := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))]
  puncture_ne_zero := one_ne_zero
  puncture_bound := by simp
  radial_support := hs
  row_ne_zero := fun _ h => h.1
  nonexceptional := fun _ h => h.2

theorem fixedParentState_width (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (bΦ Z M : ℝ) (hZ : 1 < Z) (hM : 0 ≤ M)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀ x, 0 ≤ (Φ x).re) :
    (fixedParentState η Q Φ bΦ Z M hZ hM hs hp).width =
      M + Real.logb Z (η.modulus.absNorm : ℝ) := rfl

/-- One scale threshold works for the fixed finite anchor dictionary and
every row width above a fixed positive lower bound, before any live heights. -/
theorem fixed_anchor_width_uniform {Label : Type*} [Fintype Label]
    (η : Label → Character) (Mmin ε : ℝ) (hMmin : 0 < Mmin) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ j : Label, ∀ M : ℝ, Mmin ≤ M →
      Real.logb Z ((η j).modulus.absNorm : ℝ) ≤ ε*M := by
  have hfixed (j : Label) : ∀ᶠ Z : ℝ in atTop,
      ((η j).modulus.absNorm : ℝ) ≤ Z^(ε*Mmin) :=
    (tendsto_rpow_atTop (mul_pos hε hMmin)).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_all.mpr hfixed, eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ, ?_⟩
  intro j M hM
  have hn : 0 < ((η j).modulus.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (η j).modulus_ne_bot)
  apply (Real.logb_le_iff_le_rpow hZ hn).mpr
  exact (hz j).trans (Real.rpow_le_rpow_of_exponent_le hZ.le
    (mul_le_mul_of_nonneg_left hM hε.le))

theorem fixedParentState_twists
    (rayModulus : Ideal O) [NeZero rayModulus]
    (H : Subgroup (O ⧸ rayModulus)ˣ)
    (hH : RayOrthogonality.globalUnits rayModulus ≤ H)
    (η η₀ : Character) (Q : Ideal O) (hQM : Q ≤ rayModulus)
    (hQη : Q ≤ η₀.modulus) (z : O)
    (hz : initialKeep η Q z) :
    ∀ θ : RayQuotient.Characters rayModulus H,
      ((naturalRow η z hz.1).character.product
        (relativeCharacter rayModulus H hH η₀ θ)).residue ≠ 1 := by
  intro θ
  exact sector_nonprincipal rayModulus H hH (naturalRow η z hz.1)
    η₀ θ Q 1 hQM hQη one_ne_zero hz.1 hz.2

#print axioms fixedParentState
#print axioms fixed_anchor_width_uniform
#print axioms fixedParentState_twists
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.InitialState -/
