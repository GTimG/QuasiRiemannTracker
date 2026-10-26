/- Adapted from the pinned Hailey Collet/OpenAI transport.
Apache-2.0 attribution is retained in each source block.
Only guard class/namespace references are generalized; analytic proof bodies
and original physical objects are preserved.  -/
import Candidate.FourthPower.TransportGeometry
import Candidate.FourthPower.TransportPrincipalPhysical
import Candidate.FourthPower.TransportPrincipalBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysicalRemainder
import Candidate.FourthPower.TransportFiniteProduct
import Candidate.FourthPower.TransportSignal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalResidueActual
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PrincipalRemainderPhysicalBounds -/
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SilFourthPowerTransport.Transport.PrincipalPhysical
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
open SilFourthPowerTransport.Transport.PrincipalFiniteProduct SilFourthPowerTransport.Transport.PrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e ≤ 1/1000)
    (ha : theta <HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e ≤ 2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀slotEll : Fin K→ℝ,(∑j,slotEll j)=ell → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0 ≤ W j x ∧ W j x ≤ B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1 ≤ Z → (∀j,480 ≤ c*Z^(slotEll j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(slotEll j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(slotEll j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(slotEll j)))‖ ≤ 
      C/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := SilFourthPowerTransport.Transport.PrincipalRemainderBounds.source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro slotEll hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith [SilFourthPowerTransport.Transport.theta_bounds]
  have hb := hbound slotEll hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have heq := SilFourthPowerTransport.Transport.PrincipalPhysical.principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(slotEll j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith [SilFourthPowerTransport.Transport.theta_bounds]) (by linarith [SilFourthPowerTransport.Transport.theta_bounds]) he (by linarith [SilFourthPowerTransport.Transport.theta_bounds])
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _ ≤ (2*C)/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000)
  apply hn.trans
  have hCe : C ≤ C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0 ≤ Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end SilFourthPowerTransport.Transport.PrincipalPhysical
end
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PrincipalRemainderPhysicalBounds -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PrincipalRemainderResidueActual -/
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SilFourthPowerTransport.Transport.PrincipalResidueActual
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalResidueActual
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbeFiniteProductBounds ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation
open ActualEisensteinCubic CompletedGauss
open SilFourthPowerTransport.Transport.PrincipalFiniteProduct SilFourthPowerTransport.Transport.PrincipalSignal


theorem actual_window_residue {κ : Type*} (η : Character) (S : Finset κ)
    (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (s : ℂ) :
    windowMultiplier η S T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      slotProduct S T (residueWeights W scale) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val))
        (fun _ p => idealCoeff η p.val) s := by
  exact SilFourthPowerTransport.Transport.PrincipalFiniteProduct.window_at_residue η S T W scale s

theorem normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : theta <a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta<a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0<a0 → 0<a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0 ≤ (W0 y).re) → (∀y,0 ≤ (W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480 ≤ P → 1440*P^(-(theta  : ℝ)) ≤ 1 →
      (∀j∈S,∀p∈T j,0 ≤ W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0<slotMass T (residueWeights W scale) j) → 1 ≤ Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z ell (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏p∈E,p)^2/6 *
        sourceMultiplier W0 W1 (Z^(lx : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I))
          (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^(lx : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          HeckeSignal.signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (PrincipalSignal.signalShift) Z‖  ≤ 
        D*Z^(a+PrincipalSignal.signalShift)*P^(-(theta  : ℝ)) := by
  dsimp only
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := SilFourthPowerTransport.Transport.PrincipalSignal.exists_normalized_actual_source_bound E hE η ha ha2 hβ S
  refine ⟨D,hD,?_⟩
  intro W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  refine hbound W0 W1 T (residueWeights W scale) P Y Z
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    hP hsmall ?_ hnorm hcop hmass hZ ?_ ?_
  · intro j hj p hp
    exact mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)
  · exact ProbePrincipalNormalizer.sourceResidueConstant_ne_zero (∏p∈E,p)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  · intro t
    exact actual_window_residue η S T W scale _

end SilFourthPowerTransport.Transport.PrincipalResidueActual
end
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PrincipalRemainderResidueActual -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PrincipalRemainderRayThresholds -/
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SilFourthPowerTransport.Transport.PrincipalRaySlots
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
open OAI.SevenEighths.ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0<c) (hd : c ≤ d) (hmin : 0<ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin ≤ ell j) :
    ∀ᶠZ : ℝ in atTop,
      1 ≤ Z ∧ 480 ≤ c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(theta :ℝ)) ≤ 1 ∧
      (∀j,480 ≤ c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)<c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin ≤ (P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(theta :ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by first | (solve | norm_num) | (linarith [SilFourthPowerTransport.Transport.theta_bounds]) : (0:ℝ)<theta )).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0<Z := by linarith [SilFourthPowerTransport.Transport.theta_bounds]
  have hmono (j : ι) : c*Z^ellMin ≤ c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
include hH

theorem power_ray_mass_and_normalizer {ι : Type*} [Fintype ι]
    (S : Finset Id) (W : ι→ℝ→ℝ) (c d : ℝ) (hc : 0<c) (hd : c ≤ d)
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hp : ∀j,tsupport (W j)⊆Set.Ioi 0) (hW0 : ∀j y,0 ≤ W j y) (hne : ∀j,W j≠0)
    (ell : ι→ℝ) (hell : ∀j,0<ell j) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      (∀j,0<slotMass T (residueWeights W (fun j=>Z^(ell j))) j) ∧
      |(Probe.principalScalar Finset.univ Z (∑j,ell j)
        (slotMass T (residueWeights W (fun j=>Z^(ell j)))))⁻¹| ≤ Z^eps := by
  have hm : ∀ᶠZ : ℝ in atTop,∀j,0<slotMass
      (fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j)))
      (residueWeights W (fun j=>Z^(ell j))) j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop (hell j)).eventually
      (ray_pool_mass_eventually_positive M H hH S (W j) c d hc hd (hsupp j)
        (hW j) (hcompact j) (hp j) (hW0 j) (hne j))
  have hi := ProbeRayNormalization.ray_principalScalar_inverse_subpower M H hH Finset.univ S W
    (fun _=>c) (fun _=>d) ell (fun _ _=>hc) (fun _ _=>hd) (fun j _=>hsupp j)
    (fun j _=>hW j) (fun j _=>hcompact j) (fun j _=>hp j) (fun j _=>hW0 j) (fun j _=>hne j)
    (fun j _=>hell j) eps heps
  filter_upwards [hm,hi] with Z hmass hinv
  exact ⟨hmass,hinv⟩
end SilFourthPowerTransport.Transport.PrincipalRaySlots
end
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PrincipalRemainderRayThresholds -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PrincipalRemainderNormalized -/
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace SilFourthPowerTransport.Transport.PrincipalNormalized
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
open SilFourthPowerTransport.Transport.PrincipalResidueActual SilFourthPowerTransport.Transport.PrincipalRaySlots
local notation "Id" => Ideal HeckeFamily.O

lemma normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0 ≤ c) (hA : ‖A-R‖ ≤ c) (hN : ‖N⁻¹‖ ≤ v)
    (hR : ‖R/N-F‖ ≤ d) : ‖A/N-F‖ ≤ c*v+d := by
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _  ≤  ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _  ≤  c*v+d := by rw [norm_mul];gcongr

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B) (hmin : 0<ellMin)
    (slotEll : Fin K→ℝ) (hell : ∀j,ellMin ≤ slotEll j) (hdis : Function.Injective slotEll)
    (hsum : (∑j,slotEll j)=ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0 ≤ (W0 y).re) (hp1 : ∀y,0 ≤ (W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e ≤ 1/1000) (hnu : 0<nu)
    (ha : theta <HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e ≤ 2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(slotEll j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z ell
          (slotMass T (residueWeights W (fun j=>Z^(slotEll j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(slotEll j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (PrincipalSignal.signalShift) Z‖ ≤ 
      C*(Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000+nu)+
        Z^(HeckeZeroSupremum.beta-(4+b)/6+e-(theta )*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := SilFourthPowerTransport.Transport.PrincipalPhysical.physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := SilFourthPowerTransport.Transport.PrincipalResidueActual.normalized_actual_window_residue S hS η ha ha2 (by linarith [SilFourthPowerTransport.Transport.theta_bounds]) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(theta :ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [SilFourthPowerTransport.Transport.PrincipalRaySlots.power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin slotEll hell,
    OAI.SevenEighths.ProbeRaySlots.power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne slotEll (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) slotEll (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0<Z := by linarith [SilFourthPowerTransport.Transport.theta_bounds]
  let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(slotEll j))
  let normer := cs*(Probe.principalScalar Finset.univ Z ell
    (slotMass T (residueWeights W (fun j=>Z^(slotEll j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=>Z^(slotEll j)) (c*Z^ellMin) (Z^(ly:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=>hmass.1 j) hZ
  dsimp only at hr ⊢
  simp only [PrincipalSignal.signalShift, neg_div, ← sub_eq_add_neg] at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem slotEll hsum W hWbounds (fun j=>Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖ ≤ ‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(theta :ℝ))=c^(-(theta :ℝ))*Z^(-(theta :ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-(4+b)/6)*(c*Z^ellMin)^(-(theta :ℝ))=
      (D*c^(-(theta :ℝ)))*Z^(HeckeZeroSupremum.beta-(4+b)/6+e-(theta )*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-(4+b)/6+e-(theta )*ellMin=
      (HeckeZeroSupremum.beta+e-(4+b)/6)+(-(theta :ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖ ≤ C := by
    dsimp [C]
    have : 0 ≤ D*c^(-(theta :ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(theta :ℝ)) ≤ C := by
    dsimp [C]
    have : 0 ≤ C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _  ≤  C*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000+nu)+
        C*Z^(HeckeZeroSupremum.beta-(4+b)/6+e-(theta )*ellMin) := by gcongr
    _ = _ := by ring
end SilFourthPowerTransport.Transport.PrincipalNormalized
end
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PrincipalRemainderNormalized -/
