/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B024
import Submissions.cycle61_c0125139.Bundles.B031
import Submissions.cycle61_c0125139.Bundles.B032
import Submissions.cycle61_c0125139.Bundles.B033
import Submissions.cycle61_c0125139.Bundles.B034
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalResidueActual
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderResidueActual; sha256 665614f88a1720bb2bf188600ecc676d6c74b0a08984f96dec75bb6c7f498b46 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                                 
                                                 
                                                                  
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace Cycle61.Transport.PrincipalResidueActual
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalResidueActual
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbeFiniteProductBounds ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation
open ActualEisensteinCubic CompletedGauss
open Cycle61.Transport.PrincipalFiniteProduct Cycle61.Transport.PrincipalSignal


theorem actual_window_residue {κ : Type*} (η : Character) (S : Finset κ)
    (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (s : ℂ) :
    windowMultiplier η S T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      slotProduct S T (residueWeights W scale) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val))
        (fun _ p => idealCoeff η p.val) s := by
  exact Cycle61.Transport.PrincipalFiniteProduct.window_at_residue η S T W scale s

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
  obtain ⟨D,hD,hbound⟩ := Cycle61.Transport.PrincipalSignal.exists_normalized_actual_source_bound E hE η ha ha2 hβ S
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

end Cycle61.Transport.PrincipalResidueActual
end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderResidueActual -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderNormalized; sha256 039c682688666f1698ba5a5106429cc2f8221aaaef6f8d2b7c8574dac6298842 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                                  
                                                                 
                                                                 
                                                               
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace Cycle61.Transport.PrincipalNormalized
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
open Cycle61.Transport.PrincipalResidueActual Cycle61.Transport.PrincipalRaySlots
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
  obtain ⟨C0,hC0,hrem⟩ := Cycle61.Transport.PrincipalPhysical.physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := Cycle61.Transport.PrincipalResidueActual.normalized_actual_window_residue S hS η ha ha2 (by linarith [Cycle61.Transport.theta_bounds]) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(theta :ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [Cycle61.Transport.PrincipalRaySlots.power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin slotEll hell,
    OAI.SevenEighths.ProbeRaySlots.power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne slotEll (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) slotEll (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0<Z := by linarith [Cycle61.Transport.theta_bounds]
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
#print axioms actual_ray_principal_comparison
end Cycle61.Transport.PrincipalNormalized
end

end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderNormalized -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.TailScales; sha256 f2da1ffbe6be7b4514fe5d9aec9c5710c85c25f41b5be4569fd38e4f144ed4b7 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
                                               
                                                       
                                                         
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily

lemma selected_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ) (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Cycle61.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(Cycle61.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(Cycle61.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+Cycle61.Transport.b)/6-(Cycle61.Arithmetic.y/2-Cycle61.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Cycle61.Assembly.row_endpoint, Cycle61.Transport.b]
  linarith [Cycle61.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Cycle61.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(Cycle61.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(Cycle61.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+Cycle61.Arithmetic.x/2+Cycle61.Arithmetic.y)+(Cycle61.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Cycle61.Assembly.row_endpoint]
  ring

end SevenEighths.Cycle61HighRowFamily
end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.TailScales -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.CommonProbe; sha256 d0f3e9357e35dd21fa68af3b17b5a399c49caf4a7b7ccb621fdad8821e01575a -/
section
                                 
                                                              
                                            
                                                               

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle61HighTransport
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeRaySlots CompletedGauss CanonicalQuadraticSieve
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem principal_shift_is_common :
    Cycle61.Transport.PrincipalSignal.signalShift = Cycle61.Assembly.signalShift :=
  Cycle61.Transport.signalShift_eq

/-- The exact principal, finite central, and tail partition of the shared
normalized probe at the new physical lengths. -/
theorem normalizedProbe_partition {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (slotEll : Fin K→ℝ) (a b ζ Z : ℝ)
    (hζ : 0 ≤ ζ) (hZ : 1 ≤ Z) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (η : Character) :
    let Yp := fun j=>Z^(slotEll j)
    let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
    let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
    let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z Cycle61.Arithmetic.ell
        (slotMass T (residueWeights W Yp)) : ℂ)
    Cycle61Low.normalizedProbe M H S hmax slotEll a b W W0 W1 η Z =
      principalPhysicalPool η S T WC Yp W0 W1
        (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z/normer +
      ((∑n∈smallDyadicIndices (Z^(1/100:ℝ)),
          finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n) T WC Yp W0 W1
            (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z)+
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^(Cycle61.Arithmetic.h+ζ)))
          T WC Yp W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z+
        (∑'n : ℕ, finitePhysicalRows S hmax η (dyadicRows (Z^(Cycle61.Arithmetic.h+ζ)) n)
          T WC Yp W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z))/normer := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let Yp := fun j=>Z^(slotEll j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hT : ∀i P,P∈T i → Supported P.val := by
    intro i P hP
    exact outside_prime_supported S hS.bad P ((mem_pool _ S a b (Yp i) P).mp hP).2.2.2
  have hp := canonical_physical_probe_partition S hS hmax η T hT WC Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z
    (Z^(1/100:ℝ)) (Z^(Cycle61.Arithmetic.h+ζ))
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num))
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Cycle61.Transport.h_interval.1]))
  dsimp only
  change _ = principalPhysicalPool η S T WC Yp W0 W1 _ _ _ / _ + _
  unfold Cycle61Low.normalizedProbe
  dsimp only
  rw [hp]
  exact add_div _ _ _

#print axioms normalizedProbe_partition
end SevenEighths.Cycle61HighTransport
end
end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.CommonProbe -/
