import Candidate.Target836.Num836.Fourth.Input
import Candidate.Cycle25.Energy.Physical.CertifiedFourier
import Candidate.Cycle25.Energy.Physical.CertifiedZero
import Candidate.Cycle25.Energy.Physical.RetainedGeometry
import Candidate.Cycle25.Numerator.ReflectionRetained
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
import Candidate.Cycle25.Energy.Physical.RetainedFixed

/- Original module: Candidate.Target836.Num836.Fourth.Fourier. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace Target836.Numerator.Fourth
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentEnergyBands CenteredMomentRowNorm
open CenteredMomentDetectorPlainFiberSource CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentNaturalPrimitive
open ProbePhysical CenteredMomentWholeSlotDeletion
open Cycle25WeightedNumeratorPhysical
local notation "O" => HeckeFamily.O

/-- Affine interior physical Fourier pair. The analytic premise is the actual
initial radial energy, not a row fourth moment or an improved zero-free endpoint. -/
theorem affine_fourier {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε : ℝ) (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh ε U degree control Ci) :
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0≤ width i) → (∀i,width i≤ mesh) → (∀i,(z i).re=17/50) →
      0≤ height → (∀i,|(z i).im|≤ height) →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      41/100≤ length U X₁ → length U X₁≤44/100 →
      41/100≤ length U X₂ → length U X₂≤44/100 →
      17/500≤∑i,width i → (∑i,width i)≤1/25 →
      length U X₁+length U X₂+Arithmetic.lambda*(∑i,width i)≤ Arithmetic.B →
      ∀j k:Fin 2,∀v w:ℝ,
      (∑u∈rows,‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
      ≤ (C*(1+height)^degree*U^(1+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨J,Cp,hCp,hprofile⟩:=numerator_fourier_profiles_control control
  let C:=Ci*(1+diagonalControl radialMajorant)*Cp
  have hC:0< C:=by have:=diagonalControl_nonneg radialMajorant;dsimp [C];positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hinput,eventually_fixed_source_keep F η,eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop (η.modulus.absNorm:ℝ)] with U ha hkeep hU hη
  refine ⟨hU,?_⟩
  intro rows hrows T width z height hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslo hshi hcap j k v w
  have he:=finite_physical_pair_affine F rows radialMajorant U bΦ mesh ε hU.le hsΦ
    radialMajorant_nonneg hη (fun u hu=>(hrows u hu).2)
    (fun u hu=>hkeep u (hrows u hu).1) radialMajorant_one degree control Ci ha
    T width z height hw hwmax hz hh hzim (numeratorFourierProfiles j k v w) X₁ X₂
    hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslo hshi hcap
  have heq :
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) =
      (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0 *
        ∏i,normalizedSlot η rowMaskElement 1 u.val (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
          (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      source_physical_slot_conj F u _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _),
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂,←map_prod,Complex.norm_conj]
  rw [heq]
  apply he.trans
  have hd:=diagonalControl_nonneg radialMajorant
  have hp:=hprofile j k v w
  calc
    _ ≤ (Ci*(1+diagonalControl radialMajorant))*
        (Cp*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*(1+height)^degree*U^(1+ε) := by
      gcongr
      linarith
    _ = _ := by dsimp [C];ring

end Target836.Numerator.Fourth

#print axioms Target836.Numerator.Fourth.affine_fourier
end

/- Original module: Candidate.Target836.Num836.Fourth.Hybrid. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace Target836.Numerator.Fourth
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentDetectorPlainFiberSource
open Cycle25WeightedNumeratorPhysical

/-- The improved interior is combined with genuine original small-plain,
small-slot and empty-slot bounds, covering every dual scale in restoration. -/
theorem hybrid_fourier {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ)
    (hk0 : 7/10≤ κ) (hk1 : κ≤3/4) (hb : 51/100≤ HeckeZeroSupremum.beta)
    (hkb : 2*HeckeZeroSupremum.beta-1≤ κ)
    (bΦ mesh ε : ℝ) (hε : 0< ε)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh ε U di control Ci) :
    ∃degree J:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height n:ℝ,
      (∀i,0≤ width i) → (∀i,width i≤ mesh) →
      (∀i,width i≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i,(z i).re=17/50) → 0≤ height → (∀i,|(z i).im|≤ height) →
      0≤ n → n≤2 →
      ((∃d t:ℝ,Arithmetic.dMinus≤ d ∧ d≤ Arithmetic.dPlus ∧ 0≤ t ∧ t≤ Arithmetic.t0 ∧
        n=Physical.plainScale d t ∧ (∑i,width i)≤ Physical.affineCapacity d t) ∨
        (2*n+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ → X₁≤ U^n → X₂≤ U^n →
      length U X₁≤ n → length U X₂≤ n → ∀j k:Fin 2,∀v w:ℝ,
      (∑u∈rows,‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
      ≤ (C*(1+height)^degree*U^(1+D.t+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨Ja,Ca,hCa,ha⟩:=affine_fourier F bΦ mesh ε hsΦ di control Ci hCi hinput
  obtain ⟨dp,Jp,Cp,hCp,hp⟩:=certified_reflected_fourier_moment F κ hk0 hk1 hb hkb
  obtain ⟨Jz,Cz,hCz,hz⟩:=certified_reflected_zero_fourier_moment F
  refine ⟨di+dp,Ja+Jp+Jz,Ca+Cp+Cz,by positivity,?_⟩
  filter_upwards [ha,hp,hz] with U ha hp hz
  have hU:=ha.1
  have hUp:=zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows T width z height n hw hmesh hwmax hzre hh him hn hn2 hcap X₁ X₂ hX₁ hX₂ hX₁max hX₂max hx₁ hx₂ j k v w
  have hsum:0≤∑i,width i:=Finset.sum_nonneg (fun i _=>hw i)
  have hUε:U^(1+ε)≤ U^(1+D.t+ε):=Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [D.t_pos])
  have hUt:U^(1+D.t)≤ U^(1+D.t+ε):=Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  have baseline (hbudget : 2*n+6*κ*(∑i,width i)≤1) := by
    have hn1:n≤1:=by nlinarith
    have hpow:U^n≤ U:=by simpa using Real.rpow_le_rpow_of_exponent_le hU.le hn1
    have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
      (hX₁max.trans hpow) (hX₂max.trans hpow) (by linarith) j k v w
    exact hb'
  rcases hcap with ⟨d,t,hd0,hd1,ht0,ht1,heq,hslots⟩ | hold
  · have hnhi:= (Physical.plainScale_interior ⟨hd0,hd1⟩ ⟨ht0,ht1⟩).2
    have hslotshi:= (Physical.affineCapacity_interior ⟨hd0,hd1⟩ ⟨ht0,ht1⟩).2
    rw [←heq] at hnhi
    have hx1hi:length U X₁≤264/625:=hx₁.trans hnhi.le
    have hx2hi:length U X₂≤264/625:=hx₂.trans hnhi.le
    have hs37:(∑i,width i)≤37/1000:=hslots.trans hslotshi.le
    by_cases hslo:17/500≤∑i,width i
    · by_cases h1:41/100≤ length U X₁
      · by_cases h2:41/100≤ length U X₂
        · have hbound:=ha.2 rows hrows T width z height hw hmesh hzre hh him X₁ X₂ hX₁ hX₂
            h1 (by linarith) h2 (by linarith) hslo (by linarith)
            (Physical.affine_shortening (heq ▸ hx₁) (heq ▸ hx₂) hslots) j k v w
          apply hbound.trans
          gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
        · have hc:=Physical.small_plain_shortening (le_of_not_ge h2) hx1hi hs37
          have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
            (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
            (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
            (by nlinarith) j k v w
          apply hb'.trans
          gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
      · have hc:=Physical.small_plain_shortening (le_of_not_ge h1) hx2hi hs37
        have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
          (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
          (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
          (by nlinarith) j k v w
        apply hb'.trans
        gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
    · have hc:=Physical.small_slot_shortening hx1hi hx2hi (le_of_not_ge hslo)
      have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
        (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
        (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
        (by nlinarith) j k v w
      apply hb'.trans
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
  · rcases hold with hbudget | hempty
    · apply (baseline hbudget).trans
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
    · subst T
      simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one]
      have hb':=hz.2 rows hrows X₁ X₂ hX₁ hX₂
        (hX₁max.trans (Real.rpow_le_rpow_of_exponent_le hU.le hn2))
        (hX₂max.trans (Real.rpow_le_rpow_of_exponent_le hU.le hn2)) j k v w
      apply hb'.trans
      have hheight:1≤(1+height)^(di+dp):=one_le_pow₀ (by linarith)
      have hc:Cz≤(Ca+Cp+Cz)*(1+height)^(di+dp):=by nlinarith
      gcongr <;> first | exact hc | linarith [norm_nonneg v,norm_nonneg w]

end Target836.Numerator.Fourth

#print axioms Target836.Numerator.Fourth.hybrid_fourier
end

/- Original module: Candidate.Target836.Num836.Fourth.Retained. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

namespace OAI
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Target836NumeratorFourth
open Cycle25WeightedNumeratorReflection
open Cycle25WeightedNumeratorPhysical Target836.Numerator.Fourth
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
theorem affine_actual_retained_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bΦ mesh affineError : ℝ) (hAffineError : 0< affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh affineError U di control Ci)
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
      (∀i,width i≤ mesh) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      ((∃d t:ℝ,Target836.Arithmetic.dMinus≤ d ∧ d≤ Target836.Arithmetic.dPlus ∧
        0≤ t ∧ t≤ Target836.Arithmetic.t0 ∧ m+xi=Target836.Physical.plainScale d t ∧
        (∑i,width i)≤ Target836.Physical.affineCapacity d t) ∨
        (2*(m+xi)+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) (G i) (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*Rcap^epsilon*B^4*(1+2*((m+xi)*Real.log U))^2*
          (1+height)^degree*U^(1+D.t+affineError) := by
  obtain ⟨degree,Jp,Cp,hCp,hpositive⟩:=hybrid_fourier F κ hκlo hκhi hbeta hκbeta
    bΦ mesh affineError hAffineError hsΦ di control Ci hCi hinput
  obtain ⟨H,Cr,hCr,hretained⟩ := actual_retained_uniform_fourth epsilon hepsilon 2 Jp (by norm_num)
  refine ⟨degree,H,Cr*Cp,by positivity,?_⟩
  filter_upwards [hpositive,eventually_retained_log_interval Cscale xi hCscale hxi]
    with U hp hg
  have hκpos : 0 < κ := by linarith
  have hU := hp.1
  have hUpos := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ G X m B Rcap he hX hm hmmax hB hG hRcap hR
    hcombined T width z height hw hwmesh hwmax hreal hheight hzim hcapacity
  let n := m+xi
  have hn : 0 ≤ n := by dsimp [n]; linarith
  let P (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let E := Cp*(1+height)^degree*U^(1+D.t+affineError)
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
        ≤ E*((1+‖v‖)^Jp)^2*((1+‖w‖)^Jp)^2 := by
    have hxlen := reflection_window_length U n x hU hn hx
    have hylen := reflection_window_length U n y hU hn hy
    simp_rw [hpoly]
    have hb:=hp.2 rows hrows T width z height n hw hwmesh hwmax hreal hheight hzim
      hn hmmax hcapacity (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
      hxlen.2 hylen.2 hxlen.1 hylen.1 j k v w
    rw [←Finset.sum_coe_sort rows] at hb
    simpa only [P,E] using hb
  have hresult := hretained G τ ψ P X (fun _=>U^(xi/4)) 0 (n*Real.log U) B E Rcap
    hX hinterval hgeom hB hE hG hRcap hR hmoment
  convert hresult using 1 <;> dsimp [E,n] <;> ring

end SevenEighths.Target836NumeratorFourth
end
end OAI

/- Adapted from Cycle25 physical primitive restoration and its Apache-2.0 source.
The Cycle63 affine input is explicit; both old fallback branches are proved. -/

#print axioms OAI.SevenEighths.Target836NumeratorFourth.affine_actual_retained_fourth
end

/- Original module: Candidate.Target836.Num836.Fourth.Fixed. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

namespace OAI
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Target836NumeratorFourth
open Cycle25WeightedNumeratorPhysical Target836.Numerator.Fourth
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 800000

/-- Fixed source profile version with all restoration and logarithmic losses
absorbed into any prescribed positive exponent loss. The constant is independent
of rowwise coefficient choices and all amplitude/count constants. -/
theorem affine_retained_fixed_profile {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bΦ mesh affineError : ℝ) (hAffineError : 0< affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh affineError U di control Ci)
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
      (∀i,width i≤ mesh) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      ((∃d t:ℝ,Target836.Arithmetic.dMinus≤ d ∧ d≤ Target836.Arithmetic.dPlus ∧
        0≤ t ∧ t≤ Target836.Arithmetic.t0 ∧ m+xi=Target836.Physical.plainScale d t ∧
        (∑i,width i)≤ Target836.Physical.affineCapacity d t) ∨
        (2*(m+xi)+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) G (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) := by
  obtain ⟨degree,H,Cr,hCr,hr⟩ := affine_actual_retained_fourth F κ hκlo hκhi hbeta hκbeta
    bΦ mesh affineError hAffineError hsΦ di control Ci hCi hinput (loss/2) Cscale xi
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
    hw hwmesh hwmax hreal hh him hcapacity
  have hRcap : 1 ≤ K*U := by nlinarith
  have hred' (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ K*U :=
    (hred i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hUp.le)
  have hGB (i:rows) : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ B := by dsimp [B]; linarith
  have hb := hr.2 rows hrows τ ψ (fun _=>G) X m B (K*U) he hX hm hmmax hB hGB
    hRcap hred' hcombined T width z height hw hwmesh hwmax hreal hh him hcapacity
  have hlog := hl.2 (m+xi) (by linarith) hmmax
  apply hb.trans
  calc
    _ ≤ Cr*(K*U)^(loss/2)*B^4*(25*U^(loss/2))*(1+height)^degree*U^(1+D.t+affineError) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hKpos.le hUp.le]
      calc
        _ = (25*Cr*K^(loss/2)*B^4)*(1+height)^degree*
            (U^(loss/2)*U^(loss/2)*U^(1+D.t+affineError)) := by ring
        _ = _ := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]; congr 2; ring

end SevenEighths.Target836NumeratorFourth
end
end OAI

/- Adapted from Cycle25 retained profile restoration, Apache-2.0. -/

#print axioms OAI.SevenEighths.Target836NumeratorFourth.affine_retained_fixed_profile
end
