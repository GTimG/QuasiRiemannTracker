import Candidate.Cycle63.Numerator.Fourth.Fourier
import Candidate.Cycle25.Energy.Physical.CertifiedZero
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.NumeratorCertifiedZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace Cycle63.Numerator.Fourth
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentDetectorPlainFiberSource
open Cycle25WeightedNumeratorPhysical

/-- The improved interior is combined with genuine original small-plain,
small-slot and empty-slot bounds, covering every dual scale in restoration. -/
theorem hybrid_fourier {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ)
    (hk0 : 7/10≤κ) (hk1 : κ≤3/4) (hb : 51/100≤ HeckeZeroSupremum.beta)
    (hkb : 2*HeckeZeroSupremum.beta-1≤κ)
    (bΦ mesh ε : ℝ) (hε : 0<ε)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh ε U di control Ci) :
    ∃degree J:ℕ,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      1<U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height n:ℝ,
      (∀i,0≤ width i) → (∀i,width i≤ mesh) →
      (∀i,width i≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i,(z i).re=17/50) → 0≤ height → (∀i,|(z i).im|≤ height) →
      0≤ n → n≤2 →
      ((∃d t:ℝ,Arithmetic.dMinus≤ d ∧ d≤ Arithmetic.dPlus ∧ 0≤ t ∧ t≤ Arithmetic.t0 ∧
        n=Physical.plainScale d t ∧ (∑i,width i)≤ Physical.affineCapacity d t) ∨
        (2*n+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤ U^n → X₂≤ U^n →
      length U X₁≤ n → length U X₂≤ n → ∀j k:Fin 2,∀v w:ℝ,
      (∑u∈rows,‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
      ≤ (C*(1+height)^degree*U^(1+D.t+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  have ha:=affine_fourier F bΦ mesh ε hsΦ di control Ci hCi hinput
  obtain ⟨Ja,Ca,hCa,ha⟩:=ha
  obtain ⟨dp,Jp,Cp,hCp,hp⟩:=certified_reflected_fourier_moment F κ hk0 hk1 hb hkb
  obtain ⟨Jz,Cz,hCz,hz⟩:=OAI.SevenEighths.WeightedNumeratorReflection.certified_reflected_zero_fourier_moment F hb
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
    have hn1 : n≤1 := by
      have h := hnhi
      simp only [Cycle63.CountAffine.plainTop] at h
      linarith
    have hx1hi:length U X₁≤Cycle63.CountAffine.plainTop:=hx₁.trans hnhi.le
    have hx2hi:length U X₂≤Cycle63.CountAffine.plainTop:=hx₂.trans hnhi.le
    have hs37:(∑i,width i)≤Physical.smallPlainCap:=hslots.trans hslotshi
    have hcap25:Physical.smallPlainCap≤Cycle63.Optimization.slotTop:=by norm_num [Physical.smallPlainCap, CountAffine.windowBottom, CountAffine.plainTop, Cycle63.Optimization.slotTop]
    by_cases hslo:Cycle63.Optimization.slotFloor≤∑i,width i
    · by_cases h1:Cycle63.CountAffine.windowBottom≤ length U X₁
      · by_cases h2:Cycle63.CountAffine.windowBottom≤ length U X₂
        · have hbound:=ha.2 rows hrows T width z height hw hmesh hzre hh him X₁ X₂ hX₁ hX₂
            h1 (by linarith [Cycle63.CountAffine.plainTop_le_plainLengthTop]) h2
            (by linarith [Cycle63.CountAffine.plainTop_le_plainLengthTop]) hslo (by linarith)
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

end Cycle63.Numerator.Fourth
