/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/SourceSlotEnvelope.lean. Original formulas and source attribution retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.WholeSourceGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.NaturalLowDensity.WholeGeometry
open OAI OAI.SevenEighths
open OAI.SevenEighths.Record12518109GainWholeGeometry
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open HeckePrimeRay HeckeDetectorZeros Cycle61Moment
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance sourceSlotEnvelopeFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem source_relative_slot_eq_ray (χ η₀ : Character) (θ : RayQuotient.Characters M H)
    (W : ℝ→ℂ) (b P σ freq : ℝ) (hP : 0<P) :
    naturalSlot χ (primePool M H b P)
      (fun K=>idealCoeff (relativeCharacter M H hH η₀ θ) K*HeckePrimeAnnular.annularWeight W P σ freq K) P=
    rayPrimePolynomial M H (χ.product (relativeCharacter M H hH η₀ θ).inverse.inverse) W b P σ freq := by
  unfold naturalSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow P hP]
  congr 1
  apply Finset.sum_congr rfl
  intro K hK
  simp only [idealCoeff_product,idealCoeff_inverse_conj,Complex.conj_conj]
  ring

/-- The ordinary root tail uses the actual buffered source envelope,
including its explicit amplitude-mesh loss and the empty-slot product. -/
theorem actual_source_slot_envelope
    (W : ℝ→ℂ) (lo hi Rwidth dmin dmax rmin τ ε e κ ηslot binWidth : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hRw : 0≤Rwidth) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ)
    (hηslot : 0≤ηslot) (hbin : 0<binWidth) (hbudget : 8*e*Rwidth+κ≤ε)
    (hgap : ε<rmin*binWidth) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧∀d : ℝ,dmin≤d →d≤dmax →2≤Z^d →2<Z^τ →
      ∀(χ η₀ : Character),∀hn : ∀j,(wholeSourceFamily M H hH η₀ χ j).residue≠1,
      ∀a : ℝ,∀i : ℕ,1/2≤2*a-1 →2*a-1≤3/4 →
      zeroMaximum (wholeSourceFamily M H hH η₀ χ) hn (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀(slots : Finset Slot)(w σ v : Slot→ℝ)(t : ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀s∈slots,rmin≤w s/d ∧ w s/d≤Rwidth) →
      (∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
      (∀s∈slots,∀θ',(twistedFamily M H hH (χ.product
        (relativeCharacter M H hH η₀ (θ s)).inverse.inverse) θ').modulus.absNorm≤Z^d) →
      (∀s∈slots,|t+v s|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^ηslot →
      let Q:=fun s=>naturalSlot χ (primePool M H 2 (Z^(w s)))
        (fun K=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) K*
          HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (t+v s) K) (Z^(w s));
      (∀s∈slots,‖Q s‖≤(Z^(w s))^((2*a-1)/2+binWidth)) ∧
      (∏s∈slots,max 1 (‖Q s‖^2))≤Z^(((2*a-1)+2*binWidth)*(∑s∈slots,w s)) := by
  have hamp := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W 1 2 (by norm_num) hWs hW
    Rwidth dmin dmax rmin τ ε e κ ηslot binWidth lo hi hRw hdmin hdmax hrmin hτ hε he he' hκ hηslot hbin hbudget hgap
  filter_upwards [hamp,eventually_gt_atTop (1:ℝ)] with Z hamp hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' hbase hT χ η₀ hn a i ha ha' hnext slots w σ v t θ hw hσlo hσhi hmod hfreq hheight Q
  have hdpos : 0<d := hdmin.trans_le hd
  have hwpos (s : Slot) (hs : s∈slots) : 0<w s :=
    (mul_pos hrmin hdpos).trans_le ((le_div_iff₀ hdpos).mp (hw s hs).1)
  have hQ (s : Slot) (hs : s∈slots) : ‖Q s‖≤(Z^(w s))^((2*a-1)/2+binWidth) := by
    let ray:=χ.product (relativeCharacter M H hH η₀ (θ s)).inverse.inverse
    have hnray : ∀θ',(twistedFamily M H hH ray θ').residue≠1 := fun θ'=>hn (.inr (θ s,θ'))
    have hmax := LowBranch.zeroMaximum_subfamily (twistedFamily M H hH ray)
      (wholeSourceFamily M H hH η₀ χ) hnray hn (fun θ'=>Sum.inr (θ s,θ')) (fun _=>rfl)
      (3*(i+1:ℕ)*Z^τ)
    have hb := hamp d hd hd' hbase hT ray hnray a i (by linarith) (by linarith)
      (hmax.trans_lt hnext) (w s/d) (σ s) (t+v s) (hw s hs).1 (hw s hs).2
      (hσlo s hs) (hσhi s hs) (hmod s hs) (hfreq s hs) hheight
    rw [Record12518109Gain.prime_scale_rescale Z d (w s) (by linarith) hdpos] at hb
    dsimp only [Q]
    rw [source_relative_slot_eq_ray M H hH χ η₀ (θ s) W 2 (Z^(w s)) (σ s) (t+v s) (by positivity)]
    exact hb.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le
      (Real.one_le_rpow hZ.le (hwpos s hs).le) (by linarith [hb.2.1]))
  refine ⟨hQ,?_⟩
  calc
    _≤∏s∈slots,Z^(((2*a-1)+2*binWidth)*w s) := by
      apply Finset.prod_le_prod₀ (fun _ _=>zero_le_one.trans (le_max_left _ _))
      intro s hs
      apply max_le (Real.one_le_rpow hZ.le (by nlinarith [hwpos s hs]))
      have hb:=pow_le_pow_left₀ (norm_nonneg (Q s)) (hQ s hs) 2
      have he : ((Z^(w s))^((2*a-1)/2+binWidth))^2=Z^(((2*a-1)+2*binWidth)*w s) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤Z^(w s)),
          ←Real.rpow_mul (by linarith : 0≤Z)]
        congr 1
        ring
      exact hb.trans_eq he
    _=Z^(((2*a-1)+2*binWidth)*(∑s∈slots,w s)) := by
      rw [←Real.rpow_sum_of_pos (zero_lt_one.trans hZ),Finset.mul_sum]

end
end QRH.Record1252270103Source.NaturalLowDensity.WholeGeometry
