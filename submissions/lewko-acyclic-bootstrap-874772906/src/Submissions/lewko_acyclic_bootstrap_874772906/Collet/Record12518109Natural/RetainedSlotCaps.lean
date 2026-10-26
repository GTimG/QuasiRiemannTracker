/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.SlotMaximumTransport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.HighSlots
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.WholeSourceDatum
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.HighParameters

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural.WeightedHigh
noncomputable section
open scoped Classical BigOperators ContDiff
open Cycle61Moment
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Buffered upper zeros cap every literal source slot, including slots
subsequently frozen by residual allocations. -/
theorem actual_retained_slot_caps (P : HighSourceParameters)
    (hslot : 8*P.τ≤P.d*P.vslot) (hplain : 16*P.τ≤P.d*P.vplain) :
    ∃C : ℝ,1≤C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(st : NaturalState Z P.Bmask P.bΦ),st.width≤P.Mcap→
      ∀(hQM : st.fixedModulus≤M)(hQη : st.fixedModulus≤η₀.modulus)
        (z : O)(hz : st.radial.keep z)(a : ℝ)(i : ℕ),
      51/100≤a→a≤1→(i:ℝ)≤Z^P.τ→
      st.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/st.radial.scale)≠0→
      HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture))
        (whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _)
        (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e→
      ∀(w σ t v : ℝ)(θ : RayQuotient.Characters M H),
      0≤w→w/P.d≤P.Rwidth→P.σmin≤σ→σ≤P.σmax→
      |t+v|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ→
      (max 1 ‖naturalSlot
        (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)
        (primePool M H P.B₀ (Z^w))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          annularWeight P.Wslot (Z^w) σ v I) t) (Z^w)‖)^2≤
        C*Z^((2*a-1)*w+2*P.εslot*P.d) := by
  obtain ⟨C,hC,hslots⟩:=actual_high_slots M H hH P.Wslot P.A₀ P.B₀ P.hA₀ P.hWs P.hW
    P.Rwidth P.dmax P.τ P.εslot P.e P.κ P.vslot P.σmin P.σmax
    P.bΦ P.Mcap P.Bmask P.margin P.d P.hRw P.hdmax P.hτ P.hεs P.he P.he'
    P.hκ P.hvs P.hslotBudget P.hbΦ P.hmargin P.hd P.hdsupply P.hdm
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro η₀
  filter_upwards [hslots η₀,eventually_high_truncated_heights P 0 (2*P.τ)
    hslot hplain (by norm_num)] with Z hZ hheight
  refine ⟨hZ.1,?_⟩
  intro st hwidth hQM hQη z hz a i ha ha' hi hradial hupper w σ t v θ hw hwr hlo hhi hfreq
  have hlow := whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz a P.e _ hradial hupper
  have hb:=hZ.2 st hwidth hQM hQη a i ha ha' w σ t v hw hwr hlo hhi hfreq
    (hheight.2 i hi).1 z hz hlow θ
  let amp := naturalSlot
    (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)
    (primePool M H P.B₀ (Z^w))
    (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
      annularWeight P.Wslot (Z^w) σ v I) t) (Z^w)
  have he : (max 1 C*Z^(2*P.εslot*P.d))*Z^((2*a-1)*w)=
      max 1 C*Z^((2*a-1)*w+2*P.εslot*P.d) := by
    rw [Real.rpow_add (zero_lt_one.trans hZ.1)]
    ring
  have hsq : ‖amp‖^2≤max 1 C*Z^((2*a-1)*w+2*P.εslot*P.d) := by
    dsimp only [amp]
    rw [←masked_natural_slot_eq (naturalRow st.character z (st.row_ne_zero z hz))
      st.puncture st.puncture_ne_zero]
    change ‖CenteredMomentWholeSlotDeletion.normalizedSlot st.character st.mask 1 z _ _ _ _‖^2≤_
    apply hb.trans
    rw [←he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) C)
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hone : (1:ℝ)≤max 1 C*Z^((2*a-1)*w+2*P.εslot*P.d) := by
    apply one_le_mul_of_one_le_of_one_le (le_max_left _ _)
    exact Real.one_le_rpow hZ.1.le (add_nonneg
      (mul_nonneg (by linarith) hw)
      (mul_nonneg (mul_nonneg (by norm_num) P.hεs.le) P.hd.le))
  by_cases h : ‖amp‖≤1
  · rw [max_eq_left h,one_pow]
    exact hone
  · rw [max_eq_right (le_of_not_ge h)]
    exact hsq

end
end OAI.SevenEighths.Record12518109Natural.WeightedHigh
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.actual_retained_slot_caps
