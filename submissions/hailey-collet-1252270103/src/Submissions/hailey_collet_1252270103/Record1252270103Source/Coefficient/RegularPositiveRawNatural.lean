/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The actual natural-row dictionary is the OpenAI/math masked coefficient law;
the uniform conductor and truncated-height bounds are from Cycle61. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularPositiveRaw
import Submissions.hailey_collet_1252270103.Cycle61.Moment.WholeSourceConductor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeSlots
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open ConcretePrimeRowBridge ConcreteTraceCRT Cycle61Moment
local notation "O" => HeckeFamily.O

/-- Exact slot dictionary; coefficient zeros and the enlarged puncture remain. -/
theorem positive_raw_natural_slot {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R ≠ 0) (pool : Finset (Ideal O))
    (β : Ideal O → ℂ) (P t : ℝ) :
    normalizedSlot η (fixedBadMask * idealGenerator R) 1 z pool β t P =
      naturalSlot (excluded F.character R) pool (heightCoefficient β t) P := by
  unfold normalizedSlot naturalSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR]
  simp only [heightCoefficient, one_mul]
  ring

theorem positive_raw_max_square (x : ℝ) (hx : 0 ≤ x) :
    max 1 (x ^ 2) = (max 1 x) ^ 2 := by
  by_cases h : x ≤ 1
  · rw [max_eq_left h, max_eq_left (by nlinarith : x ^ 2 ≤ 1)]
    norm_num
  · have hh : 1 ≤ x := le_of_not_ge h
    rw [max_eq_right hh, max_eq_right (by nlinarith : 1 ≤ x ^ 2)]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- One eventual threshold covers all actual natural states and all positive
shorter scales. The bin uses the actual enlarged-puncture character. -/
theorem eventual_natural_positive_raw (ap bp : ℝ) (hap : 0 < ap) :
    ∃ bound : ℕ → ℝ, (∀ k, 0 < bound k) ∧
    ∀ P : HighSourceParameters, P.profileBound = bound →
    8 * P.τ ≤ P.d * P.vslot → 16 * P.τ ≤ P.d * P.vplain →
    ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (st : NaturalState Z P.Bmask P.bΦ)
      (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
      (z : O) (hz : st.radial.keep z),
    st.width ≤ P.Mcap → st.radial.profile (‖eisEmbedding z‖ ^ 2 / st.radial.scale) ≠ 0 →
    ∀ (a : ℝ) (i : ℕ), 51 / 100 ≤ a → a ≤ 1 → (i : ℝ) ≤ Z ^ P.τ →
    HeckeDetectorZeros.zeroMaximum
      (wholeSourceFamily M H hH η₀
        (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture))
      (whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _)
        (3 * (i + 1 : ℕ) * Z ^ P.τ) < a + 2 * P.e →
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (scales : ι → ℝ),
    (∀ k, 0 < scales k) →
    ∀ (p : Profiles ap bp) (X : Fin 2 → ℝ) (t : ℝ),
    (∀ k, 0 < X k) → (∀ k, X k ≤ Z ^ (P.d * P.Rplain)) →
    |t| + Z ^ P.τ / 2 ≤ (3 * i + 2 : ℕ) * Z ^ P.τ →
    ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
      pool β scales t (X 0) (X 1)‖ ^ 2 ≤
    C * (p.control T) ^ 2 * (X 0 * X 1) ^ (2 * a - 1) * Z ^ (2 * P.εplain * P.d) *
      (∏ k, max 1 ‖naturalSlot
        (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)
        (pool k) (heightCoefficient (β k) t) (scales k)‖) ^ 2 := by
  obtain ⟨bound, hbound, hraw⟩ := buffered_positive_raw ap bp hap
  refine ⟨bound, hbound, ?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨T, C, hC, hraw⟩ := hraw P hboundeq
  refine ⟨T, C, hC, ?_⟩
  intro η₀
  have hc := eventual_whole_source_conductor M H hH η₀ P.bΦ P.Mcap P.Bmask P.margin
    P.hbΦ P.hmargin
  have hh := eventually_high_truncated_heights P 0 (2 * P.τ) hslot hplain (by norm_num)
  have hT : ∀ᶠ Z : ℝ in atTop, 2 < Z ^ P.τ :=
    (tendsto_rpow_atTop P.hτ).eventually (eventually_gt_atTop _)
  filter_upwards [hc, hh, hT] with Z hc hh hT
  refine ⟨hc.1, ?_⟩
  intro st hQM hQη z hz hwidth hradial a i ha ha' hi hupper
    ι _ _ pool β scales hscales p X t hX hcap hfreq
  let F := naturalRow st.character z (st.row_ne_zero z hz)
  let χ := wholeSourceFamily M H hH η₀ (excluded F.character st.puncture)
  have hχ := whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz F
  have hcoeff (I : Ideal O) : idealCoeff st.character I *
      CanonicalRowCompletion.idealRowHom (st.mask ^ 6 * (1 * z)) I =
        idealCoeff (χ (Sum.inl ())) I := by
    simpa only [NaturalState.mask, one_mul, χ, wholeSourceFamily, Sum.elim_inl] using
      (F.masked_ideal st.puncture st.puncture_ne_zero I).symm
  have hmod : ((χ (Sum.inl ())).modulus.absNorm : ℝ) ≤ Z ^ P.d :=
    (hc.2 st hwidth z F hradial (Sum.inl ())).trans
      (Real.rpow_le_rpow_of_exponent_le hc.1.le P.hdsupply)
  have hclip (k : Fin 2) : clippedScale (X k) ≤ Z ^ (P.d * P.Rplain) :=
    max_le (Real.one_le_rpow hc.1.le (mul_nonneg P.hd.le P.hRp)) (hcap k)
  have hb := hraw Z hc.1 hT χ hχ a i ha ha' hupper (Sum.inl ())
    st.character st.mask z hcoeff pool β scales hscales p X t hX hclip hmod
    hfreq (hh.2 i hi).2.1
  apply hb.trans_eq
  congr 1
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro k hk
  rw [show st.mask = fixedBadMask * idealGenerator st.puncture from rfl,
    positive_raw_natural_slot F st.puncture st.puncture_ne_zero,
    positive_raw_max_square _ (norm_nonneg _)]

/-- Re-expression in the actual raw logarithmic volume used by the scalar ledger. -/
theorem positive_raw_scale_exponent (Z X Y ν ε d : ℝ)
    (hZ : 1 < Z) (hX : 0 < X) (hY : 0 < Y) :
    (X * Y) ^ ν * Z ^ (2 * ε * d) =
      Z ^ (ν * Real.logb Z (X * Y) + 2 * ε * d) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  rw [Real.rpow_add hZp]
  congr 1
  rw [mul_comm ν, Real.rpow_mul hZp.le,
    Real.rpow_logb hZp hZ.ne' (mul_pos hX hY)]

#print axioms positive_raw_natural_slot
#print axioms positive_raw_max_square
#print axioms eventual_natural_positive_raw
#print axioms positive_raw_scale_exponent
end
end OAI.SevenEighths.Record1252270103Source
