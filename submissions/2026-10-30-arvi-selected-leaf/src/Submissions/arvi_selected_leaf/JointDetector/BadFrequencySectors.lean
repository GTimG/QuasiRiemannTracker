/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators

/-! Exhaustive bad-place sectors for nonzero Poisson frequencies.
A chosen section permits exact finite reindexing without assuming uniqueness
of a parametrization. Its eventual section selector is common to every row.
-/

namespace Qrh.JointDetector.BadFrequencySectors
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CanonicalRowCompletion CubicEisenstein EisensteinEmbedding ConcreteTraceCRT

abbrev O := ActualEisensteinCubic.O
abbrev SupportedIdeal := {H : Ideal O // Supported H}
abbrev NonzeroFrequency := {h : O // h ≠ 0}

structure Sector where
  unit : Oˣ
  lambdaPower : ℕ
  twoPower : ℕ
  source : SupportedIdeal

def decode (s : Sector) : O :=
  s.unit.val * lambda ^ s.lambdaPower * (2 : O) ^ s.twoPower *
    primaryGenerator s.source.val

theorem decode_ne_zero (s : Sector) : decode s ≠ 0 := by
  unfold decode
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero s.unit.ne_zero
    (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero))
    (pow_ne_zero _ (by norm_num)))
    (supported_primaryGenerator_ne_zero s.source.val s.source.property)

def decoded (s : Sector) : NonzeroFrequency := ⟨decode s, decode_ne_zero s⟩

theorem decoded_surjective : Function.Surjective decoded := by
  intro h
  obtain ⟨u, a, b, r, hs, _, hh⟩ := exists_supported_numerator_factorization h.val h.property
  have hg := supported_primaryGenerator_ne_zero (Ideal.span {r}) hs
  have hspan := (primaryGenerator_spec (Ideal.span {r}) hg).1
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨⟨u * v, a, b, ⟨Ideal.span {r}, hs⟩⟩, Subtype.ext ?_⟩
  change (u * v).val * lambda ^ a * (2 : O) ^ b * primaryGenerator (Ideal.span {r}) = h.val
  calc
    _ = u.val * lambda ^ a * (2 : O) ^ b *
      (primaryGenerator (Ideal.span {r}) * v.val) := by
        simp only [Units.val_mul]
        ring
    _ = u.val * lambda ^ a * (2 : O) ^ b * r := by rw [hv]
    _ = h.val := hh.symm

def choose (h : NonzeroFrequency) : Sector := Classical.choose (decoded_surjective h)

theorem decoded_choose (h : NonzeroFrequency) : decoded (choose h) = h :=
  Classical.choose_spec (decoded_surjective h)

theorem decode_choose (h : NonzeroFrequency) : decode (choose h) = h.val :=
  congrArg Subtype.val (decoded_choose h)

theorem choose_injective : Function.Injective choose :=
  Function.LeftInverse.injective decoded_choose

/-- Exact finite reindex. No frequency, bad prime, or unit state is discarded. -/
theorem sum_choose (F : Finset NonzeroFrequency) (f : O → ℂ) :
    (∑ h ∈ F, f h.val) = ∑ s ∈ F.image choose, f (decode s) := by
  rw [Finset.sum_image (fun _ _ _ _ h => choose_injective h)]
  apply Finset.sum_congr rfl
  intro h _
  exact congrArg (fun h : NonzeroFrequency => f h.val) (decoded_choose h).symm

theorem decode_norm (s : Sector) :
    ‖eisEmbedding (decode s)‖ ^ 2 =
      (3 : ℝ) ^ s.lambdaPower * (4 : ℝ) ^ s.twoPower *
        (Ideal.absNorm s.source.val : ℝ) := by
  have hlam : ‖eisEmbedding (s.unit.val * lambda ^ s.lambdaPower)‖ ^ 2 =
      (3 : ℝ) ^ s.lambdaPower := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span, ramifiedElement_absNorm,
      Nat.cast_pow, Nat.cast_ofNat]
  have hsource : ‖eisEmbedding (primaryGenerator s.source.val)‖ ^ 2 =
      (Ideal.absNorm s.source.val : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,
      (primaryGenerator_spec s.source.val
        (supported_primaryGenerator_ne_zero s.source.val s.source.property)).1]
  have htwo : ((2 : ℝ) ^ s.twoPower) ^ 2 = (4 : ℝ) ^ s.twoPower := by
    rw [← pow_mul, Nat.mul_comm s.twoPower 2, pow_mul]
    norm_num
  have he : ‖eisEmbedding (decode s)‖ =
      ‖eisEmbedding (s.unit.val * lambda ^ s.lambdaPower)‖ *
        (2 : ℝ) ^ s.twoPower * ‖eisEmbedding (primaryGenerator s.source.val)‖ := by
    simp only [decode, map_mul, norm_mul, map_pow, map_ofNat, norm_pow,
      Complex.norm_ofNat]
  rw [he]
  calc
    _ = ‖eisEmbedding (s.unit.val * lambda ^ s.lambdaPower)‖ ^ 2 *
      ((2 : ℝ) ^ s.twoPower) ^ 2 * ‖eisEmbedding (primaryGenerator s.source.val)‖ ^ 2 := by ring
    _ = _ := by rw [hlam, htwo, hsource]

theorem source_norm_one_le (s : Sector) : 1 ≤ (Ideal.absNorm s.source.val : ℝ) := by
  have h : 0 < Ideal.absNorm s.source.val := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr s.source.property.1)
  exact_mod_cast h

theorem bad_scale_le {s : Sector} {T : ℝ} (hT : ‖eisEmbedding (decode s)‖ ^ 2 ≤ T) :
    (3 : ℝ) ^ s.lambdaPower * (4 : ℝ) ^ s.twoPower ≤ T := by
  rw [decode_norm] at hT
  have h := mul_le_mul_of_nonneg_left (source_norm_one_le s)
    (by positivity : 0 ≤ (3 : ℝ) ^ s.lambdaPower * (4 : ℝ) ^ s.twoPower)
  simpa only [mul_one] using h.trans hT

theorem lambdaPower_le_log {s : Sector} {T : ℝ}
    (hT : ‖eisEmbedding (decode s)‖ ^ 2 ≤ T) :
    s.lambdaPower ≤ Nat.log 2 (Nat.ceil T) := by
  have h2 : (2 : ℝ) ^ s.lambdaPower ≤ (3 : ℝ) ^ s.lambdaPower :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h4 : 1 ≤ (4 : ℝ) ^ s.twoPower := one_le_pow₀ (by norm_num)
  have hm : (3 : ℝ) ^ s.lambdaPower ≤
      (3 : ℝ) ^ s.lambdaPower * (4 : ℝ) ^ s.twoPower := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ (3 : ℝ) ^ s.lambdaPower)
  have hpow : (2 : ℝ) ^ s.lambdaPower ≤ T :=
    h2.trans (hm.trans (bad_scale_le hT))
  have hn : 2 ^ s.lambdaPower ≤ Nat.ceil T := by
    exact_mod_cast hpow.trans (Nat.le_ceil T)
  exact Nat.le_log_of_pow_le (by decide) hn

theorem twoPower_le_log {s : Sector} {T : ℝ}
    (hT : ‖eisEmbedding (decode s)‖ ^ 2 ≤ T) :
    s.twoPower ≤ Nat.log 2 (Nat.ceil T) := by
  have h2 : (2 : ℝ) ^ s.twoPower ≤ (4 : ℝ) ^ s.twoPower :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h3 : 1 ≤ (3 : ℝ) ^ s.lambdaPower := one_le_pow₀ (by norm_num)
  have hm : (4 : ℝ) ^ s.twoPower ≤
      (3 : ℝ) ^ s.lambdaPower * (4 : ℝ) ^ s.twoPower := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ (4 : ℝ) ^ s.twoPower)
  have hpow : (2 : ℝ) ^ s.twoPower ≤ T :=
    h2.trans (hm.trans (bad_scale_le hT))
  have hn : 2 ^ s.twoPower ≤ Nat.ceil T := by
    exact_mod_cast hpow.trans (Nat.le_ceil T)
  exact Nat.le_log_of_pow_le (by decide) hn

local instance : Fintype Oˣ := by
  letI : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

def key (s : Sector) : Oˣ × ℕ × ℕ := (s.unit, s.lambdaPower, s.twoPower)

def boundedKeys (T : ℝ) : Finset (Oˣ × ℕ × ℕ) :=
  Finset.univ.product ((Finset.range (Nat.log 2 (Nat.ceil T) + 1)).product
    (Finset.range (Nat.log 2 (Nat.ceil T) + 1)))

theorem chosen_keys_subset (F : Finset NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ F, ‖eisEmbedding h.val‖ ^ 2 ≤ T) :
    (F.image choose).image key ⊆ boundedKeys T := by
  intro k hk
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hs
  have hbound : ‖eisEmbedding (decode (choose h))‖ ^ 2 ≤ T := by
    rw [decode_choose]
    exact hT h hh
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (lambdaPower_le_log hbound))
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (twoPower_le_log hbound))

/-- The number of bad-prime/unit sectors is logarithmic squared, uniformly
in the selected rows. No source-ideal count is charged here. -/
theorem chosen_keys_card (F : Finset NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ F, ‖eisEmbedding h.val‖ ^ 2 ≤ T) :
    ((F.image choose).image key).card ≤
      Fintype.card Oˣ * (Nat.log 2 (Nat.ceil T) + 1) ^ 2 := by
  calc
    _ ≤ (boundedKeys T).card := Finset.card_le_card (chosen_keys_subset F T hT)
    _ = _ := by
      unfold boundedKeys
      simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
        Finset.card_range]
      ring

def rebuild (k : Oˣ × ℕ × ℕ) (H : SupportedIdeal) : Sector :=
  ⟨k.1, k.2.1, k.2.2, H⟩

theorem rebuild_key_source (s : Sector) : rebuild (key s) s.source = s := by
  cases s
  rfl

theorem source_inj_on_key (k : Oˣ × ℕ × ℕ) :
    Set.InjOn Sector.source {s : Sector | key s = k} := by
  intro s hs t ht hsource
  have he : key s = key t := hs.trans ht.symm
  cases s with
  | mk u a b H =>
    cases t with
    | mk v c d J =>
      simp only [key, Prod.mk.injEq] at he
      rcases he with ⟨hu, ha, hb⟩
      cases hu
      cases ha
      cases hb
      cases hsource
      rfl

def fiberSources (F : Finset NonzeroFrequency) (k : Oˣ × ℕ × ℕ) :
    Finset SupportedIdeal :=
  ((F.image choose).filter (fun s => key s = k)).image Sector.source

theorem sum_fiber_sources (F : Finset NonzeroFrequency) (k : Oˣ × ℕ × ℕ)
    (f : O → ℂ) :
    (∑ s ∈ (F.image choose).filter (fun s => key s = k), f (decode s)) =
      ∑ H ∈ fiberSources F k, f (decode (rebuild k H)) := by
  unfold fiberSources
  have hinj : Set.InjOn Sector.source ((F.image choose).filter (fun s => key s = k)) := by
    intro s hs t ht he
    exact source_inj_on_key k (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2 he
  rw [Finset.sum_image (s := (F.image choose).filter (fun s => key s = k)) hinj]
  apply Finset.sum_congr rfl
  intro s hs
  have he := rebuild_key_source s
  rw [(Finset.mem_filter.mp hs).2] at he
  exact congrArg (fun s => f (decode s)) he.symm

/-- Every nonzero frequency in the original finite cutoff is assigned exactly
once. The good source sets are common to all rows, while every bad-prime and
unit state remains explicit. The key universe has the proved logarithmic cost. -/
theorem sum_by_bounded_sectors (F : Finset NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ F, ‖eisEmbedding h.val‖ ^ 2 ≤ T) (f : O → ℂ) :
    (∑ h ∈ F, f h.val) =
      ∑ k ∈ boundedKeys T, ∑ H ∈ fiberSources F k, f (decode (rebuild k H)) := by
  rw [sum_choose]
  have hm : ∀ s ∈ F.image choose, key s ∈ boundedKeys T := by
    intro s hs
    exact chosen_keys_subset F T hT (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun s : Sector => f (decode s))]
  apply Finset.sum_congr rfl
  intro k _
  exact sum_fiber_sources F k f

theorem fiberSource_frequency (F : Finset NonzeroFrequency) (k : Oˣ × ℕ × ℕ)
    (H : SupportedIdeal) (hH : H ∈ fiberSources F k) :
    ∃ h ∈ F, decode (rebuild k H) = h.val := by
  obtain ⟨s, hs, hsource⟩ := Finset.mem_image.mp hH
  obtain ⟨hsF, hkey⟩ := Finset.mem_filter.mp hs
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hsF
  refine ⟨h, hh, ?_⟩
  have he := rebuild_key_source (choose h)
  rw [hkey, hsource] at he
  rw [he, decode_choose]

theorem fiberSource_norm_le (F : Finset NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ F, ‖eisEmbedding h.val‖ ^ 2 ≤ T)
    (k : Oˣ × ℕ × ℕ) (H : SupportedIdeal) (hH : H ∈ fiberSources F k) :
    (3 : ℝ) ^ k.2.1 * (4 : ℝ) ^ k.2.2 * (Ideal.absNorm H.val : ℝ) ≤ T := by
  obtain ⟨h, hh, he⟩ := fiberSource_frequency F k H hH
  have hn := decode_norm (rebuild k H)
  rw [he] at hn
  change ‖eisEmbedding h.val‖ ^ 2 =
    (3 : ℝ) ^ k.2.1 * (4 : ℝ) ^ k.2.2 * (Ideal.absNorm H.val : ℝ) at hn
  rw [← hn]
  exact hT h hh

abbrev NonzeroSourceIdeal := {I : Ideal O // I ≠ 0}

def sourceFrequency (I : NonzeroSourceIdeal) : NonzeroFrequency :=
  ⟨ConcretePrimeRowBridge.idealGenerator I.val,
    ConcretePrimeRowBridge.idealGenerator_ne_zero I.val I.property⟩

theorem span_sourceFrequency (I : NonzeroSourceIdeal) :
    Ideal.span {(sourceFrequency I).val} = I.val :=
  ConcretePrimeRowBridge.span_idealGenerator I.val

theorem sourceFrequency_injective : Function.Injective sourceFrequency := by
  intro I J h
  apply Subtype.ext
  have he := congrArg (fun h : NonzeroFrequency => Ideal.span {h.val}) h
  simpa only [span_sourceFrequency] using he

def keyFactor (k : Oˣ × ℕ × ℕ) : O := k.1.val * lambda ^ k.2.1 * (2 : O) ^ k.2.2

def keyIdeal (k : Oˣ × ℕ × ℕ) : Ideal O := Ideal.span {keyFactor k}

theorem span_decode_rebuild (k : Oˣ × ℕ × ℕ) (H : SupportedIdeal) :
    Ideal.span {decode (rebuild k H)} = keyIdeal k * H.val := by
  change Ideal.span {keyFactor k * primaryGenerator H.val} = _
  rw [← Ideal.span_singleton_mul_span_singleton,
    (primaryGenerator_spec H.val (supported_primaryGenerator_ne_zero H.val H.property)).1]
  rfl

theorem sourceFrequency_norm (I : NonzeroSourceIdeal) :
    ‖eisEmbedding (sourceFrequency I).val‖ ^ 2 = (Ideal.absNorm I.val : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, span_sourceFrequency]

/-- Input ordinary ideals have the same exhaustive bad-place split. It is
not legitimate to discard their2-parts merely because the good source is
supported. This exact identity retains them as a frozen ideal multiplier. -/
theorem sum_ideals_by_bounded_sectors (F : Finset NonzeroSourceIdeal) (T : ℝ)
    (hT : ∀ I ∈ F, (Ideal.absNorm I.val : ℝ) ≤ T) (f : Ideal O → ℂ) :
    (∑ I ∈ F, f I.val) =
      ∑ k ∈ boundedKeys T,
        ∑ H ∈ fiberSources (F.image sourceFrequency) k, f (keyIdeal k * H.val) := by
  have hf : (∑ I ∈ F, f I.val) =
      ∑ h ∈ F.image sourceFrequency, f (Ideal.span {h.val}) := by
    rw [Finset.sum_image sourceFrequency_injective.injOn]
    simp only [span_sourceFrequency]
  have hbound : ∀ h ∈ F.image sourceFrequency, ‖eisEmbedding h.val‖ ^ 2 ≤ T := by
    intro h hh
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hh
    rw [sourceFrequency_norm]
    exact hT I hI
  rw [hf, sum_by_bounded_sectors (F.image sourceFrequency) T hbound
    (fun h : O => f (Ideal.span {h}))]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro H _
  rw [span_decode_rebuild]

theorem idealRow_source_sector (row : O) (k : Oˣ × ℕ × ℕ) (H : SupportedIdeal) :
    idealRowHom row (keyIdeal k * H.val) =
      idealRowHom row (keyIdeal k) * idealRowHom row H.val :=
  map_mul _ _ _

theorem idealRow_sector_multiplier_norm (row : O) (k : Oˣ × ℕ × ℕ) :
    ‖idealRowHom row (keyIdeal k)‖ ≤ 1 := idealRowHom_norm _ _

end
end Qrh.JointDetector.BadFrequencySectors

#print axioms Qrh.JointDetector.BadFrequencySectors.sum_by_bounded_sectors
#print axioms Qrh.JointDetector.BadFrequencySectors.fiberSource_norm_le
#print axioms Qrh.JointDetector.BadFrequencySectors.sum_ideals_by_bounded_sectors
