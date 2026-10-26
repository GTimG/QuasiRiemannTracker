import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.DeletionAnnular
import Submissions.hailey_collet_1252270103.LocalMoment.RawSixthDensity

/- Raw-root slot transport adapted from PR63 DeletionRawSlots.lean and the
holes_with_root_norm lemma in DeletionGeometry.lean; Apache-2.0.
Only the used algebraic closure is imported; physical geometry is unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Record12518109GainDeletion
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily HeckePrimeAnnular
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

theorem holes_with_root_norm (R A : Ideal O) (U b a : ℝ) (hU : 0 < U)
    (hR : (R.absNorm : ℝ) ≤ U^b) (hA : (A.absNorm : ℝ) ≤ U^a) :
    ((R*A).absNorm : ℝ) ≤ U^(b+a) := by
  simp only [map_mul,Nat.cast_mul]
  rw [Real.rpow_add hU]
  exact mul_le_mul hR hA (Nat.cast_nonneg _) (Real.rpow_nonneg hU.le _)

/-- Above a fixed positive width, raw sixth-power rows and the common
unmasked core slot differ by at most one half, uniformly in both masks. -/
theorem eventually_raw_slot_comparison (W : ℝ → ℂ)
    (a b lo hi Bmask Broot wmin : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin) :
    ∀ᶠU : ℝ in atTop,1<U ∧
      ∀(η ν : Character)(u : FreeRow)(B : NZIdeal)(R : Ideal O),R≠0 →
      (R.absNorm : ℝ)≤U^Bmask → (B.val.absNorm : ℝ)≤U^Broot →
      ∀(pool : Finset (Ideal O)),(∀I∈pool,Prime I) →
      ∀(w σ v t : ℝ),wmin≤w → lo≤σ → σ≤hi →
      let F := naturalRow η u.val u.property.1
      let Fr := naturalRow η (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property
      let β := heightCoefficient (fun I=>idealCoeff ν I*annularWeight W (U^w) σ v I) t
      ‖naturalSlot (excluded Fr.character R) pool β (U^w)-
        naturalSlot F.character pool β (U^w)‖≤1/2 := by
  filter_upwards [eventually_annular_deletion_half W a b lo hi (Broot+Bmask) wmin
    ha hWs hW (add_nonneg hBroot hBmask) hwmin] with U hU
  refine ⟨hU.1,?_⟩
  intro η ν u B R hR hRN hBN pool hp w σ v t hw hσlo hσhi F Fr β
  have hg : ConcretePrimeRowBridge.idealGenerator B.val≠0 :=
    ConcretePrimeRowBridge.idealGenerator_ne_zero B.val B.property
  have he : naturalSlot (excluded Fr.character R) pool β (U^w)=
      naturalSlot (excluded F.character (B.val*R)) pool β (U^w) := by
    apply naturalSlot_congr_ideal
    intro I
    have hh := naturalRow_sixth_masked_ideal F
      (ConcretePrimeRowBridge.idealGenerator B.val) hg Fr R hR I
    rwa [ConcretePrimeRowBridge.span_idealGenerator] at hh
  rw [he]
  exact hU.2 F.character ν (B.val*R) (mul_ne_zero B.property hR)
    (holes_with_root_norm B.val R U Broot Bmask (zero_lt_one.trans hU.1) hBN hRN)
    pool hp w σ v t hw hσlo hσhi

/-- The actual raw row norm bounds its sixth-root ideal, independently
of any source representation or coprimality condition. -/
theorem raw_root_norm_cap (u : FreeRow) (B : NZIdeal) (U : ℝ)
    (hrow : rawFrequencyNorm (sixthFrequencyEquiv (u,B))≤U) :
    (B.val.absNorm : ℝ)≤U^(1/6:ℝ) := by
  have hNp : 0<(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hpow : (B.val.absNorm : ℝ)^6≤U := by
    rw [raw_sixth_norm] at hrow
    exact (le_mul_of_one_le_left (pow_nonneg hNp.le _) (rowNorm_ge_one u)).trans hrow
  calc
    _ = ((B.val.absNorm : ℝ)^6)^(1/6:ℝ) := by
      rw [←Real.rpow_natCast_mul hNp.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (pow_nonneg hNp.le _) hpow (by norm_num)

/-- The maximum-with-one convention makes comparison stable even when a
slot falls below the amplitude threshold after deleting primes. -/
theorem max_slot_product_comparison {ι : Type*} (S : Finset ι) (Q Q₀ : ι → ℂ)
    (hclose : ∀i∈S,‖Q i-Q₀ i‖≤1/2) :
    (∏i∈S,max 1 ‖Q i‖)^2 ≤ (4:ℝ)^S.card*(∏i∈S,max 1 ‖Q₀ i‖)^2 := by
  have hp : (∏i∈S,max 1 ‖Q i‖) ≤ (2:ℝ)^S.card*(∏i∈S,max 1 ‖Q₀ i‖) := by
    calc
      _ ≤ ∏i∈S,2*max 1 ‖Q₀ i‖ := Finset.prod_le_prod₀
        (fun i _=>(zero_le_one.trans (le_max_left _ _)))
        (fun i hi=>max_amplitude_of_deletion_error (hclose i hi))
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]
  have hpow := pow_le_pow_left₀
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _))) hp 2
  rw [mul_pow,←pow_mul] at hpow
  have he : ((2:ℝ)^S.card)^2=(4:ℝ)^S.card := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rw [←pow_mul] at he
  rwa [he] at hpow

/-- The raw weight of literal normalized slots is controlled by the
common core amplitudes at a cost independent of the number of rows. -/
theorem slot_product_comparison {ι : Type*} (S : Finset ι) (Q Q₀ : ι → ℂ)
    (hclose : ∀i∈S,‖Q i-Q₀ i‖≤1/2) :
    ‖∏i∈S,Q i‖^2 ≤ (4:ℝ)^S.card*(∏i∈S,max 1 ‖Q₀ i‖)^2 := by
  apply le_trans _ (max_slot_product_comparison S Q Q₀ hclose)
  rw [norm_prod]
  exact pow_le_pow_left₀ (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
    (Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun _ _=>le_max_right _ _)) 2

theorem max_square_eq (x : ℝ) (hx : 0≤x) : (max 1 x)^2=max 1 (x^2) := by
  by_cases h : x≤1
  · rw [max_eq_left h,max_eq_left (by nlinarith : x^2≤1)]
    norm_num
  · have hh : 1≤x := le_of_not_ge h
    rw [max_eq_right hh,max_eq_right (by nlinarith : 1≤x^2)]

theorem max_square_product_eq {ι : Type*} (S : Finset ι) (Q : ι→ℂ) :
    (∏s∈S,max 1 ‖Q s‖)^2=∏s∈S,max 1 (‖Q s‖^2) := by
  rw [←Finset.prod_pow]
  exact Finset.prod_congr rfl (fun s _=>max_square_eq _ (norm_nonneg _))

theorem raw_max_fiber_comparison {ι Row : Type*} (rows : Finset Row) (slots : Finset ι)
    (Q Q₀ : Row→ι→ℂ) (hclose : ∀u∈rows,∀s∈slots,‖Q u s-Q₀ u s‖≤1/2) :
    (∑u∈rows,∏s∈slots,max 1 (‖Q u s‖^2)) ≤
      (4:ℝ)^slots.card*(∑u∈rows,∏s∈slots,max 1 (‖Q₀ u s‖^2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hh := max_slot_product_comparison slots (Q u) (Q₀ u) (hclose u hu)
  simpa only [max_square_product_eq] using hh

theorem heightCoefficient_zero (β : Ideal O→ℂ) : heightCoefficient β 0=β := by
  funext I
  simp [heightCoefficient]

/-- Root and moving-hole uniformity applies directly to the rowwise common
height plus the independent slot height used by `NaturalBatch`. -/
theorem eventually_raw_max_family_comparison {Slot : Type*}
    (W : ℝ→ℂ) (a b lo hi Bmask Broot wmin : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin) :
    ∀ᶠU : ℝ in atTop,1<U ∧
      ∀(η : Character)(ν : Slot→Character)(B : NZIdeal)(R : FreeRow→Ideal O)
        (rows : Finset FreeRow)(slots : Finset Slot),
      (∀u∈rows,R u≠0) → (∀u∈rows,((R u).absNorm : ℝ)≤U^Bmask) →
      (B.val.absNorm : ℝ)≤U^Broot →
      ∀(pool : Slot→Finset (Ideal O)),(∀s∈slots,∀I∈pool s,Prime I) →
      ∀(w σ v : Slot→ℝ)(t : FreeRow→ℝ),
      (∀s∈slots,wmin≤w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤hi) →
      let rawQ := fun u s=>naturalSlot
        (excluded (naturalRow η (sixthFrequencyEquiv (u,B)).val
          (sixthFrequencyEquiv (u,B)).property).character (R u)) (pool s)
        (fun I=>idealCoeff (ν s) I*annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s));
      let coreQ := fun u s=>naturalSlot (naturalRow η u.val u.property.1).character (pool s)
        (fun I=>idealCoeff (ν s) I*annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s));
      (∑u∈rows,∏s∈slots,max 1 (‖rawQ u s‖^2)) ≤
        (4:ℝ)^slots.card*(∑u∈rows,∏s∈slots,max 1 (‖coreQ u s‖^2)) := by
  filter_upwards [eventually_raw_slot_comparison W a b lo hi Bmask Broot wmin
    ha hWs hW hBmask hBroot hwmin] with U hU
  refine ⟨hU.1,?_⟩
  intro η ν B R rows slots hR hRN hBN pool hp w σ v t hw hσlo hσhi rawQ coreQ
  apply raw_max_fiber_comparison rows slots rawQ coreQ
  intro u hu s hs
  have hh := hU.2 η (ν s) u B (R u) (hR u hu) (hRN u hu) hBN (pool s) (hp s hs)
    (w s) (σ s) (t u+v s) 0 (hw s hs) (hσlo s hs) (hσhi s hs)
  simpa only [heightCoefficient_zero] using hh


end
end OAI.SevenEighths.Record12518109GainDeletion
