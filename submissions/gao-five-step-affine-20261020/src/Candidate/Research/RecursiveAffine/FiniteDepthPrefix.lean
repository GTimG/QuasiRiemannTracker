/- Joint prefix counting for a literal finite history of affine source steps.
Apache-2.0; builds on PR67's ChildPrefix count, retaining all missing radicals. -/
import Candidate.Research.RecursiveAffine.NativeChildPrefix

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic Cycle63Moment
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- The multiplier after the actual two common transforms, with all ancestor factors retained. -/
def appendMultiplier {P : Type*} (v : P → O) (left : Bool)
    (unit : P → FirstSourceLabel → O) (x : P × ChildPrefix) : O :=
  childMultiplier left (v x.1) (unit x.1) x.2

/-- Only the genuinely missing first-source radical is added to the historical cost. -/
def stepMissing (left : Bool) (Z : ℝ) (p : ChildPrefix) : ℝ :=
  Real.logb Z ((firstSourceMissing left p.1).absNorm : ℝ)

structure StepFacts {P : Type*} (v : P → O) (left : Bool)
    (unit : P → FirstSourceLabel → O) (Z B : ℝ) (x : P × ChildPrefix) : Prop where
  nonzero : appendMultiplier v left unit x ≠ 0
  multiplier_cap : ((Ideal.span {appendMultiplier v left unit x}).absNorm : ℝ) ≤ Z^B
  supported : Supported x.2.1.1.1 ∧ x.2.1.1.2 ≠ 0 ∧ Supported x.2.2.1.1 ∧ x.2.2.1.2 ≠ 0
  same_support : primeSupport x.2.1.1.1 = primeSupport x.2.1.1.2 ∧
    primeSupport x.2.2.1.1 = primeSupport x.2.2.1.2
  row_cap : ((Ideal.span {appendMultiplier v left unit x}*firstSourceMissing left x.2.1).absNorm : ℝ) ≤ Z^B
  ideal_cap : (x.2.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.2.1.1.2.absNorm : ℝ) ≤ Z^B ∧
    (x.2.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (x.2.2.1.2.absNorm : ℝ) ≤ Z^B

/-- The literal ancestor multiplier divides the new one; no new dictionary is introduced. -/
theorem old_multiplier_dvd_append {P : Type*} (v : P → O) (left : Bool)
    (unit : P → FirstSourceLabel → O) (x : P × ChildPrefix) :
    v x.1 ∣ appendMultiplier v left unit x := by
  refine ⟨unit x.1 x.2.1*
    primeSubsetGenerator (fun P : CommonIndex x.2.1.1.1 x.2.1.1.2 => P.val) x.2.1.2.val*
    firstSourceNumerator left x.2.1*
    (commonFrequencyGenerator x.2.2.1.1 x.2.2.1.2*
      nonunitFrequencyGenerator x.2.2.1.1 x.2.2.1.2 x.2.2.2), ?_⟩
  dsimp only [appendMultiplier, childMultiplier]
  ring

theorem missing_ne_zero (left : Bool) (p : ChildPrefix) : firstSourceMissing left p.1 ≠ 0 := by
  intro h0
  apply CenteredMomentRankinRadical.commonRadical_ne_zero p.1.1.1 p.1.1.2
  rw [Cycle63Moment.actual_first_radical_partition p.1.1.1 p.1.1.2 p.1.2.val p.1.2.property left]
  change _*firstSourceMissing left p.1 = 0
  rw [h0, mul_zero]

theorem stepMissing_bounds {P : Type*} (v : P → O) (left : Bool)
    (unit : P → FirstSourceLabel → O) (Z B : ℝ) (hZ : 1 < Z)
    (x : P × ChildPrefix) (hx : StepFacts v left unit Z B x) :
    0 ≤ stepMissing left Z x.2 ∧ stepMissing left Z x.2 ≤ B := by
  have hm1 : (1 : ℝ) ≤ ((firstSourceMissing left x.2.1).absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (missing_ne_zero left x.2))
  have hv1 : (1 : ℝ) ≤ ((Ideal.span {appendMultiplier v left unit x}).absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hx.nonzero))
  have hcap := hx.row_cap
  rw [map_mul, Nat.cast_mul] at hcap
  have hmcap : ((firstSourceMissing left x.2.1).absNorm : ℝ) ≤ Z^B := by nlinarith
  exact ⟨Real.logb_nonneg hZ hm1,
    (Real.logb_le_iff_le_rpow hZ (by linarith : (0 : ℝ) < ((firstSourceMissing left x.2.1).absNorm : ℝ))).mpr hmcap⟩

/-- An appended literal history costs the SUM of historical missing logarithms, with coefficient one.
The constant is uniform before the source, units, finite histories and all moving variables.
The hypotheses are native support and norm facts, not another assumed count theorem. -/
theorem append_prefix_fibre_count (B Q loss : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {P : Type*} (v : P → O) (left : Bool)
      (unit : P → FirstSourceLabel → O) (oldMissing : P → ℝ) (Z : ℝ), 2 ≤ Z →
      ∀ (S : Finset (P × ChildPrefix)) (A : ℝ), 0 ≤ A →
      (∀ x ∈ S, StepFacts v left unit Z B x) →
      (∀ p ∈ S.image Prod.fst, 0 ≤ oldMissing p ∧ oldMissing p ≤ Q) →
      (∀ t : ℝ, ∀ D : Ideal O,
        ((((S.image Prod.fst).filter (fun p => oldMissing p ≤ t)).filter
          (fun p => Ideal.span {v p} = D)).card : ℝ) ≤ A*Z^t) →
      ∀ m : ℝ, ∀ D : Ideal O,
        ((S.filter (fun x => oldMissing x.1 + stepMissing left Z x.2 ≤ m ∧
          Ideal.span {appendMultiplier v left unit x} = D)).card : ℝ) ≤ C*A*Z^(m+loss) := by
  let w := loss/3
  have hw : 0 < w := by dsimp [w]; positivity
  obtain ⟨Cc, hCc, hc⟩ := child_prefix_count B w hB hw
  obtain ⟨Cd, hCd, hd⟩ := CenteredMomentMask.polynomial_mask_divisor_bound w B hw hB
  let bins : Finset ℤ := Finset.Icc ⌊(0 : ℝ)/w⌋ ⌊Q/w⌋
  refine ⟨((bins.card : ℝ)+1)*Cc*Cd, by positivity, ?_⟩
  intro P v left unit oldMissing Z hZ S A hA hfact hrange hparent m D
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 < Z := by linarith
  let F := S.filter (fun x => oldMissing x.1 + stepMissing left Z x.2 ≤ m ∧
    Ideal.span {appendMultiplier v left unit x} = D)
  have mem (x : P × ChildPrefix) (hx : x ∈ F) : x ∈ S ∧
      oldMissing x.1 + stepMissing left Z x.2 ≤ m ∧
      Ideal.span {appendMultiplier v left unit x} = D := Finset.mem_filter.mp hx
  rcases F.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · change (F.card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  have hD : D ≠ ⊥ := by
    rw [← (mem x₀ hx₀).2.2]
    exact Ideal.span_singleton_eq_bot.not.mpr (hfact x₀ (mem x₀ hx₀).1).nonzero
  have hDcap : (D.absNorm : ℝ) ≤ Z^B := by
    rw [← (mem x₀ hx₀).2.2]
    exact (hfact x₀ (mem x₀ hx₀).1).multiplier_cap
  let key := fun x : P × ChildPrefix => ⌊oldMissing x.1/w⌋
  have hbins : F.image key ⊆ bins := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    have hp := hrange x.1 (Finset.mem_image_of_mem Prod.fst (mem x hx).1)
    exact Finset.mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right hp.1 hw.le),
      Int.floor_mono (div_le_div_of_nonneg_right hp.2 hw.le)⟩
  have hbin (k : ℤ) : ((F.filter (fun x => key x = k)).card : ℝ) ≤ Cc*Cd*A*Z^(m+loss) := by
    let G := F.filter (fun x => key x = k)
    let parents := G.image Prod.fst
    let lo : ℝ := (k : ℝ)*w
    let hi : ℝ := ((k : ℝ)+1)*w
    have edges (x : P × ChildPrefix) (hx : x ∈ G) : lo ≤ oldMissing x.1 ∧ oldMissing x.1 ≤ hi := by
      have hk : key x = k := (Finset.mem_filter.mp hx).2
      have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (oldMissing x.1/w)) hw.le
      have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (oldMissing x.1/w)) hw
      rw [div_mul_cancel₀ _ hw.ne'] at hlo hhi
      change (⌊oldMissing x.1/w⌋ : ℤ) = k at hk
      rw [hk] at hlo hhi
      exact ⟨hlo, hhi.le⟩
    have hparents : (parents.card : ℝ) ≤ (idealDivisors D).card*(A*Z^hi) := by
      have hsub : parents ⊆ (idealDivisors D).biUnion (fun I => parents.filter (fun p => Ideal.span {v p} = I)) := by
        intro p hp
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
        refine Finset.mem_biUnion.mpr ⟨Ideal.span {v x.1}, ?_, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hx, rfl⟩⟩
        rw [mem_idealDivisors hD, ← (mem x (Finset.mem_filter.mp hx).1).2.2]
        rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
        exact old_multiplier_dvd_append v left unit x
      have hpf (I : Ideal O) : ((parents.filter (fun p => Ideal.span {v p} = I)).card : ℝ) ≤ A*Z^hi := by
        have hsub' : parents.filter (fun p => Ideal.span {v p} = I) ⊆
            ((S.image Prod.fst).filter (fun p => oldMissing p ≤ hi)).filter (fun p => Ideal.span {v p} = I) := by
          intro p hp
          obtain ⟨hpG, hpI⟩ := Finset.mem_filter.mp hp
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpG
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_image_of_mem _ (mem x (Finset.mem_filter.mp hx).1).1, (edges x hx).2⟩, hpI⟩
        exact (Nat.cast_le.mpr (Finset.card_le_card hsub')).trans (hparent hi I)
      calc (parents.card : ℝ)
          ≤ (((idealDivisors D).biUnion (fun I => parents.filter (fun p => Ideal.span {v p} = I))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ∑ I ∈ idealDivisors D, ((parents.filter (fun p => Ideal.span {v p} = I)).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _I ∈ idealDivisors D, A*Z^hi := Finset.sum_le_sum (fun I _ => hpf I)
        _ = (idealDivisors D).card*(A*Z^hi) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hchild (p : P) : ((G.filter (fun x => x.1 = p)).card : ℝ) ≤ Cc*Z^(m-lo+w) := by
      let over := G.filter (fun x => x.1 = p)
      have ov (x : P × ChildPrefix) (hx : x ∈ over) : x ∈ G ∧ x.1 = p := Finset.mem_filter.mp hx
      have inj : Set.InjOn Prod.snd (over : Set (P × ChildPrefix)) := by
        intro x hx y hy hxy
        exact Prod.ext ((ov x hx).2.trans (ov y hy).2.symm) hxy
      have hh := hc left (v p) (unit p) Z hZ D hD hDcap (m-lo) (over.image Prod.snd)
        (by
          intro c hc'
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
          have h := (mem x (Finset.mem_filter.mp (ov x hx).1).1).2.2
          change Ideal.span {childMultiplier left (v p) (unit p) x.2} = D
          rw [← (ov x hx).2]
          exact h)
        (by
          intro c hc'; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
          exact (hfact x (mem x (Finset.mem_filter.mp (ov x hx).1).1).1).supported)
        (by
          intro c hc'; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
          exact (hfact x (mem x (Finset.mem_filter.mp (ov x hx).1).1).1).same_support)
        (by
          intro c hc'; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
          have hf := hfact x (mem x (Finset.mem_filter.mp (ov x hx).1).1).1
          rw [← (mem x (Finset.mem_filter.mp (ov x hx).1).1).2.2]
          exact hf.row_cap)
        (by
          intro c hc'; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
          exact (hfact x (mem x (Finset.mem_filter.mp (ov x hx).1).1).1).ideal_cap)
        (by
          intro c hc'; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
          have hm := (mem x (Finset.mem_filter.mp (ov x hx).1).1).2.1
          have he := (edges x (ov x hx).1).1
          have hpos : (0 : ℝ) < ((firstSourceMissing left x.2.1).absNorm : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (missing_ne_zero left x.2))
          apply (Real.logb_le_iff_le_rpow hZ1 hpos).mp
          change stepMissing left Z x.2 ≤ m-lo
          linarith)
      rw [Finset.card_image_of_injOn inj] at hh
      exact hh
    have hfib := Finset.card_eq_sum_card_fiberwise (fun x (hx : x ∈ G) => Finset.mem_image_of_mem Prod.fst hx)
    have hd' := hd Z hZ1.le D hD hDcap
    calc ((G.card : ℕ) : ℝ)
        = ∑ p ∈ parents, ((G.filter (fun x => x.1 = p)).card : ℝ) := by exact_mod_cast hfib
      _ ≤ ∑ _p ∈ parents, Cc*Z^(m-lo+w) := Finset.sum_le_sum (fun p _ => hchild p)
      _ = (parents.card : ℝ)*(Cc*Z^(m-lo+w)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((idealDivisors D).card*(A*Z^hi))*(Cc*Z^(m-lo+w)) :=
          mul_le_mul_of_nonneg_right hparents (by positivity)
      _ ≤ ((Cd*Z^w)*(A*Z^hi))*(Cc*Z^(m-lo+w)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hd' (mul_nonneg hA (by positivity))
      _ = Cc*Cd*A*Z^(m+loss) := by
          have he : w+hi+(m-lo+w)=m+loss := by dsimp [w, hi, lo]; ring
          rw [show ((Cd*Z^w)*(A*Z^hi))*(Cc*Z^(m-lo+w)) =
            Cc*Cd*A*(Z^w*Z^hi*Z^(m-lo+w)) by ring]
          rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0, he]
  have hfib := Finset.card_eq_sum_card_fiberwise (fun x (hx : x ∈ F) => Finset.mem_image_of_mem key hx)
  change (F.card : ℝ) ≤ _
  calc (F.card : ℝ)
      = ∑ k ∈ F.image key, ((F.filter (fun x => key x = k)).card : ℝ) := by exact_mod_cast hfib
    _ ≤ ∑ _k ∈ F.image key, Cc*Cd*A*Z^(m+loss) := Finset.sum_le_sum (fun k _ => hbin k)
    _ = ((F.image key).card : ℝ)*(Cc*Cd*A*Z^(m+loss)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((bins.card : ℝ)+1)*(Cc*Cd*A*Z^(m+loss)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (Nat.cast_le.mpr (Finset.card_le_card hbins)).trans (by linarith)
    _ = (((bins.card : ℝ)+1)*Cc*Cd)*A*Z^(m+loss) := by ring

end
end OAI.SevenEighths.Cycle153JointCount
