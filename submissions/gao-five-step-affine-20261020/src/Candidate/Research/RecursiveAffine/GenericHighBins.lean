/- Native generic binned-key counts, extracted without unrelated source-energy imports. Apache-2.0. -/
import Candidate.Cycle63.Moment.DepthTwoHighCountRows
import Candidate.Cycle63.Physical.InitialMass.DepthTwoReturnedCount
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment LocalMoment
open Cycle63InitialMass
def binnedCount {κ : Type*} (labels : Finset κ) (x : κ→Fin 4→ℝ) (width : ℝ) (weight : (Fin 4→ℤ)→ℝ) : ℝ :=
  ∑key∈labels.image (fun l=>exponentBin width (x l)),
    weight key*((labels.filter (fun l=>exponentBin width (x l)=key)).card:ℝ)

/-- The binned count form of the keys of a family of rows: over the exponent bins of the rows, a weight of the bin
times the number of keys of the rows in the bin. -/
def keyBinnedCount {κ K : Type*} (labels : Finset κ) (key : κ→K) (x : κ→Fin 4→ℝ) (width : ℝ)
    (weight : (Fin 4→ℤ)→ℝ) : ℝ :=
  ∑b∈labels.image (fun l=>exponentBin width (x l)),
    weight b*(((labels.filter (fun l=>exponentBin width (x l)=b)).image key).card:ℝ)

/-- With nonnegative weights the binned count form is nonnegative. -/
theorem binnedCount_nonneg {κ : Type*} (labels : Finset κ) (x : κ→Fin 4→ℝ) (width : ℝ)
    (weight : (Fin 4→ℤ)→ℝ) (hw : ∀b,0≤weight b) : 0≤binnedCount labels x width weight :=
  Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (Nat.cast_nonneg _)

/-- With nonnegative weights the binned count form of the keys is nonnegative. -/
theorem keyBinnedCount_nonneg {κ K : Type*} (labels : Finset κ) (key : κ→K) (x : κ→Fin 4→ℝ) (width : ℝ)
    (weight : (Fin 4→ℤ)→ℝ) (hw : ∀b,0≤weight b) : 0≤keyBinnedCount labels key x width weight :=
  Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (Nat.cast_nonneg _)

/-- The binned count form of the keys grows with the weights. -/
theorem keyBinnedCount_mono_weight {κ K : Type*} (labels : Finset κ) (key : κ→K) (x : κ→Fin 4→ℝ) (width : ℝ)
    (weight weight' : (Fin 4→ℤ)→ℝ) (h : ∀b,weight b≤weight' b) :
    keyBinnedCount labels key x width weight≤keyBinnedCount labels key x width weight' := by
  unfold keyBinnedCount
  exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (h b) (Nat.cast_nonneg _)

/-- With nonnegative weights the binned count form of a subfamily is at most that of the family. -/
theorem binnedCount_mono_labels {κ : Type*} {S labels : Finset κ} (hS : S⊆labels) (x : κ→Fin 4→ℝ) (width : ℝ)
    (weight : (Fin 4→ℤ)→ℝ) (hw : ∀b,0≤weight b) :
    binnedCount S x width weight≤binnedCount labels x width weight := by
  unfold binnedCount
  calc ∑b∈S.image (fun l=>exponentBin width (x l)),
        weight b*((S.filter (fun l=>exponentBin width (x l)=b)).card:ℝ)
      ≤ ∑b∈S.image (fun l=>exponentBin width (x l)),
        weight b*((labels.filter (fun l=>exponentBin width (x l)=b)).card:ℝ) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
          (by exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hS)) (hw b)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hS)
        (fun b _ _ => mul_nonneg (hw b) (Nat.cast_nonneg _))

/-- With nonnegative weights the binned count form of the keys of a subfamily is at most that of the family. -/
theorem keyBinnedCount_mono_labels {κ K : Type*} {S labels : Finset κ} (hS : S⊆labels) (key : κ→K)
    (x : κ→Fin 4→ℝ) (width : ℝ) (weight : (Fin 4→ℤ)→ℝ) (hw : ∀b,0≤weight b) :
    keyBinnedCount S key x width weight≤keyBinnedCount labels key x width weight := by
  unfold keyBinnedCount
  have hcard (b : Fin 4→ℤ) : (((S.filter (fun l=>exponentBin width (x l)=b)).image key).card:ℝ)≤
      (((labels.filter (fun l=>exponentBin width (x l)=b)).image key).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter _ hS))
  calc ∑b∈S.image (fun l=>exponentBin width (x l)),
        weight b*(((S.filter (fun l=>exponentBin width (x l)=b)).image key).card:ℝ)
      ≤ ∑b∈S.image (fun l=>exponentBin width (x l)),
        weight b*(((labels.filter (fun l=>exponentBin width (x l)=b)).image key).card:ℝ) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hcard b) (hw b)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hS)
        (fun b _ _ => mul_nonneg (hw b) (Nat.cast_nonneg _))

/-- With nonnegative weights the binned count form of a subfamily on which the key is injective is at most the binned
count form of the keys of the family. -/
theorem binnedCount_le_keyBinnedCount {κ K : Type*} {S labels : Finset κ} (hS : S⊆labels) (key : κ→K)
    (hinj : Set.InjOn key ↑S) (x : κ→Fin 4→ℝ) (width : ℝ) (weight : (Fin 4→ℤ)→ℝ) (hw : ∀b,0≤weight b) :
    binnedCount S x width weight≤keyBinnedCount labels key x width weight := by
  have hS' : binnedCount S x width weight=keyBinnedCount S key x width weight := by
    unfold binnedCount keyBinnedCount
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
  rw [hS']
  exact keyBinnedCount_mono_labels hS key x width weight hw

/-- The binned count form of a reindexed family is that of the image family, for a reindexing injective on the
rows. -/
theorem binnedCount_comp {κ κ' : Type*} (labels : Finset κ') (g : κ'→κ) (hg : Set.InjOn g ↑labels)
    (x : κ→Fin 4→ℝ) (width : ℝ) (weight : (Fin 4→ℤ)→ℝ) :
    binnedCount labels (fun l=>x (g l)) width weight=binnedCount (labels.image g) x width weight := by
  simp only [binnedCount]
  rw [Finset.image_image]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.filter_image, Finset.card_image_of_injOn (hg.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

/-- The binned count form of the keys of a reindexed family is that of the image family. -/
theorem keyBinnedCount_comp {κ κ' K : Type*} (labels : Finset κ') (g : κ'→κ) (key : κ→K) (x : κ→Fin 4→ℝ)
    (width : ℝ) (weight : (Fin 4→ℤ)→ℝ) :
    keyBinnedCount labels (fun l=>key (g l)) (fun l=>x (g l)) width weight=
      keyBinnedCount (labels.image g) key x width weight := by
  unfold keyBinnedCount
  rw [Finset.image_image]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.filter_image, Finset.image_image]
  rfl

/-- With nonnegative weights, the binned count form of the keys of a family reindexed into a family `T` is at most that
of `T`. -/
theorem keyBinnedCount_le_of_map {κ κ' K : Type*} (S : Finset κ') (T : Finset κ) (g : κ'→κ)
    (hg : ∀l∈S,g l∈T) (key : κ→K) (x : κ→Fin 4→ℝ) (width : ℝ) (weight : (Fin 4→ℤ)→ℝ) (hw : ∀b,0≤weight b) :
    keyBinnedCount S (fun l=>key (g l)) (fun l=>x (g l)) width weight≤keyBinnedCount T key x width weight := by
  rw [keyBinnedCount_comp]
  apply keyBinnedCount_mono_labels _ key x width weight hw
  intro y hy
  obtain ⟨l,hl,rfl⟩:=Finset.mem_image.mp hy
  exact hg l hl

/-- A constant factor of the weights comes out of the binned count of the keys. -/
theorem keyBinnedCount_const_mul {κ K : Type*} (S : Finset κ) (key : κ → K) (x : κ → Fin 4 → ℝ) (width c : ℝ)
    (weight : (Fin 4 → ℤ) → ℝ) :
    keyBinnedCount S key x width (fun b => c*weight b) = c*keyBinnedCount S key x width weight := by
  unfold keyBinnedCount
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- A common power `Z^a` of the weights comes out of the binned count of the keys. -/
theorem keyBinnedCount_rpow_shift {κ K : Type*} (S : Finset κ) (key : κ → K) (x : κ → Fin 4 → ℝ) (width Z a : ℝ)
    (hZ : 0<Z) (f : (Fin 4 → ℤ) → ℝ) :
    keyBinnedCount S key x width (fun b => Z^(f b+a)) = Z^a*keyBinnedCount S key x width (fun b => Z^(f b)) := by
  unfold keyBinnedCount
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  dsimp only
  rw [Real.rpow_add hZ]
  ring

/-- A binned count whose bins lie in a finite set `box` is the sum over `box` of the weight times the number of keys in
the bin. -/
theorem keyBinnedCount_eq_sum_box {κ K : Type*} (S : Finset κ) (key : κ → K) (x : κ → Fin 4 → ℝ) (width : ℝ)
    (weight : (Fin 4 → ℤ) → ℝ) (box : Finset (Fin 4 → ℤ)) (hbox : ∀ l ∈ S, exponentBin width (x l) ∈ box) :
    keyBinnedCount S key x width weight =
      ∑ b ∈ box, weight b*(((S.filter (fun l => exponentBin width (x l) = b)).image key).card : ℝ) := by
  unfold keyBinnedCount
  refine Finset.sum_subset (fun b hb => ?_) (fun b _ hb => ?_)
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hb
    exact hbox l hl
  · have hempty : S.filter (fun l => exponentBin width (x l) = b) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun l hl hlb => hb ?_
      exact Finset.mem_image.mpr ⟨l, hl, hlb⟩
    rw [hempty, Finset.image_empty, Finset.card_empty, Nat.cast_zero, mul_zero]

/-- A real function of the form `t ↦ ∑ i ∈ s, c i * n t i`, with natural numbers `n t i` at most `N` on `s`, attains its
maximum. -/
theorem exists_max_of_bounded_counts {I ι : Type*} [Nonempty I] (s : Finset ι) (c : ι → ℝ) (N : ℕ)
    (f : I → ℝ) (n : I → ι → ℕ) (hn : ∀ t, ∀ i ∈ s, n t i ≤ N)
    (hf : ∀ t, f t = ∑ i ∈ s, c i*(n t i : ℝ)) : ∃ t₀, ∀ t, f t ≤ f t₀ := by
  let Φ : (s → Fin (N+1)) → ℝ := fun v => ∑ i : s, c i*((v i : ℕ) : ℝ)
  have hsub : Set.range f ⊆ Set.range Φ := by
    rintro _ ⟨t, rfl⟩
    refine ⟨fun i => ⟨n t i, Nat.lt_succ_of_le (hn t i i.property)⟩, ?_⟩
    rw [hf t, ← Finset.sum_coe_sort s]
  obtain ⟨y, ⟨t₀, rfl⟩, hy⟩ := Set.exists_max_image (Set.range f) id ((Set.finite_range Φ).subset hsub)
    (Set.range_nonempty f)
  exact ⟨t₀, fun t => hy (f t) ⟨t, rfl⟩⟩

/-- Along any family of finite sets of rows, indexed by `I`, whose rows number at most `N` and whose row types have
their exponent bins in a fixed box `box`, the transport form over finitely many buffer bins attains its maximum. -/
theorem exists_max_key_transport {I ι K : Type*} [Nonempty I] [Fintype ι] [DecidableEq ι] (κ : I → Type*)
    (S : (t : I) → Finset (κ t)) (select : (t : I) → κ t → ι) (key : (t : I) → κ t → K)
    (x : (t : I) → κ t → Fin 4 → ℝ) (width : ℝ) (weight : ι → (Fin 4 → ℤ) → ℝ)
    (box : Finset (Fin 4 → ℤ)) (N : ℕ)
    (hbox : ∀ t, ∀ l, exponentBin width (x t l) ∈ box) (hcard : ∀ t, (S t).card ≤ N) :
    ∃ t₀, ∀ t, (∑ q, keyBinnedCount ((S t).filter (fun l => select t l = q)) (key t) (x t) width (weight q)) ≤
      ∑ q, keyBinnedCount ((S t₀).filter (fun l => select t₀ l = q)) (key t₀) (x t₀) width (weight q) := by
  let n : I → ι × (Fin 4 → ℤ) → ℕ := fun t i =>
    ((((S t).filter (fun l => select t l = i.1)).filter (fun l => exponentBin width (x t l) = i.2)).image (key t)).card
  refine exists_max_of_bounded_counts ((Finset.univ : Finset ι) ×ˢ box) (fun i => weight i.1 i.2) N _ n
    (fun t i _ => ?_) (fun t => ?_)
  · exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans
      ((Finset.card_filter_le _ _).trans (hcard t))
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact keyBinnedCount_eq_sum_box _ _ _ _ _ box fun l _ => hbox t l

/-- The level-one payment of a binned count form. Let every bin weight be at most `C₀ Z^(U₀ + δ U₃ + rest)` at the
bin's upper edges `U`, let the rows of every bin number at most `Ccount Z^(U₁ + U₂ ρ + loss)` with `ρ` the unmarked
density at `δ`, and let every row pay the target. Then the binned count form is at most the number of bins of the box
times `C₀ Ccount Z^(target - reserve + 4 width + loss + rest)`. -/

def highExponentValue (δ : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  x 0+x 1+unmarkedDensity δ*x 2+δ*x 3

theorem high_bin_reserve_transfer (width δ target reserve : ℝ) (hw : 0 < width)
    (hδ : 0 ≤ δ ∧ δ ≤ 3/4) (x : Fin 4 → ℝ)
    (hbound : highExponentValue δ x ≤ target-reserve) :
    highExponentValue δ (Cycle63InitialMass.exponentBinUpper width (Cycle63InitialMass.exponentBin width x)) ≤
      target-reserve+4*width := by
  have hr := Cycle63InitialMass.unmarkedDensity_lipschitz (δ₁:=δ) (δ₂:=δ) hδ.1 le_rfl hδ.2
  have hρ0 : 0 ≤ unmarkedDensity δ := hr.2.2.1
  have hρ1 : unmarkedDensity δ ≤ 1 := hr.2.2.2
  have h0 := (Cycle63InitialMass.exponent_bin_enclosure width hw x 0).2
  have h1 := (Cycle63InitialMass.exponent_bin_enclosure width hw x 1).2
  have h2 := mul_le_mul_of_nonneg_left (Cycle63InitialMass.exponent_bin_enclosure width hw x 2).2 hρ0
  have h3 := mul_le_mul_of_nonneg_left (Cycle63InitialMass.exponent_bin_enclosure width hw x 3).2 hδ.1
  have hρw := mul_le_mul_of_nonneg_right hρ1 hw.le
  have hdw := mul_le_mul_of_nonneg_right hδ.2 hw.le
  unfold highExponentValue at *
  nlinarith

end
end OAI.SevenEighths.Cycle153HighProvider
