import Candidate.Cycle63.Moment.JointHighDensity
import Candidate.Cycle63.Physical.InitialMass.GeometryHighShell
import Candidate.Cycle63.Physical.InitialMass.SecondHighBins

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The binned count form of a family of rows: over the exponent bins of the rows, a weight of the bin times the number
of rows in the bin. -/
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
theorem binned_count_payment {κ : Type*} (labels : Finset κ) (x : κ→Fin 4→ℝ) (width : ℝ)
    (weight : (Fin 4→ℤ)→ℝ) (Bbox δ Z C₀ Ccount target reserve loss rest : ℝ)
    (hw : 0<width) (hZ : 1≤Z) (hC₀ : 0≤C₀) (hCcount : 0≤Ccount)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4)
    (hx : ∀l∈labels,∀j,-Bbox≤x l j ∧ x l j≤Bbox)
    (hpoint : ∀l∈labels,highExponentValue δ (x l)≤target-reserve)
    (hweight : ∀key,weight key≤C₀*Z^(exponentBinUpper width key 0+δ*exponentBinUpper width key 3+rest))
    (hcount : ∀key∈labels.image (fun l=>exponentBin width (x l)),
      ((labels.filter (fun l=>exponentBin width (x l)=key)).card:ℝ)≤
        Ccount*Z^(exponentBinUpper width key 1+exponentBinUpper width key 2*unmarkedDensity δ+loss)) :
    binnedCount labels x width weight≤
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (C₀*Ccount*Z^(target-reserve+4*width+loss+rest)) := by
  unfold binnedCount
  have hZ0 : 0<Z := by linarith
  have hbins := exponent_bins_card labels x width Bbox hw hx
  have hterm : ∀key∈labels.image (fun l=>exponentBin width (x l)),
      weight key*((labels.filter (fun l=>exponentBin width (x l)=key)).card:ℝ)≤
        C₀*Ccount*Z^(target-reserve+4*width+loss+rest) := by
    intro key hkey
    obtain ⟨l₀,hl₀,hk₀⟩ := Finset.mem_image.mp hkey
    have hpay := high_bin_reserve_transfer width δ target reserve hw hδ (x l₀) (hpoint l₀ hl₀)
    rw [hk₀] at hpay
    have hcard0 : (0:ℝ)≤((labels.filter (fun l=>exponentBin width (x l)=key)).card:ℝ) := Nat.cast_nonneg _
    have hA : 0≤C₀*Z^(exponentBinUpper width key 0+δ*exponentBinUpper width key 3+rest) := by positivity
    have hpow : Z^(exponentBinUpper width key 0+δ*exponentBinUpper width key 3+rest)*
        Z^(exponentBinUpper width key 1+exponentBinUpper width key 2*unmarkedDensity δ+loss)=
        Z^(highExponentValue δ (exponentBinUpper width key)+loss+rest) := by
      rw [← Real.rpow_add hZ0]
      congr 1
      unfold highExponentValue
      ring
    calc weight key*((labels.filter (fun l=>exponentBin width (x l)=key)).card:ℝ)
        ≤ C₀*Z^(exponentBinUpper width key 0+δ*exponentBinUpper width key 3+rest)*
          ((labels.filter (fun l=>exponentBin width (x l)=key)).card:ℝ) :=
          mul_le_mul_of_nonneg_right (hweight key) hcard0
      _ ≤ C₀*Z^(exponentBinUpper width key 0+δ*exponentBinUpper width key 3+rest)*
          (Ccount*Z^(exponentBinUpper width key 1+exponentBinUpper width key 2*unmarkedDensity δ+loss)) :=
          mul_le_mul_of_nonneg_left (hcount key hkey) hA
      _ = C₀*Ccount*Z^(highExponentValue δ (exponentBinUpper width key)+loss+rest) := by
          rw [← hpow]
          ring
      _ ≤ C₀*Ccount*Z^(target-reserve+4*width+loss+rest) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc ∑key∈labels.image (fun l=>exponentBin width (x l)),
        weight key*((labels.filter (fun l=>exponentBin width (x l)=key)).card:ℝ)
      ≤ ∑_key∈labels.image (fun l=>exponentBin width (x l)),C₀*Ccount*Z^(target-reserve+4*width+loss+rest) :=
        Finset.sum_le_sum hterm
    _ = ((labels.image (fun l=>exponentBin width (x l))).card:ℝ)*
          (C₀*Ccount*Z^(target-reserve+4*width+loss+rest)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hbins) (by positivity)

/-- High shell energy of a set of physical geometric rows with outside weights at most `Z^U0` and raw volumes at most
`U3`: at most the pointwise bound times the number of rows. The rows are counted by the caller. -/
theorem actual_geometry_high_shell_upper {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l)),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (a rawError allowance Kcontrol T U0 U3 : ℝ) (i : ℕ),
      4/5 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      Function.Injective key →
      ∀(labels : Finset κ)(coeff : κ→ℝ),
      (∀l∈labels,coeff l≤Z^U0) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l)),
      (i:ℝ)≤Z^P.τ →
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(C₁ R₁ : κ→ Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      Real.logb Z (preVolume s.toData)≤Araw → pad≤allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀j,0≤w j) → (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤(2*a-1)*U3+rawError) →
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^(U0+(2*a-1)*U3+rawError+allowance)*labels.card  := by
  obtain ⟨bound,hbound,hselected⟩ := actual_geometry_selected_high_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ ε hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hselected P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s R seed K ξ hK bin column datum first row hfirst
    left unit hf rawKey key a rawError allowance Kcontrol T U0 U3 i ha ha' hKcontrol hT
    hinj labels coeff hcoeff st hQM hQη z hz hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  have hzpos : 0<Z := by linarith [he.1]
  let shell := fun l=>∑L∈Ds l,∑alloc∈(src l).toSource.active L,
    retainedAllocationCost (src l) L alloc (z l)
  have hshell0 (l : κ) : 0≤ shell l := Finset.sum_nonneg (fun L _=>
    Finset.sum_nonneg (fun alloc _=>retained_allocation_cost_nonneg _ _ _ _))
  have hshellBound := he.2 reflected second s R seed K ξ hK bin column datum first row hfirst
    a ((2*a-1)*U3+rawError) allowance Kcontrol T i ha ha' hKcontrol hT hinj labels st hQM hQη z hz
    hi hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ E R₂ pick t w σ v θ p Ds cap Araw
    hcap hmatches hscales hAraw hpadallow hf₂ hstateMask hwidth hradial hupper hw hwr hσlo hσhi
    hfreq hplainfreq hW hDs hdyad hcontrol hledger
  calc (∑l∈labels,coeff l*shell l)
      ≤ ∑l∈labels,Z^U0*shell l := Finset.sum_le_sum (fun l hl=>
        mul_le_mul_of_nonneg_right (hcoeff l hl) (hshell0 l))
    _ = Z^U0*(∑l∈labels,shell l) := (Finset.mul_sum _ _ _).symm
    _ ≤ Z^U0*(C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^((2*a-1)*U3+rawError+allowance)*labels.card) :=
        mul_le_mul_of_nonneg_left hshellBound (Real.rpow_nonneg hzpos.le _)
    _ = _ := by
        rw [show U0+(2*a-1)*U3+rawError+allowance=U0+((2*a-1)*U3+rawError+allowance) by ring,
          Real.rpow_add hzpos U0 ((2*a-1)*U3+rawError+allowance)]
        ring

/-- Finite-bin transport of the high shell energy of the physical geometric rows: the energy is at most the sum over
the exponent bins of the pointwise bound at the bin's upper edges times the number of rows of the bin. The rows of a
bin are counted by the caller. -/
theorem actual_geometry_binned_high_transport {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l)),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (a rawError allowance Kcontrol T width : ℝ) (i : ℕ),
      4/5 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0<width →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ),
      (∀l∈labels,coeff l≤Z^(x l 0)) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l)),
      (i:ℝ)≤Z^P.τ →
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(C₁ R₁ : κ→ Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      Real.logb Z (preVolume s.toData)≤Araw → pad≤allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀j,0≤w j) → (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤(2*a-1)*x l 3+rawError) →
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      binnedCount labels x width (fun key=>C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
        Z^(exponentBinUpper width key 0+(2*a-1)*exponentBinUpper width key 3+rawError+allowance)) := by
  obtain ⟨bound,hbound,hupper⟩ := actual_geometry_high_shell_upper
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ ε hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hupper P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s R seed K ξ hK bin column datum first row hfirst
    left unit hf rawKey key a rawError allowance Kcontrol T width i ha ha' hKcontrol hT hwidthbin
    hinj labels x coeff hcoeff st hQM hQη z hz hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupperZero hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  have hZ : 1<Z := by linarith [he.1]
  have hd0 : 0≤2*a-1 := by linarith
  let shell := fun l=>∑L∈Ds l,∑alloc∈(src l).toSource.active L,
    retainedAllocationCost (src l) L alloc (z l)
  let keys := labels.image (fun l=>exponentBin width (x l))
  have hsplit : (∑l∈labels,coeff l*shell l)=
      ∑key∈keys,∑l∈labels.filter (fun l=>exponentBin width (x l)=key),coeff l*shell l :=
    (Finset.sum_fiberwise_of_maps_to (fun l hl=>Finset.mem_image.mpr ⟨l,hl,rfl⟩) _).symm
  change (∑l∈labels,coeff l*shell l)≤_
  unfold binnedCount
  rw [hsplit]
  refine Finset.sum_le_sum (fun key _=>?_)
  let rows := labels.filter (fun l=>exponentBin width (x l)=key)
  have hrow' (l : κ)(hl : l∈rows) : l∈labels := (Finset.mem_filter.mp hl).1
  have hround (l : κ)(hl : l∈rows)(j : Fin 4) :
      x l j≤exponentBinUpper width key j := by
    have hh:=exponent_bin_enclosure width hwidthbin (x l) j
    rw [(Finset.mem_filter.mp hl).2] at hh
    exact hh.1
  exact he.2 reflected second s R seed K ξ hK bin column datum first row hfirst
    a rawError allowance Kcontrol T (exponentBinUpper width key 0) (exponentBinUpper width key 3) i
    ha ha' hKcontrol hT hinj rows coeff
    (fun l hl=>(hcoeff l (hrow' l hl)).trans (Real.rpow_le_rpow_of_exponent_le hZ.le (hround l hl 0)))
    st hQM hQη z hz hi hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁
    (fun l hl=>hf₁ l (hrow' l hl)) E R₂ pick t w σ v θ p Ds cap Araw
    hcap hmatches hscales hAraw hpadallow (fun l hl=>hf₂ l (hrow' l hl))
    (fun l hl=>hstateMask l (hrow' l hl)) (fun l hl=>hwidth l (hrow' l hl))
    (fun l hl=>hradial l (hrow' l hl)) (fun l hl=>hupperZero l (hrow' l hl))
    hw hwr hσlo hσhi
    (fun l hl=>hfreq l (hrow' l hl)) (fun l hl=>hplainfreq l (hrow' l hl))
    (fun l hl=>hW l (hrow' l hl)) (fun l hl=>hDs l (hrow' l hl))
    (fun l hl=>hdyad l (hrow' l hl)) (fun l hl=>hcontrol l (hrow' l hl)) (by
      intro l hl
      have hh:=hledger l (hrow' l hl)
      have hr:=mul_le_mul_of_nonneg_left (hround l hl 3) hd0
      linarith)

end
end OAI.SevenEighths.Cycle63InitialMass
