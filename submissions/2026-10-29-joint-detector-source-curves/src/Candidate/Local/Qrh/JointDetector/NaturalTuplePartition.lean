/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalPositiveGram
import Candidate.Local.Qrh.JointDetector.NaturalPivotBall

/-! Six norm dyads and five fixed residue classes for the actual tuple set.
The sixth dyad controls the WHOLE radical, so the common Mellin coordinate
lies in [1,2]. Every cell is an intersection with the original tuple set.
-/
namespace Qrh.JointDetector.NaturalSelectedNorm.TuplePartition
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve ConcretePrimeRowBridge
open IdealMobiusDivisorSum CompletedGauss CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O

abbrev RayClass := O ⧸ (Ideal.span {(36:O)} : Ideal O)
instance : Finite RayClass := Ring.HasFiniteQuotients.finiteQuotient
  (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (36:O) ≠ 0))
instance : Fintype RayClass := Fintype.ofFinite _

abbrev Key (Y : ℝ) := (Fin 5 → Fin (columnDyadicLength Y+1)) ×
  Fin (columnDyadicLength Y+1) × (Fin 5 → RayClass)

def radical (c : ColourTuple) : Ideal O := ∏ j, c j

def normIndex (Y : ℝ) (I : Ideal O) : Fin (columnDyadicLength Y+1) :=
  ⟨min (Nat.log 2 (Ideal.absNorm I)) (columnDyadicLength Y),
    Nat.lt_succ_of_le (min_le_right _ _)⟩

def key (Y : ℝ) (c : ColourTuple) : Key Y :=
  ⟨fun j => normIndex Y (c j), normIndex Y (radical c),
    fun j => Ideal.Quotient.mk _ (primaryGenerator (c j))⟩

def cell (F : Finset ColourTuple) (Y : ℝ) (k : Key Y) : Finset ColourTuple :=
  F.filter fun c => key Y c=k

def colourScale {Y : ℝ} (k : Key Y) (j : Fin 5) : ℝ := 2^(k.1 j).val
def radicalScale {Y : ℝ} (k : Key Y) : ℝ := 2^k.2.1.val

theorem radical_ne_zero (c : ColourTuple) (hc : ∀ j, Admissible (c j)) :
    radical c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (hc j).1)

theorem radical_dvd_weighted (c : ColourTuple) : radical c ∣ weightedIdeal c := by
  unfold radical weightedIdeal NaturalRowColours.colourProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro j hj
  exact dvd_pow_self _ (by omega : j.val+1 ≠ 0)

theorem norms_le_height (c : ColourTuple) (hc : ∀ j, Admissible (c j))
    (Y : ℝ) (hY : ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) :
    (∀ j, (Ideal.absNorm (c j):ℝ) ≤ Y) ∧ (Ideal.absNorm (radical c):ℝ) ≤ Y := by
  have hsp : Ideal.span {tupleRow c}=weightedIdeal c := by
    rw [tupleRow_eq_primary]
    exact (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _
      (tuple_weighted_supported c hc))).1
  rw [hsp] at hY
  have hn : weightedIdeal c ≠ 0 := (tuple_weighted_supported c hc).1
  have hrad : (Ideal.absNorm (radical c):ℝ) ≤ Y :=
    (norm_le_of_dvd hn (radical_dvd_weighted c)).trans hY
  refine ⟨?_,hrad⟩
  intro j
  exact (norm_le_of_dvd (radical_ne_zero c hc)
    (Finset.dvd_prod_of_mem (fun j => c j) (Finset.mem_univ j))).trans hrad

theorem normIndex_val (Y : ℝ) (I : Ideal O) (hI : (Ideal.absNorm I:ℝ) ≤ Y) :
    (normIndex Y I).val=Nat.log 2 (Ideal.absNorm I) :=
  min_eq_left (NaturalPivotBall.log_norm_le_length Y I hI)

theorem normIndex_bounds (Y : ℝ) (I : Ideal O) (hI : I ≠ 0)
    (hIY : (Ideal.absNorm I:ℝ) ≤ Y) :
    (Ideal.absNorm I:ℝ) ∈ Set.Icc ((2:ℝ)^(normIndex Y I).val)
      (2*(2:ℝ)^(normIndex Y I).val) := by
  rw [normIndex_val Y I hIY]
  have hpos : 0 < Ideal.absNorm I := by exact_mod_cast norm_pos hI
  constructor
  · exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos)
  · have hh : (Ideal.absNorm I:ℝ) < (2:ℝ)^(Nat.log 2 (Ideal.absNorm I)+1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Ideal.absNorm I)
    simpa only [pow_succ,mul_comm] using hh.le

theorem colourScale_pos {Y : ℝ} (k : Key Y) (j : Fin 5) : 0 < colourScale k j := by
  unfold colourScale
  positivity

theorem radicalScale_pos {Y : ℝ} (k : Key Y) : 0 < radicalScale k := by
  unfold radicalScale
  positivity

theorem cell_colour_bounds (F : Finset ColourTuple) (Y : ℝ) (k : Key Y)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hY : ∀ c ∈ F, ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (c : ColourTuple) (hc : c ∈ cell F Y k) (j : Fin 5) :
    (Ideal.absNorm (c j):ℝ) ∈ Set.Icc (colourScale k j) (2*colourScale k j) := by
  obtain ⟨hcF,hck⟩ := Finset.mem_filter.mp hc
  have he : normIndex Y (c j)=k.1 j := congrArg (fun k : Key Y => k.1 j) hck
  have hh := normIndex_bounds Y (c j) (hF c hcF j).1
    ((norms_le_height c (hF c hcF) Y (hY c hcF)).1 j)
  simpa only [he,colourScale] using hh

theorem cell_radical_bounds (F : Finset ColourTuple) (Y : ℝ) (k : Key Y)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hY : ∀ c ∈ F, ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (c : ColourTuple) (hc : c ∈ cell F Y k) :
    (Ideal.absNorm (radical c):ℝ) ∈ Set.Icc (radicalScale k) (2*radicalScale k) := by
  obtain ⟨hcF,hck⟩ := Finset.mem_filter.mp hc
  have he : normIndex Y (radical c)=k.2.1 := congrArg (fun k : Key Y => k.2.1) hck
  have hh := normIndex_bounds Y (radical c) (radical_ne_zero c (hF c hcF))
    (norms_le_height c (hF c hcF) Y (hY c hcF)).2
  simpa only [he,radicalScale] using hh

theorem cell_radical_coordinate (F : Finset ColourTuple) (Y : ℝ) (k : Key Y)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hY : ∀ c ∈ F, ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (c : ColourTuple) (hc : c ∈ cell F Y k) :
    (Ideal.absNorm (radical c):ℝ)/radicalScale k ∈ Set.Icc (1:ℝ) 2 := by
  have hh := cell_radical_bounds F Y k hF hY c hc
  exact ⟨(le_div_iff₀ (radicalScale_pos k)).mpr (by simpa using hh.1),
    (div_le_iff₀ (radicalScale_pos k)).mpr hh.2⟩

/-- The lower dyadic pivot anchor is bounded by the original natural height.
No balance or independence of the five colours is assumed. -/
theorem cell_anchor_le_height (F : Finset ColourTuple) (Y : ℝ) (k : Key Y)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hY : ∀ c ∈ F, ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (c : ColourTuple) (hc : c ∈ cell F Y k) :
    colourScale k 0*(∏ j : Fin 4, colourScale k j.succ)^2 ≤ Y := by
  have hcF := (Finset.mem_filter.mp hc).1
  have hsp : Ideal.span {tupleRow c}=weightedIdeal c := by
    rw [tupleRow_eq_primary]
    exact (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _
      (tuple_weighted_supported c (hF c hcF)))).1
  have hheight : (Ideal.absNorm (weightedIdeal c):ℝ) ≤ Y := by
    simpa only [hsp] using hY c hcF
  have hanchor := norm_le_of_dvd (tuple_weighted_supported c (hF c hcF)).1
    (NaturalRowColours.pivot_anchor_dvd c)
  have hanchor' : (Ideal.absNorm (c 0):ℝ)*
      (Ideal.absNorm (NaturalRowColours.higherProduct c):ℝ)^2 ≤ Y := by
    have hh : (Ideal.absNorm (c 0):ℝ)*
        (Ideal.absNorm (NaturalRowColours.higherProduct c):ℝ)^2 ≤ (Ideal.absNorm (weightedIdeal c):ℝ) := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hanchor
    exact hh.trans hheight
  have hV : (∏ j : Fin 4, colourScale k j.succ) ≤
      (Ideal.absNorm (NaturalRowColours.higherProduct c):ℝ) := by
    simp only [NaturalRowColours.higherProduct,map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun j _ => (colourScale_pos k j.succ).le)
      (fun j _ => (cell_colour_bounds F Y k hF hY c hc j.succ).1)
  have hV0 : 0 ≤ ∏ j : Fin 4, colourScale k j.succ :=
    Finset.prod_nonneg fun j _ => (colourScale_pos k j.succ).le
  exact (mul_le_mul (cell_colour_bounds F Y k hF hY c hc 0).1
    (pow_le_pow_left₀ hV0 hV 2) (sq_nonneg _)
    (Nat.cast_nonneg _)).trans hanchor'

theorem cell_same_ray (F : Finset ColourTuple) (Y : ℝ) (k : Key Y)
    (c d : ColourTuple) (hc : c ∈ cell F Y k) (hd : d ∈ cell F Y k) (j : Fin 5) :
    primaryGenerator (c j)-primaryGenerator (d j) ∈ (Ideal.span {(36:O)} : Ideal O) := by
  have he := (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2.symm
  have hr := congrArg (fun k : Key Y => k.2.2 j) he
  exact Ideal.Quotient.eq.mp hr

theorem cell_rows_same_ray (F : Finset ColourTuple) (Y : ℝ) (k : Key Y)
    (c d : ColourTuple) (hc : c ∈ cell F Y k) (hd : d ∈ cell F Y k) :
    tupleRow c-tupleRow d ∈ (Ideal.span {(36:O)} : Ideal O) := by
  apply Ideal.Quotient.eq.mp
  simp only [tupleRow,map_prod,map_pow]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Ideal.Quotient.eq.mpr (cell_same_ray F Y k c d hc hd j)]

theorem cell_selects {N : ℕ} (d : SelectedSlotData N) (Z : ℝ)
    (F : Finset ColourTuple) (Y : ℝ) (k : Key Y)
    (hs : d.Selects Z (F.image tupleRow)) : d.Selects Z ((cell F Y k).image tupleRow) := by
  intro z hz i
  exact hs z (Finset.image_subset_image (Finset.filter_subset _ _) hz) i

private theorem sum_biUnion_nonneg_le {T U : Type*} [DecidableEq U]
    (labels : Finset T) (S : T → Finset U) (f : U → ℝ) (hf : ∀ u, 0 ≤ f u) :
    ∑ u ∈ labels.biUnion S, f u ≤ ∑ t ∈ labels, ∑ u ∈ S t, f u := by
  induction labels using Finset.induction_on with
  | empty => simp
  | @insert t ts ht ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ht]
    have hh := Finset.sum_union_inter (s₁:=S t) (s₂:=ts.biUnion S) (f:=f)
    have hn : 0 ≤ ∑ u ∈ S t ∩ ts.biUnion S, f u := Finset.sum_nonneg fun u _ => hf u
    linarith

/-- Image overlap is harmless: the proof sums nonnegative primal energies.
No injectivity of tuple presentations or entrywise kernel comparison is used. -/
theorem selectedNorm_image_partition_le {ι κ : Type*} [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (F : Finset ι) (f : ι → O) (label : ι → κ)
    (S : Finset (Ideal O)) (K : ℝ) (hK : 0 ≤ K)
    (hcell : ∀ k, selectedNorm ((F.filter fun c => label c=k).image f) S ≤ K) :
    selectedNorm (F.image f) S ≤ (Fintype.card κ:ℝ)*K := by
  let rows := fun k => (F.filter fun c => label c=k).image f
  have hcover : F.image f=Finset.univ.biUnion rows := by
    ext z
    simp only [Finset.mem_image,Finset.mem_biUnion,Finset.mem_univ,true_and,rows,Finset.mem_filter]
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact ⟨label c,c,⟨hc,rfl⟩,rfl⟩
    · rintro ⟨k,c,⟨hc,_⟩,rfl⟩
      exact ⟨c,hc,rfl⟩
  apply SlotHistogram.selectedNorm_le_of_primal_energy _ _ _ (by positivity)
  intro a
  rw [hcover,Finset.sum_coe_sort _ (fun z => ‖ordinaryPolynomial S a z‖^2)]
  calc
    _ ≤ ∑ k, ∑ z ∈ rows k, ‖ordinaryPolynomial S a z‖^2 :=
      sum_biUnion_nonneg_le Finset.univ rows _ (fun z => sq_nonneg _)
    _ ≤ ∑ _k : κ, K*(∑ I : S, ‖a I‖^2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← Finset.sum_coe_sort (rows k) (fun z => ‖ordinaryPolynomial S a z‖^2)]
      exact (ordinaryPolynomial_energy (rows k) S a).trans
        (mul_le_mul_of_nonneg_right (hcell k) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = _ := by simp [mul_assoc]

theorem selectedNorm_partition_le (F : Finset ColourTuple) (Y : ℝ)
    (S : Finset (Ideal O)) (K : ℝ) (hK : 0 ≤ K)
    (hcell : ∀ k : Key Y, selectedNorm ((cell F Y k).image tupleRow) S ≤ K) :
    selectedNorm (F.image tupleRow) S ≤ (Fintype.card (Key Y):ℝ)*K :=
  selectedNorm_image_partition_le F tupleRow (key Y) S K hK hcell

theorem key_card (Y : ℝ) : Fintype.card (Key Y)=
    (columnDyadicLength Y+1)^6*(Fintype.card RayClass)^5 := by
  simp only [Key,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  ring

theorem key_card_small_power (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z Y : ℝ, 1 ≤ Z → 1 ≤ Y → Y ≤ Z^A →
      (Fintype.card (Key Y):ℝ) ≤ C*Z^ε := by
  let D : ℝ := 2+A/((ε/6)*Real.log 2)
  let Q : ℝ := (Fintype.card RayClass:ℝ)^5
  have hD : 0 < D := by dsimp [D]; positivity
  have hQ : 0 < Q := by
    dsimp [Q]
    exact pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  refine ⟨D^6*Q,mul_pos (pow_pos hD _) hQ,?_⟩
  intro Z Y hZ hY hYA
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hlog : columnDyadicLength Y ≤ columnDyadicLength (Z^A) := by
    unfold columnDyadicLength
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
    exact Real.log_le_log (by linarith) hYA
  have hcard : (columnDyadicLength Y+1:ℝ) ≤ D*Z^(ε/6) := by
    have hh : (columnDyadicLength Y+1:ℝ) ≤ (columnDyadicLength (Z^A)+1:ℝ) := by
      exact_mod_cast Nat.add_le_add_right hlog 1
    exact hh.trans (NaturalScalarBudget.dyadic_shell_card_le Z A (ε/6) hZ hA (by positivity))
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (columnDyadicLength Y+1:ℝ)) hcard 6
  have hexp : (Z^(ε/6))^6=Z^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hZ0.le]
    congr 1
    norm_num
  rw [key_card]
  push_cast
  calc
    _ ≤ (D*Z^(ε/6))^6*Q := mul_le_mul_of_nonneg_right hpow hQ.le
    _ = (D^6*Q)*Z^ε := by rw [mul_pow,hexp]; ring

end
end Qrh.JointDetector.NaturalSelectedNorm.TuplePartition

#print axioms Qrh.JointDetector.NaturalSelectedNorm.TuplePartition.selectedNorm_partition_le
#print axioms Qrh.JointDetector.NaturalSelectedNorm.TuplePartition.key_card_small_power
