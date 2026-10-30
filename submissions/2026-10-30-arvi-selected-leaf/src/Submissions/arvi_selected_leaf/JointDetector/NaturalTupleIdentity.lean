/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalSharedTables
import Submissions.arvi_selected_leaf.JointDetector.NaturalTupleFibres
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Forcing

/-! Uniqueness of the actual weighted natural colour tuple. Common prime
carriers then identify the exact principal quotient and off-diagonal zero mode. -/
namespace Qrh.JointDetector.NaturalTupleIdentity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open NaturalSelectedNorm NaturalRowColours FiveColourPoisson
open CenteredExceptionalCount UniqueFactorizationMonoid IdealMobiusDivisorSum
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

private theorem one_hot_code (a : Fin 5 → ℕ) (ha : ∑ j,a j ≤ 1)
    (j : Fin 5) (haj : a j ≠ 0) :
    (∀ k,a k=if k=j then 1 else 0) ∧ (∑ k,(k.val+1)*a k)=j.val+1 := by
  have hajle : a j ≤ 1 := (Finset.single_le_sum (fun k _ => Nat.zero_le (a k))
    (Finset.mem_univ j)).trans ha
  have haj1 : a j=1 := by omega
  have hsum := Finset.sum_erase_add Finset.univ a (Finset.mem_univ j)
  have hrest : (∑ k ∈ Finset.univ.erase j,a k)=0 := by omega
  have hzero (k : Fin 5) (hkj : k ≠ j) : a k=0 := by
    have hle := Finset.single_le_sum (s:=Finset.univ.erase j)
      (f:=a) (fun k _ => Nat.zero_le (a k)) (Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ k⟩)
    omega
  refine ⟨?_,?_⟩
  · intro k
    by_cases hk : k=j
    · simpa [hk] using haj1
    · simp [hk,hzero k hk]
  · rw [Finset.sum_eq_single j]
    · rw [haj1,mul_one]
    · intro k hk hkj
      rw [hzero k hkj,mul_zero]
    · simp

private theorem one_hot_code_injective (a b : Fin 5 → ℕ)
    (ha : ∑ j,a j ≤ 1) (hb : ∑ j,b j ≤ 1)
    (he : (∑ j,(j.val+1)*a j) = ∑ j,(j.val+1)*b j) : a=b := by
  by_cases haz : ∀ j,a j=0
  · have haeq : a=fun _ => 0 := funext haz
    have hbsum : (∑ j,(j.val+1)*b j)=0 := by rw [← he,haeq]; simp
    funext j
    rw [haz j]
    have hb0 : (j.val+1)*b j=0 := by
      have hle := Finset.single_le_sum (f:=fun j : Fin 5 => (j.val+1)*b j)
        (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hz : b j=0 := (Nat.mul_eq_zero.mp hb0).resolve_left (by omega)
    exact hz.symm
  · obtain ⟨j,hj⟩ := not_forall.mp haz
    obtain ⟨hav,hac⟩ := one_hot_code a ha j hj
    by_cases hbz : ∀ j,b j=0
    · have hbeq : b=fun _ => 0 := funext hbz
      rw [hac,hbeq] at he
      simp only [mul_zero,Finset.sum_const_zero] at he
      omega
    · obtain ⟨k,hk⟩ := not_forall.mp hbz
      obtain ⟨hbv,hbc⟩ := one_hot_code b hb k hk
      have hjk : j=k := Fin.ext (by omega)
      funext i
      rw [hav i,hbv i,hjk]

theorem valuation_colour_sum_le_one (c : ColourTuple)
    (hc : ∀ j,Admissible (c j))
    (hp : Pairwise (fun j k => IsCoprime (c j) (c k))) (P : Ideal O) :
    ∑ j,valuation (c j) P ≤ 1 := by
  have hn : (∏ j,c j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (hc j).1)
  have hs : Squarefree (∏ j,c j) := Finset.squarefree_prod_of_pairwise_isCoprime
    (fun j _ k _ hjk => (hp hjk).isRelPrime) (fun j _ => (hc j).2.1)
  have hv := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hn).mp hs) P
  change valuation (∏ j,c j) P ≤ 1 at hv
  rwa [valuation_prod _ _ (fun j _ => (hc j).1)] at hv

theorem weighted_valuation (c : ColourTuple) (hc : ∀ j,Admissible (c j)) (P : Ideal O) :
    valuation (colourProduct c) P = ∑ j,(j.val+1)*valuation (c j) P := by
  unfold colourProduct
  rw [valuation_prod _ _ (fun j _ => pow_ne_zero _ (hc j).1)]
  simp only [valuation_pow]

/-- Pairwise coprime squarefree colours are recovered uniquely from their
weighted ordinary ideal, including unit colours. -/
theorem colourProduct_eq_iff {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    colourProduct c=colourProduct d ↔ c=d := by
  constructor
  · intro he
    funext j
    apply ideal_eq_of_valuation_eq (hc j).1 (hd j).1
    intro P
    have hcode : (∑ j,(j.val+1)*valuation (c j) P)=∑ j,(j.val+1)*valuation (d j) P := by
      rw [← weighted_valuation c hc P,← weighted_valuation d hd P,he]
    exact congrFun (one_hot_code_injective _ _
      (valuation_colour_sum_le_one c hc hpc P) (valuation_colour_sum_le_one d hd hpd P) hcode) j
  · rintro rfl
    rfl

theorem span_tupleRow (c : ColourTuple) (hc : ∀ j,Admissible (c j)) :
    Ideal.span {tupleRow c}=colourProduct c := by
  unfold tupleRow colourProduct
  rw [← Ideal.prod_span_singleton]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← Ideal.span_singleton_pow,
    (primaryGenerator_spec _ (primaryGenerator_admissible _ (hc j))).1]

theorem tupleRow_eq_iff {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    tupleRow c=tupleRow d ↔ c=d := by
  constructor
  · intro he
    apply (colourProduct_eq_iff hc hd hpc hpd).mp
    rw [← span_tupleRow c hc,← span_tupleRow d hd,he]
  · rintro rfl
    rfl

theorem tupleRow_injOn (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) :
    Set.InjOn tupleRow F := by
  intro c hc d hd he
  exact (tupleRow_eq_iff (hF c hc) (hF d hd) (hpF c hc) (hpF d hd)).mp he

/-- Exact image reindexing for the actual Gram row array. -/
theorem sum_tupleRow_image {M : Type*} [AddCommMonoid M] (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) (f : O → M) :
    (∑ z ∈ F.image tupleRow,f z)=∑ c ∈ F,f (tupleRow c) :=
  Finset.sum_image (tupleRow_injOn F hF hpF)

section CommonPrimeCarrier
variable {ι : Type*} [Fintype ι]

/-- Any actual distinct-prime carrier preserves the complete natural
exponent vector. The representation identities are supplied by the proved
common-pool construction, not by a character or norm assumption. -/
theorem prime_power_product_eq_iff (P : ι → Ideal O) (hP : ∀ i,Prime (P i))
    (hinj : Function.Injective P) (left right : ι → ℕ) :
    (∏ i,(P i)^(left i))=(∏ i,(P i)^(right i)) ↔ left=right := by
  constructor
  · intro he
    funext i
    have hv := congrArg (fun I => valuation I (P i)) he
    simpa only [CenteredMomentForcing.valuation_prime_power_product P hP hinj] using hv
  · rintro rfl
    rfl

theorem primitiveSupport_empty_iff (left right : ι → ℕ) :
    primitiveSupport left right=∅ ↔ left=right := by
  constructor
  · intro h
    funext i
    by_contra hi
    have hm : i ∈ primitiveSupport left right := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
    exact (Finset.ne_empty_of_mem hm) h
  · rintro rfl
    simp [primitiveSupport]

/-- The actual primitive quotient is principal exactly on identical tuples. -/
theorem primitiveSupport_empty_iff_tuple {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (P : ι → Ideal O) (hP : ∀ i,Prime (P i)) (hinj : Function.Injective P)
    (left right : ι → ℕ)
    (hl : colourProduct c=∏ i,(P i)^(left i))
    (hr : colourProduct d=∏ i,(P i)^(right i)) :
    primitiveSupport left right=∅ ↔ c=d := by
  rw [primitiveSupport_empty_iff,← prime_power_product_eq_iff P hP hinj,← hl,← hr]
  exact colourProduct_eq_iff hc hd hpc hpd

theorem quotientExponent_zero_iff {j k : ℕ} (hj : j < 6) (hk : k < 6) :
    quotientExponent j k=0 ↔ j=k := by
  unfold quotientExponent
  omega

theorem quotient_exponents_zero_iff_tuple {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (P : ι → Ideal O) (hP : ∀ i,Prime (P i)) (hinj : Function.Injective P)
    (left right : ι → ℕ) (hl6 : ∀ i,left i < 6) (hr6 : ∀ i,right i < 6)
    (hl : colourProduct c=∏ i,(P i)^(left i))
    (hr : colourProduct d=∏ i,(P i)^(right i)) :
    (∀ i,quotientExponent (left i) (right i)=0) ↔ c=d := by
  have he : (∀ i,quotientExponent (left i) (right i)=0) ↔ left=right := by
    simp only [quotientExponent_zero_iff (hl6 _) (hr6 _),funext_iff]
  rw [he,← primitiveSupport_empty_iff]
  exact primitiveSupport_empty_iff_tuple hc hd hpc hpd P hP hinj left right hl hr

/-- Every off-diagonal actual pair has zero primitive frequency coefficient. -/
theorem offdiagonal_zero_frequency {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal] (hg : ∀ i,lambda ∉ P i)
    (hP : ∀ i,Prime (P i)) (hinj : Function.Injective P) (left right : ι → ℕ)
    (hl : colourProduct c=∏ i,(P i)^(left i))
    (hr : colourProduct d=∏ i,(P i)^(right i)) (hne : c ≠ d) :
    finiteSexticRow (fun i : primitiveSupport left right => P i.val) (fun i => hg i.val)
      (fun i => quotientExponent (left i.val) (right i.val)) 0=0 := by
  have hn : (primitiveSupport left right).Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun he => hne ((primitiveSupport_empty_iff_tuple hc hd hpc hpd P hP hinj left right hl hr).mp he))
  obtain ⟨i,hi⟩ := hn
  letI : Nonempty (primitiveSupport left right) := ⟨⟨i,hi⟩⟩
  exact finiteSexticRow_zero _ _ _

def primitiveConductor (P : ι → Ideal O) (left right : ι → ℕ) : Ideal O :=
  ∏ i : primitiveSupport left right,P i.val

theorem primitiveConductor_eq_one_iff (P : ι → Ideal O) (hP : ∀ i,Prime (P i))
    (left right : ι → ℕ) :
    primitiveConductor P left right=1 ↔ primitiveSupport left right=∅ := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hn
    have hd : P i ∣ primitiveConductor P left right :=
      Finset.dvd_prod_of_mem (a:=⟨i,hi⟩) (fun j : primitiveSupport left right => P j.val)
        (Finset.mem_univ (⟨i,hi⟩ : primitiveSupport left right))
    rw [he] at hd
    exact (hP i).not_isUnit (isUnit_of_dvd_one hd)
  · intro he
    unfold primitiveConductor
    apply Finset.prod_eq_one
    intro i hi
    exact False.elim ((Finset.ne_empty_of_mem i.property) he)

theorem primitiveConductor_eq_one_iff_tuple {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (P : ι → Ideal O) (hP : ∀ i,Prime (P i)) (hinj : Function.Injective P)
    (left right : ι → ℕ)
    (hl : colourProduct c=∏ i,(P i)^(left i))
    (hr : colourProduct d=∏ i,(P i)^(right i)) :
    primitiveConductor P left right=1 ↔ c=d := by
  rw [primitiveConductor_eq_one_iff P hP left right]
  exact primitiveSupport_empty_iff_tuple hc hd hpc hpd P hP hinj left right hl hr

theorem idealRowHom_zero_primitive {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (P : ι → Ideal O) (hP : ∀ i,Prime (P i)) (hinj : Function.Injective P)
    (left right : ι → ℕ)
    (hl : colourProduct c=∏ i,(P i)^(left i))
    (hr : colourProduct d=∏ i,(P i)^(right i)) (hne : c ≠ d) :
    idealRowHom 0 (primitiveConductor P left right)=0 := by
  have hn : (primitiveSupport left right).Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun he => hne ((primitiveSupport_empty_iff_tuple hc hd hpc hpd P hP hinj left right hl hr).mp he))
  obtain ⟨i,hi⟩ := hn
  exact idealRowHom_zero_of_dvd 0 (hP i)
    (Finset.dvd_prod_of_mem (a:=⟨i,hi⟩) (fun j : primitiveSupport left right => P j.val) (Finset.mem_univ (⟨i,hi⟩ : primitiveSupport left right)))
    (Ideal.zero_mem _)

/-- Every finite original puncture contribution has zero off-diagonal
frequency. The coefficient may retain all good/bad masks and Gauss factors;
the actual radial Fourier transform is left untouched. -/
theorem whole_offdiagonal_zero_frequency {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal] (hg : ∀ i,lambda ∉ P i)
    (hP : ∀ i,Prime (P i)) (hinj : Function.Injective P) (left right : ι → ℕ)
    (hl : colourProduct c=∏ i,(P i)^(left i))
    (hr : colourProduct d=∏ i,(P i)^(right i)) (hne : c ≠ d)
    (cancelled : Finset ι) (a : Finset ι → ℂ) (scale : Finset ι → ℝ) (W : 𝓢(ℝ,ℂ)) :
    (∑ E ∈ cancelled.powerset,a E*star (finiteSexticRow
      (fun i : primitiveSupport left right => P i.val) (fun i => hg i.val)
      (fun i => quotientExponent (left i.val) (right i.val)) 0)*
      paperRadialFourier W (scale E))=0 := by
  have hz := offdiagonal_zero_frequency hc hd hpc hpd P hg hP hinj left right hl hr hne
  apply Finset.sum_eq_zero
  intro E hE
  simp only [hz,star_zero,mul_zero,zero_mul]

end CommonPrimeCarrier

section ActualIncidence
open NaturalSharedTables

def actualTables (F : Finset ColourTuple) (c : ColourTuple) : Finset SharedTable :=
  F.image (table c)
def diagonalProduct (g : SharedTable) : Ideal O := ∏ j,g j j

/-- Actual labels attached to ONE original row. The puncture here is the
good cancelled-prime divisor; fixed bad divisors are separate finite labels. -/
abbrev ActualLabel (F : Finset ColourTuple) (c : ColourTuple) :=
  (g : actualTables F c) × (idealDivisors (diagonalProduct g.val)) × idealDivisors (c 0)

theorem weighted_ne_zero (c : ColourTuple) (hc : ∀ j,Admissible (c j)) :
    colourProduct c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hc j).1)

private theorem colour_power_dvd (c : ColourTuple) (j : Fin 5) : c j ∣ (c j)^(j.val+1) :=
  ⟨(c j)^j.val,by rw [pow_succ,mul_comm]⟩

theorem colour_dvd_weighted (c : ColourTuple) (j : Fin 5) : c j ∣ colourProduct c :=
  (colour_power_dvd c j).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

theorem table_entry_dvd_weighted {F : Finset ColourTuple} {c : ColourTuple} {g : SharedTable}
    (hg : g ∈ actualTables F c) (j k : Fin 5) : g j k ∣ colourProduct c := by
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hg
  exact (gcd_dvd_left _ _).trans (colour_dvd_weighted c j)

theorem diagonal_dvd_weighted {F : Finset ColourTuple} {c : ColourTuple} {g : SharedTable}
    (hg : g ∈ actualTables F c) : diagonalProduct g ∣ colourProduct c := by
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hg
  apply Finset.prod_dvd_prod_of_dvd
  intro j hj
  exact (gcd_dvd_left _ _).trans (colour_power_dvd c j)

/-- The table is tagged by its 25 original-row ideal divisors. -/
def tableEmbedding (F : Finset ColourTuple) (c : ColourTuple) (hc : ∀ j,Admissible (c j))
    (g : actualTables F c) : Fin 5 × Fin 5 → idealDivisors (colourProduct c) :=
  fun jk => ⟨g.val jk.1 jk.2,(mem_idealDivisors (weighted_ne_zero c hc)).2
    (table_entry_dvd_weighted g.property jk.1 jk.2)⟩

theorem tableEmbedding_injective (F : Finset ColourTuple) (c : ColourTuple)
    (hc : ∀ j,Admissible (c j)) : Function.Injective (tableEmbedding F c hc) := by
  intro g h he
  apply Subtype.ext
  funext j k
  exact congrArg Subtype.val (congrFun he (j,k))

theorem actualTables_card_le (F : Finset ColourTuple) (c : ColourTuple)
    (hc : ∀ j,Admissible (c j)) :
    (actualTables F c).card ≤ (idealDivisors (colourProduct c)).card^25 := by
  have he := Fintype.card_le_of_injective _ (tableEmbedding_injective F c hc)
  simpa only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,
    show 5*5=25 from rfl] using he

/-- All 25 table coordinates and both remaining divisors are counted by
actual injections/subset inclusions into original-row divisor sets. -/
theorem actualLabel_card_le (F : Finset ColourTuple) (c : ColourTuple)
    (hc : ∀ j,Admissible (c j)) :
    Fintype.card (ActualLabel F c) ≤ (idealDivisors (colourProduct c)).card^27 := by
  let D := (idealDivisors (colourProduct c)).card
  have hI := weighted_ne_zero c hc
  have hpivot : (idealDivisors (c 0)).card ≤ D := by
    apply Finset.card_le_card
    intro I hmem
    exact (mem_idealDivisors hI).2 (((mem_idealDivisors (hc 0).1).1 hmem).trans (colour_dvd_weighted c 0))
  have hdiag (g : actualTables F c) : (idealDivisors (diagonalProduct g.val)).card ≤ D := by
    have hd := diagonal_dvd_weighted g.property
    apply Finset.card_le_card
    intro I hmem
    exact (mem_idealDivisors hI).2
      (((mem_idealDivisors (ne_zero_of_dvd_ne_zero hI hd)).1 hmem).trans hd)
  change Fintype.card ((g : actualTables F c) ×
    idealDivisors (diagonalProduct g.val) × idealDivisors (c 0)) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ g : actualTables F c,D*D := Finset.sum_le_sum (fun g _ => by
      simpa only [Fintype.card_prod,Fintype.card_coe] using Nat.mul_le_mul (hdiag g) hpivot)
    _ = (actualTables F c).card*(D*D) := by simp
    _ ≤ D^25*(D*D) := Nat.mul_le_mul_right _ (actualTables_card_le F c hc)
    _ = _ := by dsimp [D]; ring

/-- Any requested power loss pays every ACTUAL shared table and good
puncture/pivot divisor incident to the original row, uniformly in F. -/
theorem actualLabel_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset ColourTuple) (c : ColourTuple),
      (∀ j,Admissible (c j)) →
      (Fintype.card (ActualLabel F c):ℝ) ≤ C*(Ideal.absNorm (colourProduct c):ℝ)^ε := by
  have he : 0 < ε/27 := by positivity
  let K := idealDivisorConstant (ε/27) he
  have hK : 0 < K := idealDivisorConstant_pos _ _
  refine ⟨K^27,by positivity,?_⟩
  intro F c hc
  have hI := weighted_ne_zero c hc
  have hn := CenteredExceptionalCount.norm_pos hI
  have hcard : (Fintype.card (ActualLabel F c):ℝ) ≤ ((idealDivisors (colourProduct c)).card:ℝ)^27 := by
    exact_mod_cast actualLabel_card_le F c hc
  have hdiv : ((idealDivisors (colourProduct c)).card:ℝ) ≤
      K*(Ideal.absNorm (colourProduct c):ℝ)^(ε/27) := idealDivisorConstant_bound _ _ _ hI
  calc
    _ ≤ ((idealDivisors (colourProduct c)).card:ℝ)^27 := hcard
    _ ≤ (K*(Ideal.absNorm (colourProduct c):ℝ)^(ε/27))^27 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv _
    _ = _ := by
      rw [mul_pow,← Real.rpow_mul_natCast hn.le]
      congr 1
      ring

/-- Actual restricted array mass, including a SEPARATE finite bad-divisor
label. Source/ray/fibre restrictions are arbitrary subsets of these labels;
all remaining complex masks must only be contractive. -/
theorem actual_incidence_masked_mass (ε : ℝ) (hε : 0 < ε) (bad : Finset (Ideal O)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset ColourTuple),
      (∀ c ∈ F,∀ j,Admissible (c j)) →
      ∀ (B : ℝ) (a : ColourTuple → ℂ)
        (E : ∀ c,Finset (bad × ActualLabel F c))
        (mask : ∀ c,bad × ActualLabel F c → ℂ),
        1 ≤ B → (∀ c ∈ F,(Ideal.absNorm (colourProduct c):ℝ) ≤ B) →
        (∀ c ∈ F,∀ l,‖mask c l‖ ≤ 1) →
      (∑ c ∈ F,∑ l ∈ E c,‖a c*mask c l‖^2) ≤ C*B^ε*(∑ c ∈ F,‖a c‖^2) := by
  obtain ⟨C₀,hC₀,hcard⟩ := actualLabel_small_power ε hε
  let C : ℝ := ((bad.card:ℝ)+1)*C₀
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro F hF B a E mask hB hnorm hmask
  have hlocal (c : ColourTuple) (hc : c ∈ F) :
      (Fintype.card (bad × ActualLabel F c):ℝ) ≤ C*B^ε := by
    rw [Fintype.card_prod,Fintype.card_coe,Nat.cast_mul]
    have hN0 : 0 ≤ (Ideal.absNorm (colourProduct c):ℝ) := Nat.cast_nonneg _
    calc
      _ ≤ (bad.card:ℝ)*(C₀*(Ideal.absNorm (colourProduct c):ℝ)^ε) :=
        mul_le_mul_of_nonneg_left (hcard F c (hF c hc)) (Nat.cast_nonneg _)
      _ ≤ ((bad.card:ℝ)+1)*(C₀*(Ideal.absNorm (colourProduct c):ℝ)^ε) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = C*(Ideal.absNorm (colourProduct c):ℝ)^ε := by dsimp [C]; ring
      _ ≤ C*B^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0 (hnorm c hc) hε.le) hC.le
  calc
    _ ≤ ∑ c ∈ F,(C*B^ε)*‖a c‖^2 := by
      apply Finset.sum_le_sum
      intro c hc
      calc
        _ ≤ ∑ _l ∈ E c,‖a c‖^2 := Finset.sum_le_sum (fun l hl =>
          pow_le_pow_left₀ (norm_nonneg _) (by
            rw [norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _) (hmask c hc l)) 2)
        _ = ((E c).card:ℝ)*‖a c‖^2 := by simp
        _ ≤ (Fintype.card (bad × ActualLabel F c):ℝ)*‖a c‖^2 :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ _)) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (hlocal c hc) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

end ActualIncidence

section ActualArrays
open NaturalSharedTables

def leftOriginals (F : Finset ColourTuple) (g : SharedTable) : Finset ColourTuple :=
  (pairFibre F g).image Prod.fst
def rightOriginals (F : Finset ColourTuple) (g : SharedTable) : Finset ColourTuple :=
  (pairFibre F g).image Prod.snd

theorem mem_leftOriginals {F : Finset ColourTuple} {g : SharedTable} {c : ColourTuple} :
    c ∈ leftOriginals F g ↔ c ∈ F ∧ ∃ d ∈ F,table c d=g := by
  constructor
  · intro h
    obtain ⟨⟨c',d⟩,hp,he⟩ := Finset.mem_image.mp h
    change c'=c at he
    subst c'
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_product.mp hp).1,d,(Finset.mem_product.mp hp).2,ht⟩
  · rintro ⟨hc,d,hd,ht⟩
    exact Finset.mem_image.mpr ⟨(c,d),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc,hd⟩,ht⟩,rfl⟩

theorem mem_rightOriginals {F : Finset ColourTuple} {g : SharedTable} {d : ColourTuple} :
    d ∈ rightOriginals F g ↔ d ∈ F ∧ ∃ c ∈ F,table c d=g := by
  constructor
  · intro h
    obtain ⟨⟨c,d'⟩,hp,he⟩ := Finset.mem_image.mp h
    change d'=d at he
    subst d'
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_product.mp hp).2,c,(Finset.mem_product.mp hp).1,ht⟩
  · rintro ⟨hd,c,hc,ht⟩
    exact Finset.mem_image.mpr ⟨(c,d),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc,hd⟩,ht⟩,rfl⟩

theorem recoverLeft_image (F : Finset ColourTuple) (g : SharedTable)
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) :
    (leftFamily F g).image (recoverLeft g)=leftOriginals F g := by
  ext c
  constructor
  · intro hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr ⟨p,hp,(congrArg Prod.fst (recover_pair_of_mem hpF hp)).symm⟩
  · intro hc
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_image.mpr ⟨(residualPair p).1,?_,congrArg Prod.fst (recover_pair_of_mem hpF hp)⟩
    exact Finset.mem_image.mpr ⟨residualPair p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩

theorem recoverRight_image (F : Finset ColourTuple) (g : SharedTable)
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) :
    (rightFamily F g).image (recoverRight g)=rightOriginals F g := by
  ext c
  constructor
  · intro hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr ⟨p,hp,(congrArg Prod.snd (recover_pair_of_mem hpF hp)).symm⟩
  · intro hc
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_image.mpr ⟨(residualPair p).2,?_,congrArg Prod.snd (recover_pair_of_mem hpF hp)⟩
    exact Finset.mem_image.mpr ⟨residualPair p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩

theorem recoverLeft_injOn_family {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) :
    Set.InjOn (recoverLeft g) (leftFamily F g) := by
  intro a ha b hb he
  have hc : recoverLeft g a ∈ F := (mem_leftOriginals.mp (by
    rw [← recoverLeft_image F g hpF]
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩)).1
  funext j
  have hn : rowProduct g j*a j ≠ 0 := (hF _ hc j).1
  exact mul_left_cancel₀ (left_ne_zero_of_mul hn) (congrFun he j)

theorem recoverRight_injOn_family {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) :
    Set.InjOn (recoverRight g) (rightFamily F g) := by
  intro a ha b hb he
  have hc : recoverRight g a ∈ F := (mem_rightOriginals.mp (by
    rw [← recoverRight_image F g hpF]
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩)).1
  funext j
  have hn : columnProduct g j*a j ≠ 0 := (hF _ hc j).1
  exact mul_left_cancel₀ (left_ne_zero_of_mul hn) (congrFun he j)

theorem sum_recoverLeft_family {M : Type*} [AddCommMonoid M]
    (F : Finset ColourTuple) (g : SharedTable)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) (f : ColourTuple → M) :
    (∑ a ∈ leftFamily F g,f (recoverLeft g a))=∑ c ∈ leftOriginals F g,f c := by
  rw [← recoverLeft_image F g hpF,Finset.sum_image (recoverLeft_injOn_family hF hpF)]

theorem sum_recoverRight_family {M : Type*} [AddCommMonoid M]
    (F : Finset ColourTuple) (g : SharedTable)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) (f : ColourTuple → M) :
    (∑ a ∈ rightFamily F g,f (recoverRight g a))=∑ c ∈ rightOriginals F g,f c := by
  rw [← recoverRight_image F g hpF,Finset.sum_image (recoverRight_injOn_family hF hpF)]

theorem actualLabel_card_sum (F : Finset ColourTuple) (c : ColourTuple) :
    (Fintype.card (ActualLabel F c):ℝ) =
      ∑ g ∈ actualTables F c,((idealDivisors (diagonalProduct g)).card:ℝ)*((idealDivisors (c 0)).card:ℝ) := by
  have he : Fintype.card (ActualLabel F c) =
      ∑ g ∈ actualTables F c,(idealDivisors (diagonalProduct g)).card*(idealDivisors (c 0)).card := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod,Fintype.card_coe]
    exact (Finset.sum_coe_sort (actualTables F c)
      (fun g => (idealDivisors (diagonalProduct g)).card*(idealDivisors (c 0)).card))
  exact_mod_cast he

private theorem leftOriginals_subset (F : Finset ColourTuple) (g : SharedTable) :
    leftOriginals F g ⊆ F := fun c hc => (mem_leftOriginals.mp hc).1

private theorem sum_originals (F : Finset ColourTuple) (g : SharedTable) (f : ColourTuple → ℝ) :
    (∑ c ∈ leftOriginals F g,f c)=∑ c ∈ F,if c ∈ leftOriginals F g then f c else 0 := by
  calc
    _ = ∑ c ∈ leftOriginals F g,if c ∈ leftOriginals F g then f c else 0 :=
      Finset.sum_congr rfl (fun c hc => by rw [if_pos hc])
    _ = _ := Finset.sum_subset (leftOriginals_subset F g) (fun c hc hn => by rw [if_neg hn])

private theorem incident_sum_le (F : Finset ColourTuple) (G : Finset SharedTable) (c : ColourTuple) :
    (∑ g ∈ G.filter (fun g => c ∈ leftOriginals F g),
      ((idealDivisors (diagonalProduct g)).card:ℝ)*((idealDivisors (c 0)).card:ℝ)) ≤
      (Fintype.card (ActualLabel F c):ℝ) := by
  rw [actualLabel_card_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro g hg
    obtain ⟨hc,d,hd,ht⟩ := mem_leftOriginals.mp (Finset.mem_filter.mp hg).2
    exact Finset.mem_image.mpr ⟨d,hd,ht⟩
  · intro g hg hn
    positivity

/-- The actual recovered left array pays only the incidences of each
original row. G is arbitrary; no global table-pool cardinal is used. -/
theorem left_array_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset ColourTuple),
      (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      ∀ (G : Finset SharedTable) (B : ℝ) (a : ColourTuple → ℂ),
      1 ≤ B → (∀ c ∈ F,(Ideal.absNorm (colourProduct c):ℝ) ≤ B) →
      (∑ g ∈ G,∑ b ∈ leftFamily F g,
        ((idealDivisors (diagonalProduct g)).card:ℝ)*
          ((idealDivisors ((recoverLeft g b) 0)).card:ℝ)*‖a (recoverLeft g b)‖^2) ≤
        C*B^ε*(∑ c ∈ F,‖a c‖^2) := by
  obtain ⟨C,hC,hcard⟩ := actualLabel_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro F hF hpF G B a hB hnorm
  let cost : SharedTable → ColourTuple → ℝ := fun g c =>
    ((idealDivisors (diagonalProduct g)).card:ℝ)*((idealDivisors (c 0)).card:ℝ)
  change (∑ g ∈ G,∑ b ∈ leftFamily F g,cost g (recoverLeft g b)*‖a (recoverLeft g b)‖^2) ≤ _
  calc
    _ = ∑ g ∈ G,∑ c ∈ leftOriginals F g,cost g c*‖a c‖^2 :=
      Finset.sum_congr rfl (fun g hg => sum_recoverLeft_family F g hF hpF _)
    _ = ∑ g ∈ G,∑ c ∈ F,if c ∈ leftOriginals F g then cost g c*‖a c‖^2 else 0 :=
      Finset.sum_congr rfl (fun g hg => sum_originals F g _)
    _ = ∑ c ∈ F,∑ g ∈ G,if c ∈ leftOriginals F g then cost g c*‖a c‖^2 else 0 := Finset.sum_comm
    _ ≤ ∑ c ∈ F,(C*B^ε)*‖a c‖^2 := by
      apply Finset.sum_le_sum
      intro c hc
      have hlocal : (Fintype.card (ActualLabel F c):ℝ) ≤ C*B^ε :=
        (hcard F c (hF c hc)).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm c hc) hε.le) hC.le)
      calc
        _ = (∑ g ∈ G.filter (fun g => c ∈ leftOriginals F g),cost g c)*‖a c‖^2 := by
          rw [Finset.sum_mul,Finset.sum_filter]
        _ ≤ (Fintype.card (ActualLabel F c):ℝ)*‖a c‖^2 :=
          mul_le_mul_of_nonneg_right (incident_sum_le F G c) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right hlocal (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

def transpose (g : SharedTable) : SharedTable := fun j k => g k j

theorem transpose_involutive (g : SharedTable) : transpose (transpose g)=g := rfl

theorem transpose_injective : Function.Injective transpose := by
  intro g h he
  have hh := congrArg transpose he
  exact hh

theorem table_transpose (c d : ColourTuple) : transpose (table c d)=table d c := by
  funext j k
  exact gcd_comm _ _

theorem leftResidual_swap (c d : ColourTuple) : leftResidual d c=rightResidual c d := by
  funext j
  simp only [leftResidual,rightResidual,rowProduct,columnProduct,table,gcd_comm]

theorem pairFibre_swap {F : Finset ColourTuple} {g : SharedTable} (p : ColourTuple × ColourTuple) :
    p ∈ pairFibre F g ↔ p.swap ∈ pairFibre F (transpose g) := by
  constructor
  · intro hp
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr (Finset.mem_product.mp hp).symm,?_⟩
    change table p.2 p.1=transpose g
    rw [← table_transpose,ht]
  · intro hp
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr (Finset.mem_product.mp hp).symm,?_⟩
    change table p.2 p.1=transpose g at ht
    have he := congrArg transpose ht
    rwa [table_transpose,transpose_involutive] at he

theorem rightFamily_eq_left (F : Finset ColourTuple) (g : SharedTable) :
    rightFamily F g=leftFamily F (transpose g) := by
  ext b
  constructor
  · intro hb
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_image.mpr
    refine ⟨residualPair p.swap,Finset.mem_image.mpr ⟨p.swap,(pairFibre_swap p).mp hp,rfl⟩,?_⟩
    exact leftResidual_swap p.1 p.2
  · intro hb
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
    have hp' : p.swap ∈ pairFibre F g := by
      simpa only [transpose_involutive] using (pairFibre_swap p).mp hp
    apply Finset.mem_image.mpr
    refine ⟨residualPair p.swap,Finset.mem_image.mpr ⟨p.swap,hp',rfl⟩,?_⟩
    exact (leftResidual_swap p.2 p.1).symm

/-- The right array is paid independently, using the transposed ACTUAL
table at each original right row. No left/right table count is multiplied. -/
theorem right_array_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset ColourTuple),
      (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      ∀ (G : Finset SharedTable) (B : ℝ) (a : ColourTuple → ℂ),
      1 ≤ B → (∀ c ∈ F,(Ideal.absNorm (colourProduct c):ℝ) ≤ B) →
      (∑ g ∈ G,∑ b ∈ rightFamily F g,
        ((idealDivisors (diagonalProduct g)).card:ℝ)*
          ((idealDivisors ((recoverRight g b) 0)).card:ℝ)*‖a (recoverRight g b)‖^2) ≤
        C*B^ε*(∑ c ∈ F,‖a c‖^2) := by
  obtain ⟨C,hC,hleft⟩ := left_array_mass ε hε
  refine ⟨C,hC,?_⟩
  intro F hF hpF G B a hB hnorm
  have he := hleft F hF hpF (G.image transpose) B a hB hnorm
  rw [Finset.sum_image (fun g hg h hh heq => transpose_injective heq)] at he
  have hrewrite (g : SharedTable) :
      (∑ b ∈ leftFamily F (transpose g),
        ((idealDivisors (diagonalProduct (transpose g))).card:ℝ)*
          ((idealDivisors ((recoverLeft (transpose g) b) 0)).card:ℝ)*‖a (recoverLeft (transpose g) b)‖^2) =
      (∑ b ∈ rightFamily F g,
        ((idealDivisors (diagonalProduct g)).card:ℝ)*
          ((idealDivisors ((recoverRight g b) 0)).card:ℝ)*‖a (recoverRight g b)‖^2) := by
    rw [← rightFamily_eq_left]
    rfl
  simpa only [hrewrite] using he

def arrayFamily (left : Bool) (F : Finset ColourTuple) (g : SharedTable) : Finset ColourTuple :=
  if left then leftFamily F g else rightFamily F g
def arrayRecover (left : Bool) (g : SharedTable) : ColourTuple → ColourTuple :=
  if left then recoverLeft g else recoverRight g

private theorem array_mass (left : Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset ColourTuple),
      (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      ∀ (G : Finset SharedTable) (B : ℝ) (a : ColourTuple → ℂ),
      1 ≤ B → (∀ c ∈ F,(Ideal.absNorm (colourProduct c):ℝ) ≤ B) →
      (∑ g ∈ G,∑ b ∈ arrayFamily left F g,
        ((idealDivisors (diagonalProduct g)).card:ℝ)*
          ((idealDivisors ((arrayRecover left g b) 0)).card:ℝ)*‖a (arrayRecover left g b)‖^2) ≤
        C*B^ε*(∑ c ∈ F,‖a c‖^2) := by
  cases left
  · simpa [arrayFamily,arrayRecover] using right_array_mass ε hε
  · simpa [arrayFamily,arrayRecover] using left_array_mass ε hε

/-- Complete actual left/right array mass with every good puncture, pivot
divisor and separate fixed bad label. All source/ray/fibre selectors can
remain inside the arbitrary contractive complex mask. -/
theorem masked_array_mass (left : Bool) (ε : ℝ) (hε : 0 < ε) (bad : Finset (Ideal O)) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset ColourTuple),
      (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      ∀ (G : Finset SharedTable) (B : ℝ) (a : ColourTuple → ℂ)
        (mask : SharedTable → ColourTuple → Ideal O → Ideal O → Ideal O → ℂ),
      1 ≤ B → (∀ c ∈ F,(Ideal.absNorm (colourProduct c):ℝ) ≤ B) →
      (∀ g ∈ G,∀ b ∈ arrayFamily left F g,
        ∀ e ∈ idealDivisors (diagonalProduct g),
        ∀ m ∈ idealDivisors ((arrayRecover left g b) 0),∀ d ∈ bad,‖mask g b e m d‖ ≤ 1) →
      (∑ g ∈ G,∑ b ∈ arrayFamily left F g,
        ∑ e ∈ idealDivisors (diagonalProduct g),
        ∑ m ∈ idealDivisors ((arrayRecover left g b) 0),∑ d ∈ bad,
          ‖a (arrayRecover left g b)*mask g b e m d‖^2) ≤
        C*B^ε*(∑ c ∈ F,‖a c‖^2) := by
  obtain ⟨C₀,hC₀,hbound⟩ := array_mass left ε hε
  let C : ℝ := ((bad.card:ℝ)+1)*C₀
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro F hF hpF G B a mask hB hnorm hmask
  have hcost := hbound F hF hpF G B a hB hnorm
  have hpoint :
      (∑ g ∈ G,∑ b ∈ arrayFamily left F g,
        ∑ e ∈ idealDivisors (diagonalProduct g),
        ∑ m ∈ idealDivisors ((arrayRecover left g b) 0),∑ d ∈ bad,
          ‖a (arrayRecover left g b)*mask g b e m d‖^2) ≤
      (bad.card:ℝ)*(∑ g ∈ G,∑ b ∈ arrayFamily left F g,
        ((idealDivisors (diagonalProduct g)).card:ℝ)*
          ((idealDivisors ((arrayRecover left g b) 0)).card:ℝ)*‖a (arrayRecover left g b)‖^2) := by
    calc
      _ ≤ ∑ g ∈ G,∑ b ∈ arrayFamily left F g,
          ∑ e ∈ idealDivisors (diagonalProduct g),
          ∑ m ∈ idealDivisors ((arrayRecover left g b) 0),∑ d ∈ bad,
            ‖a (arrayRecover left g b)‖^2 := by
        apply Finset.sum_le_sum
        intro g hg
        apply Finset.sum_le_sum
        intro b hb
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro d hd
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hmask g hg b hb e he m hm d hd)
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
  calc
    _ ≤ _ := hpoint
    _ ≤ (bad.card:ℝ)*(C₀*B^ε*(∑ c ∈ F,‖a c‖^2)) :=
      mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg _)
    _ ≤ ((bad.card:ℝ)+1)*(C₀*B^ε*(∑ c ∈ F,‖a c‖^2)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by dsimp [C]; ring

end ActualArrays

end
end Qrh.JointDetector.NaturalTupleIdentity

#print axioms Qrh.JointDetector.NaturalTupleIdentity.tupleRow_eq_iff
#print axioms Qrh.JointDetector.NaturalTupleIdentity.primitiveSupport_empty_iff_tuple
#print axioms Qrh.JointDetector.NaturalTupleIdentity.offdiagonal_zero_frequency

#print axioms Qrh.JointDetector.NaturalTupleIdentity.actualLabel_small_power
#print axioms Qrh.JointDetector.NaturalTupleIdentity.actual_incidence_masked_mass

#print axioms Qrh.JointDetector.NaturalTupleIdentity.whole_offdiagonal_zero_frequency
#print axioms Qrh.JointDetector.NaturalTupleIdentity.idealRowHom_zero_primitive

#print axioms Qrh.JointDetector.NaturalTupleIdentity.left_array_mass

#print axioms Qrh.JointDetector.NaturalTupleIdentity.right_array_mass

#print axioms Qrh.JointDetector.NaturalTupleIdentity.masked_array_mass
