/- Copyright (c) 2026 Sil. Apache-2.0.
Exact fixing of ALL supplier values and a subsequent selected-slot split
of the original restricted tuple coefficient.
The remaining ordinary/Gauss kernel is evaluated at the reconstructed
original assignment; no separability premise replaces that evaluation.
-/
import Candidate.Feedback.FourthPower.MixedSupplierPartition
import Candidate.Feedback.FourthPower.KernelAssignmentReindex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedSupplierSplit
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRectangle CenteredMomentRectangle CenteredMomentFirstSectors
open Record12518109GainDeletion
open MixedHeightEnergy MixedLiteralAllocation MixedCommonRestriction MixedCommonCoefficient
open MixedCommonAllocation MixedTupleRows MixedSupplierPartition KernelAssignmentReindex
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- A finite alphabet containing exactly the supplied marked pools. -/
def markedUniverse (pool : α → Finset Id) : Finset Id := Finset.univ.biUnion pool

theorem mem_markedUniverse (pool : α → Finset Id) (i : α) (I : Id) (hI : I ∈ pool i) :
    I ∈ markedUniverse pool := Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hI⟩

def values (pool : α → Finset Id) (p : α → markedUniverse pool) : α → Id :=
  fun i => (p i).val

theorem pi_sum_zeroextend (pool : α → Finset Id) (f : (α → Id) → ℂ) :
    (∑ p ∈ Fintype.piFinset pool, f p) =
      ∑ p : α → markedUniverse pool,
        if ∀ i, (p i).val ∈ pool i then f (values pool p) else 0 := by
  symm
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun p _ => values pool p)
  · intro p hp
    exact Fintype.mem_piFinset.mpr (Finset.mem_filter.mp hp).2
  · intro p hp q hq he
    funext i
    exact Subtype.ext (congrFun he i)
  · intro p hp
    let q : α → markedUniverse pool := fun i =>
      ⟨p i, mem_markedUniverse pool i (p i) (Fintype.mem_piFinset.mp hp i)⟩
    refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    intro i
    exact Fintype.mem_piFinset.mp hp i
  · intro p hp
    rfl

def slotAmplitude (pool : α → Finset Id) (ν : α → Id → ℂ)
    (Wslot : α → ℝ → ℂ) (P : α → ℝ) (i : α) (q : markedUniverse pool) : ℂ :=
  if q.val ∈ pool i then ν i q.val * Wslot i ((q.val.absNorm : ℝ)/P i) else 0

/-- Everything except the separated marked slot factors. In particular
the fifth-free ordinary restriction, all punctures, the old seed, the
exact column equality and the original centered rectangle are retained. -/
def ordinaryKernel (H R seed I : Id) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (p : α → Id) (n : Id×Id) : ℂ :=
  if finiteTupleProduct (pack p n) = I then
    restrictionWeight H (∏ i,p i) n.1 n.2 *
      (if IsCoprime (finiteTupleProduct (pack p n)) R then 1 else 0) *
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (d.1*n.1) (d.2*n.2) *
      (if seed ∣ finiteTupleProduct (pack p n) then 1 else 0)
  else 0

theorem packed_coefficient (H R seed I : Id) (ν : α → Id → ℂ)
    (Wslot : α → ℝ → ℂ) (P : α → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (p : α → Id) (n : Id×Id) :
    (if finiteTupleProduct (pack p n) = I then
      tupleWeight H (pack p n) * profileCoefficient R ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed (pack p n) else 0) =
      if Function.Injective p then
        ordinaryKernel H R seed I W₁ W₂ X₁ X₂ Y₁ Y₂ d p n *
          ∏ i, ν i (p i) * Wslot i (((p i).absNorm : ℝ)/P i)
      else 0 := by
  have hw : tupleWeight H (pack p n) =
      if Function.Injective p then restrictionWeight H (∏ i,p i) n.1 n.2 else 0 := by
    unfold tupleWeight tupleRestriction slotProduct restrictionWeight
    simp only [MixedTupleRows.pack,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
    by_cases hi : Function.Injective p <;> simp [hi]
  rw [hw]
  unfold ordinaryKernel profileCoefficient
  simp only [MixedTupleRows.pack,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
  split_ifs <;> ring

theorem finite_column_weighted (pool : α → Finset Id) (A B : Finset Id)
    (H R seed I : Id) (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) :
    finiteColumnCoefficient (Fintype.piFinset (pools pool A B))
      (fun v => tupleWeight H v * profileCoefficient R ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) I =
      weightedSum (slotAmplitude pool ν Wslot P) (fun p =>
        ∑ n ∈ A×ˢB, ordinaryKernel H R seed I W₁ W₂ X₁ X₂ Y₁ Y₂ d (values pool p) n) := by
  unfold finiteColumnCoefficient
  rw [Finset.sum_filter, split_tuple_sum, pi_sum_zeroextend]
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro p hp
  have hi : Function.Injective (values pool p) ↔ Function.Injective p := by
    constructor
    · intro h i j he
      exact h (congrArg Subtype.val he)
    · intro h i j he
      exact h (Subtype.ext he)
  by_cases hpool : ∀ i, (p i).val ∈ pool i
  · rw [if_pos hpool]
    have hamp : (∏ i,slotAmplitude pool ν Wslot P i (p i)) =
        ∏ i,ν i ((p i).val) * Wslot i (((p i).val.absNorm : ℝ)/P i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [slotAmplitude,if_pos (hpool i)]
    rw [hamp]
    simp_rw [packed_coefficient H R seed I ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d,
      hi]
    by_cases hinj : Function.Injective p
    · simp only [hinj,ite_true,Finset.sum_mul,values]
    · simp only [hinj,ite_false,Finset.sum_const_zero]
  · rw [if_neg hpool]
    push_neg at hpool
    obtain ⟨i,hi⟩ := hpool
    have hz : (∏ j,slotAmplitude pool ν Wslot P j (p j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [slotAmplitude,hi])
    simp only [hz,mul_zero,ite_self]

def ordinaryPairs (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (b X₁ X₂ Y₁ Y₂ : ℝ) : Finset (Id×Id) :=
  (residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁)) ×ˢ
    (residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂))

def columnKernel (pool : α → Finset Id) (H R seed I : Id)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (hd : d.1≠0 ∧ d.2≠0) (p : α → markedUniverse pool) : ℂ :=
  ∑ n ∈ ordinaryPairs d hd b X₁ X₂ Y₁ Y₂,
    ordinaryKernel H R seed I W₁ W₂ X₁ X₂ Y₁ Y₂ d (values pool p) n

theorem originalColumn_weighted (S H : Finset PrimeIdeal) (pool : α → Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (I : Id) :
    originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I =
      weightedSum (slotAmplitude pool ν Wslot P)
        (columnKernel pool (punctureProduct S H) R seed I W₁ W₂ b X₁ X₂ Y₁ Y₂ d hd) := by
  exact finite_column_weighted pool _ _ (punctureProduct S H) R seed I ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ d

section Split
variable {ι A : Type*} [Fintype ι] [Fintype A]

def frozenLiveAmplitude (T : Finset ι) (a : ι → A → ℂ) (t : T → A)
    (j : {i // i ∉ T}) (p : A) : ℂ :=
  if ∀ i : T, t i ≠ p then a j.val p else 0

/-- All holes against the frozen assignment remain in each live slot.
This is a weighted identity, not a bound on arbitrary restricted sums. -/
theorem remaining_as_weighted (T : Finset ι) (a : ι → A → ℂ) (t : T → A)
    (F : ({i // i ∉ T} → A) → ℂ) :
    remainingSum T a t F = weightedSum (frozenLiveAmplitude T a t) F := by
  unfold remainingSum weightedSum frozenLiveAmplitude
  apply Finset.sum_congr (by ext; simp)
  intro s hs
  by_cases hinj : Function.Injective s
  · simp only [hinj,true_and,ite_true,Fintype.prod_ite_zero]
    have hc : (∀ i : T, ∀ j : {i // i ∉ T}, t i ≠ s j) ↔
        (∀ j : {i // i ∉ T}, ∀ i : T, t i ≠ s j) := forall_comm
    simp only [hc]
    split_ifs <;> simp
  · simp [hinj]

theorem split_rejoined (T : Finset ι) (a : ι → A → ℂ) (F : (ι → A) → ℂ) :
    weightedSum a F = ∑ t : T → A, if Function.Injective t then
      (∏ i : T,a i.val (t i)) * remainingSum T a t
        (fun s => F (joinAssignments (fun i => i ∈ T) t s)) else 0 := by
  have hjoin (x : ι → A) :
      joinAssignments (fun i => i ∈ T) (fun i => x i.val) (fun j => x j.val) = x := by
    funext i
    simp [joinAssignments]
  simpa only [hjoin] using split_weighted T a
    (fun t s => F (joinAssignments (fun i => i ∈ T) t s))

/-- First freeze T, then select J among the remaining indices. The
remaining kernel still sees the exact reconstructed full assignment. -/
theorem split_two_levels (T : Finset ι) (J : Finset {i // i ∉ T})
    (a : ι → A → ℂ) (F : (ι → A) → ℂ) :
    weightedSum a F = ∑ t : T → A, if Function.Injective t then
      (∏ i : T,a i.val (t i)) *
        ∑ s : J → A, if Function.Injective s then
          (∏ j : J,frozenLiveAmplitude T a t j.val (s j)) *
            remainingSum J (frozenLiveAmplitude T a t) s (fun r =>
              F (joinAssignments (fun i => i ∈ T) t
                (joinAssignments (fun j => j ∈ J) s r))) else 0
      else 0 := by
  rw [split_rejoined T a F]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hinj : Function.Injective t
  · rw [if_pos hinj,if_pos hinj,remaining_as_weighted,
      split_rejoined J (frozenLiveAmplitude T a t)
        (fun s => F (joinAssignments (fun i => i ∈ T) t s))]
    congr 1
    apply Finset.sum_congr (by ext; simp)
    intro s hs
    by_cases hsinj : Function.Injective s
    · simp only [hsinj,ite_true]
    · simp only [hsinj,ite_false]
  · simp [hinj]
end Split

/-- The reconstructed tuple product is literally f*D*n. This is the
product needed by the old seed mask and by primaryGenerator_mul. -/
theorem packed_two_level_product (pool : α → Finset Id) (T : Finset α)
    (J : Finset {i // i ∉ T}) (t : T → markedUniverse pool)
    (s : J → markedUniverse pool)
    (r : {j : {i // i ∉ T} // j ∉ J} → markedUniverse pool) (n : Id×Id) :
    finiteTupleProduct (pack (values pool
      (joinAssignments (fun i => i ∈ T) t (joinAssignments (fun j => j ∈ J) s r))) n) =
      (∏ i : T,(t i).val) * (∏ j : J,(s j).val) *
        (n.1*n.2*∏ k : {j : {i // i ∉ T} // j ∉ J},(r k).val) := by
  rw [MixedTupleRows.pack_product]
  change n.1*n.2*(∏ i,
    (joinAssignments (fun i => i ∈ T) t (joinAssignments (fun j => j ∈ J) s r) i).val) = _
  rw [joinAssignments_product (fun i => i ∈ T)
      (fun (_ : α) (q : markedUniverse pool) => q.val)
        t (joinAssignments (fun j => j ∈ J) s r)]
  have hinner := joinAssignments_product (fun j : {i // i ∉ T} => j ∈ J)
      (fun (_ : {i // i ∉ T}) (q : markedUniverse pool) => q.val) s r
  calc
    _ = n.1*n.2*((∏ i : T,(t i).val)*
        ((∏ j : J,(s j).val)*(∏ k : {j : {i // i ∉ T} // j ∉ J},(r k).val))) := by
      congr 2
      · apply Finset.prod_congr (by ext; simp)
        intros
        rfl
      · convert hinner using 2 <;> first
        | rfl
        | (apply Finset.ext; intro i; simp)
        | (apply Finset.prod_congr (by ext; simp); intros; rfl)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- The concrete supplier branch of originalColumn after fixing its
supplier values and then its selected live values. Every original
tuple mask remains in columnKernel and every cross-hole in remainingSum.
There is deliberately NO hypothesis that this kernel already separates. -/
theorem originalColumn_supplier_selected_split (u : Id) (L : Finset α)
    (J : Finset {i // i ∉ Lᶜ}) (S H : Finset PrimeIdeal) (pool : α → Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (I : Id) :
    let a := slotAmplitude pool (supplierCharacters u L ν) Wslot P
    let F := columnKernel pool (punctureProduct S H) R seed I W₁ W₂ b X₁ X₂ Y₁ Y₂ d hd
    originalColumn S H pool d hd R seed (supplierCharacters u L ν)
      Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I =
      ∑ t : ↥(Lᶜ) → markedUniverse pool, if Function.Injective t then
        (∏ i : ↥(Lᶜ),a i.val (t i)) *
          ∑ s : J → markedUniverse pool, if Function.Injective s then
            (∏ j : J,frozenLiveAmplitude Lᶜ a t j.val (s j)) *
              remainingSum J (frozenLiveAmplitude Lᶜ a t) s (fun r =>
                F (joinAssignments (fun i => i ∈ Lᶜ) t
                  (joinAssignments (fun j => j ∈ J) s r))) else 0
        else 0 := by
  dsimp only
  rw [originalColumn_weighted S H pool d hd R seed (supplierCharacters u L ν)
    Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I]
  have he := split_two_levels Lᶜ J (slotAmplitude pool (supplierCharacters u L ν) Wslot P)
    (columnKernel pool (punctureProduct S H) R seed I W₁ W₂ b X₁ X₂ Y₁ Y₂ d hd)
  calc
    _ = _ := he
    _ = _ := by
      apply Finset.sum_congr (by ext; simp)
      intro t ht
      by_cases hi : Function.Injective t
      · simp only [hi,ite_true]
        congr 1
        apply Finset.sum_congr (by ext; simp)
        intro s hs
        by_cases hj : Function.Injective s <;> simp only [hj,ite_true,ite_false]
      · simp only [hi,ite_false]

end
end Candidate.Feedback.FourthPower.MixedSupplierSplit
