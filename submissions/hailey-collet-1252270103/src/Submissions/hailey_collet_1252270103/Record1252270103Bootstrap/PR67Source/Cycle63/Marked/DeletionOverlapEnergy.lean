import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionOverlapSlots
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O

def overlapCost (B : ℝ) (K : ℕ) : ℝ :=
  ((2:ℝ)^(K*K)*(256*B^K)^K)^2*(max 1 (K:ℝ))^(2*K)

theorem overlapCost_pos (B : ℝ) (hB : 1≤B) (K : ℕ) : 0<overlapCost B K := by
  unfold overlapCost
  have : 0<B := zero_lt_one.trans_le hB
  positivity

/-- A separated-pool estimate implies the same moment for arbitrary
pool overlaps. The coefficient square mass controls all repeated primes. -/
theorem overlapping_direct_energy {I Row : Type} [Fintype I] [DecidableEq I]
    (rows : Finset Row) (u : Row→O) (D : Row→ℂ)
    (L : I→Finset (Ideal O)) (β : I→ Ideal O→ℂ) (P : I→ℝ)
    (B E : ℝ) (hB : 1≤B) (hE : 0≤E) (K : ℕ) (hK : Fintype.card I≤K)
    (hP : ∀i,1≤P i) (hβ : ∀i,∀p∈L i,‖β i p‖≤B)
    (hp : ∀i,∀p∈L i,p≠0) (hN : ∀i,∀p∈L i,(p.absNorm:ℝ)≤2*P i)
    (hsep : ∀{J : Type} [Fintype J] [DecidableEq J],
      ∀f : J→ I,Function.Injective f →∀L' : J→Finset (Ideal O),
      (∀j,L' j⊆L (f j)) →
      (((Finset.univ : Finset J) : Set J).PairwiseDisjoint L') →
      (∑v∈rows,‖D v*(∏j,directPrimeSlot (u v) (L' j) (β (f j)) (P (f j)))‖^2)≤E) :
    (∑v∈rows,‖D v*(∏i,directPrimeSlot (u v) (L i) (β i) (P i))‖^2)≤overlapCost B K*E := by
  classical
  let atoms : Finset (Ideal O) := Finset.univ.biUnion L
  have hLa (i : I) : L i⊆atoms := by
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hp⟩
  let a : Row→ I→atoms→ℂ := fun v i p=>idealRowHom (u v) p.val*normalizedPrimeCoeff (L i) (β i) (P i) p.val
  let coeffNorm : I→atoms→ℝ := fun i p=>‖normalizedPrimeCoeff (L i) (β i) (P i) p.val‖
  let cK : ℝ := (max 1 (K:ℝ))^(2*K)
  have hcK : 1≤ cK := one_le_pow₀ (le_max_left _ _)
  have ha (v : Row) (hv : v∈rows) (i : I) (p : atoms) : ‖a v i p‖≤ coeffNorm i p := by
    dsimp [a,coeffNorm]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)
  have hv (i : I) (p : atoms) : coeffNorm i p≤B := normalizedPrimeCoeff_bound _ _ _ _
    (hP i) (zero_le_one.trans hB) (hβ i) p.val
  have he (i : I) : (∑p : atoms,(coeffNorm i p)^2)≤256*B^2 := by
    rw [←Finset.sum_subtype (F:=inferInstance) (p:=fun p : Ideal O=>p∈atoms) atoms (by simp)
      (fun p=>‖normalizedPrimeCoeff (L i) (β i) (P i) p‖^2)]
    exact normalizedPrimeCoeff_energy atoms (L i) (β i) (P i) B (hP i)
      (zero_le_one.trans hB) (hβ i) (hp i) (hN i)
  have hsingle (r : Setoid I) (t : {q // ¬singletonBlock r q}→atoms) :
      (∑v∈rows,‖D v*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q}=>fun p : atoms=>
          if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a v (singletonRepresentative r q) p else 0)‖^2)≤ cK*E := by
    let J := {q // singletonBlock r q}
    let : DecidableEq J := Classical.decEq J
    let f : J→ I := singletonRepresentative r
    have hf : Function.Injective f := singletonRepresentative_injective r
    by_cases hJ : Nonempty J
    · let : Nonempty J := hJ
      have hcolor (col : atoms→J) :
          (∑v∈rows,‖D v*(∏q : J,∑p : atoms,
            if col p=q then
              (if ∀j : {q // ¬singletonBlock r q},p≠t j then a v (f q) p else 0)
            else 0)‖^2)≤E := by
        let col' : Ideal O→J := fun p=>if h : p∈atoms then col ⟨p,h⟩ else Classical.choice hJ
        let keep : J→ Ideal O→Prop := fun q p=>col' p=q ∧
          ∀j : {q // ¬singletonBlock r q},p≠(t j).val
        let L' : J→Finset (Ideal O) := fun q=>(L (f q)).filter (keep q)
        have hsub (q : J) : L' q⊆L (f q) := Finset.filter_subset _ _
        have hdis : (((Finset.univ : Finset J) : Set J).PairwiseDisjoint L') := by
          intro q hq q' hq' hne
          apply Finset.disjoint_left.mpr
          intro p hp hp'
          have hq := (Finset.mem_filter.mp hp).2.1
          have hq' := (Finset.mem_filter.mp hp').2.1
          exact hne (hq.symm.trans hq')
        have hid (v : Row) (q : J) :
            (∑p : atoms,if col p=q then
              (if ∀j : {q // ¬singletonBlock r q},p≠t j then a v (f q) p else 0)
              else 0) =directPrimeSlot (u v) (L' q) (β (f q)) (P (f q)) := by
          rw [directPrimeSlot_sum_atoms _ _ atoms _ _ ((hsub q).trans (hLa (f q)))]
          refine Finset.sum_congr rfl fun p hp => ?_
          dsimp only [L']
          simp only [normalizedPrimeCoeff,Finset.mem_filter]
          have hkeep : keep q p.val ↔col p=q ∧∀j : {q // ¬singletonBlock r q},p≠t j := by
            simp only [keep,col',p.property,dite_true]
            constructor
            · rintro ⟨hc,hn⟩
              exact ⟨hc,fun j hh=>hn j (congrArg Subtype.val hh)⟩
            · rintro ⟨hc,hn⟩
              exact ⟨hc,fun j hh=>hn j (Subtype.ext hh)⟩
          dsimp only [a]
          simp only [normalizedPrimeCoeff]
          simp only [hkeep]
          by_cases hc : col p=q <;> by_cases ht : ∀j : {q // ¬singletonBlock r q},p≠t j
          <;> by_cases hl : p.val∈L (f q)
          <;> simp only [hc,ht,hl,and_self,and_false,false_and,true_and,ite_true,ite_false,mul_zero]
          all_goals split_ifs; simp only []
        have hbound := hsep f hf L' hsub hdis
        simpa only [hid] using hbound
      have hh := RepeatedPrimeSlots.injective_coloring_energy rows
        (fun v q p=>if ∀j : {q // ¬singletonBlock r q},p≠t j then a v (f q) p else 0)
        D E hE (by intro col; convert hcolor col using 1)
      apply hh.trans
      apply mul_le_mul_of_nonneg_right _ hE
      have hc : (Fintype.card J:ℝ)≤ max 1 (K:ℝ) :=
        (show (Fintype.card J:ℝ)≤(K:ℝ) by exact_mod_cast (singleton_card_le r).trans hK).trans (le_max_right _ _)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hc _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (Nat.mul_le_mul_left 2 ((singleton_card_le r).trans hK)))
    · let : IsEmpty J := not_nonempty_iff.mp hJ
      have hdis : (((Finset.univ : Finset J) : Set J).PairwiseDisjoint (fun q=>L (f q))) := by
        intro q
        exact isEmptyElim q
      have hh := hsep f hf (fun q=>L (f q)) (fun _=>Finset.Subset.refl _) hdis
      have hbound : (∑v∈rows,‖D v‖^2)≤E := by simpa using hh
      have hid (v : Row) : injectiveTuplePolynomial
          (fun q : J=>fun p : atoms=>if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a v (f q) p else 0)=1 := by simp [injectiveTuplePolynomial,Function.injective_of_subsingleton]
      have heq : (∑v∈rows,‖D v*injectiveTuplePolynomial
          (fun q : {q // singletonBlock r q}=>fun p : atoms=>
            if ∀j : {q // ¬singletonBlock r q},p≠t j then
              a v (singletonRepresentative r q) p else 0)‖^2)=(∑v∈rows,‖D v‖^2) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        have hp := hid v
        change injectiveTuplePolynomial
          (fun q : {q // singletonBlock r q}=>fun p : atoms=>
            if ∀j : {q // ¬singletonBlock r q},p≠t j then
              a v (singletonRepresentative r q) p else 0)=1 at hp
        rw [hp,mul_one]
      rw [heq]
      exact hbound.trans (le_mul_of_one_le_left hE hcK)
  have hh := product_energy_of_singletons rows a coeffNorm D B 256 (cK*E) hB
    (by norm_num) (mul_nonneg (zero_le_one.trans hcK) hE)
    (fun i p=>norm_nonneg _) hv he ha K hK (by
      intro r t
      calc
        _ = (∑v∈rows,‖D v*injectiveTuplePolynomial
          (fun q : {q // singletonBlock r q}=>fun p : atoms=>
            if ∀j : {q // ¬singletonBlock r q},p≠t j then
              a v (singletonRepresentative r q) p else 0)‖^2) := by
          refine Finset.sum_congr rfl fun v hv => ?_
          apply congrArg (fun z : ℂ=>‖D v*z‖^2)
          apply congrArg injectiveTuplePolynomial
          funext q p
          split_ifs <;> rfl
        _ ≤ _ := hsingle r t)
  have hid (v : Row) (i : I) : (∑p : atoms,a v i p)=directPrimeSlot (u v) (L i) (β i) (P i) :=
    (directPrimeSlot_sum_atoms _ _ atoms _ _ (hLa i)).symm
  have heq : (∑v∈rows,‖D v*(∏i,∑p : atoms,a v i p)‖^2)=
      (∑v∈rows,‖D v*(∏i,directPrimeSlot (u v) (L i) (β i) (P i))‖^2) := by
    refine Finset.sum_congr rfl fun v hv => ?_
    congr 2
    apply congrArg (D v * ·)
    exact Finset.prod_congr rfl (fun i _=>hid v i)
  rw [heq] at hh
  convert hh using 1
  dsimp [overlapCost,cK]
  ring

end
end OAI.SevenEighths.Deletion26

end Record1252270103Bootstrap.PR67
