/- Copyright (c) 2026 Sil. Apache-2.0.
Reverse collision completion in the same positive physical norm.
Repeated blocks are frozen with their true absolute masses. The subsequent
induction will require full products only, with bounded finite exclusions.
-/
import Candidate.SilPrior.FourthPower.KernelCollisionInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Candidate.SilPrior.FourthPower.NativeCollisionEnergy
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths.Record12518109GainDeletion
open KernelCollisionEnergy KernelCollisionInverse

universe u v w
variable {I : Type u} {A : Type v} {Row : Type w} [Fintype I] [Fintype A]

/-- Only the lower singleton family is used for this one equality pattern. -/
theorem pattern_energy (rows : Finset Row) (ρ : Row→ℝ)
    (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L E : ℝ) (hρ : ∀u∈rows,0≤ρ u) (hB : 1≤B) (hL : 1≤L) (hE : 0≤E)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p)
    (N : ℕ) (hN : Fintype.card I≤N) (r : Setoid I)
    (hchild : ∀t : {q // ¬singletonBlock r q}→A,
      (∑u∈rows,ρ u*‖D u*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q}=>fun p=>
          if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a u (singletonRepresentative r q) p else 0)‖^2)≤E) :
    (∑u∈rows,ρ u*‖D u*patternPolynomial r (a u)‖^2)≤((L*B^N)^N)^2*E := by
  let G (t : {q // ¬singletonBlock r q}→A) (u : Row) :=
    D u*injectiveTuplePolynomial
      (fun q : {q // singletonBlock r q}=>fun p=>
        if ∀j : {q // ¬singletonBlock r q},p≠t j then
          a u (singletonRepresentative r q) p else 0)
  let F (t : {q // ¬singletonBlock r q}→A) (u : Row) :=
    if Function.Injective t then
      (∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,a u i (t q))*G t u
    else 0
  let mass (t : {q // ¬singletonBlock r q}→A) : ℝ :=
    ∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,v i (t q)
  have hm (t) : 0≤mass t := Finset.prod_nonneg
    (fun q _=>Finset.prod_nonneg (fun i _=>hv0 i (t q)))
  have hFG (t) (u) (hu : u∈rows) : ‖F t u‖≤mass t*‖G t u‖ := by
    dsimp only [F]
    split_ifs
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simp only [norm_prod]
      exact Finset.prod_le_prod₀ (fun q _=>Finset.prod_nonneg (fun i _=>norm_nonneg _))
        (fun q _=>Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>ha u hu i (t q)))
    · simpa only [norm_zero] using mul_nonneg (hm t) (norm_nonneg (G t u))
  have hh := weighted_physical_energy rows ρ F G mass E hρ hm
    (fun t u hu=>hFG t u hu) hchild
  have hmass : (∑t,mass t)≤(L*B^N)^N := collision_assignments_mass r v B L hB hL hv0 hv he N hN
  have hbound := hh.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun t _=>hm t)) hmass 2) hE)
  apply (le_of_eq ?_).trans hbound
  apply Finset.sum_congr rfl
  intro u _
  apply congrArg (fun z : ℂ=>ρ u*‖z‖^2)
  rw [freeze_collision_blocks,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only [F,G]
  split_ifs <;> ring

def stepCost (N : ℕ) (B L : ℝ) : ℝ :=
  2*(1+((2:ℝ)^(N*N)*(L*B^N)^N)^2)

theorem stepCost_one_le (N : ℕ) (B L : ℝ) : 1≤stepCost N B L := by
  unfold stepCost
  nlinarith [sq_nonneg ((2:ℝ)^(N*N)*(L*B^N)^N)]

/-- One reverse step. The equality pattern bottom is excluded from the
recursive premise, so every required child has strictly fewer live slots. -/
theorem inverse_step (rows : Finset Row) (ρ : Row→ℝ)
    (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L E : ℝ) (hρ : ∀u∈rows,0≤ρ u) (hB : 1≤B) (hL : 1≤L) (hE : 0≤E)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p)
    (N : ℕ) (hN : Fintype.card I≤N)
    (hfull : (∑u∈rows,ρ u*‖D u*(∏i,∑p,a u i p)‖^2)≤E)
    (hchild : ∀r : Setoid I,r≠⊥ → ∀t : {q // ¬singletonBlock r q}→A,
      (∑u∈rows,ρ u*‖D u*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q}=>fun p=>
          if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a u (singletonRepresentative r q) p else 0)‖^2)≤E) :
    (∑u∈rows,ρ u*‖D u*injectiveTuplePolynomial (a u)‖^2)≤stepCost N B L*E := by
  let R := (Finset.univ : Finset (Setoid I)).erase ⊥
  let F (r : R) (u : Row) := D u*patternPolynomial r.val (a u)
  let M : ℝ := (L*B^N)^N
  have hM : 0≤M := by dsimp [M]; positivity
  have hr (r : R) : (∑u∈rows,ρ u*‖F r u‖^2)≤M^2*E :=
    pattern_energy rows ρ a v D B L E hρ hB hL hE hv0 hv he ha N hN r.val
      (hchild r.val (Finset.mem_erase.mp r.property).1)
  have hh := weighted_physical_energy rows ρ F F (fun _=>1) (M^2*E) hρ
    (fun _=>zero_le_one) (by intros; simp) hr
  have hcard : (Fintype.card R:ℝ)≤(2:ℝ)^(N*N) := by
    exact_mod_cast (show Fintype.card R≤2^(N*N) from by
      rw [Fintype.card_coe]
      exact (Finset.card_le_univ R).trans (setoid_card_le N hN))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  have hcorr := hh.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (mul_nonneg (sq_nonneg M) hE))
  have hid (u : Row) : D u*injectiveTuplePolynomial (a u)=
      D u*(∏i,∑p,a u i p)-∑r : R,F r u := by
    rw [complete_collisions,mul_sub,Finset.mul_sum]
    congr 1
    exact (Finset.sum_coe_sort R (fun r : Setoid I=>D u*patternPolynomial r (a u))).symm
  have hpoint (u : Row) : ‖D u*injectiveTuplePolynomial (a u)‖^2≤
      2*‖D u*(∏i,∑p,a u i p)‖^2+2*‖∑r : R,F r u‖^2 := by
    rw [hid]
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le
      (D u*(∏i,∑p,a u i p)) (∑r : R,F r u)) 2
    nlinarith [sq_nonneg (‖D u*(∏i,∑p,a u i p)‖-‖∑r : R,F r u‖)]
  calc
    _ ≤ ∑u∈rows,ρ u*(2*‖D u*(∏i,∑p,a u i p)‖^2+2*‖∑r : R,F r u‖^2) :=
      Finset.sum_le_sum (fun u hu=>mul_le_mul_of_nonneg_left (hpoint u) (hρ u hu))
    _ = 2*(∑u∈rows,ρ u*‖D u*(∏i,∑p,a u i p)‖^2)+
        2*(∑u∈rows,ρ u*‖∑r : R,F r u‖^2) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
    _ ≤ 2*E+2*((2:ℝ)^(N*N))^2*(M^2*E) := by linarith
    _ = stepCost N B L*E := by unfold stepCost; dsimp [M]; ring

/-- A finite mask changes coefficients only at the listed atoms. -/
def mask {J : Type*} (a : J→A→ℂ) (R : J→Finset A) (j : J) (p : A) : ℂ :=
  if p∈R j then 0 else a j p

theorem avoid_image {J : Type*} [Fintype J] (t : J→A) (f : A→ℂ) (p : A) :
    (if ∀j,p≠t j then f p else 0) =
      if p∈Finset.univ.image t then 0 else f p := by
  have hh : p∈Finset.univ.image t ↔ ¬∀j,p≠t j := by simp [eq_comm]
  simp only [hh]
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem mask_union (f : A→ℂ) (R S : Finset A) (p : A) :
    (if p∈R then 0 else if p∈S then 0 else f p) =
      if p∈R∪S then 0 else f p := by
  simp only [Finset.mem_union]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- Closed finite induction. The premise contains only full products of
embedded original labels with at most N*n excluded atoms per live slot.
No injective-product energy is assumed. The loss is polynomial in L for
fixed N, so a subpower collision mass remains subpower after the induction. -/
theorem injective_depth (N : ℕ) (rows : Finset Row) (ρ : Row→ℝ) (D : Row→ℂ)
    (B L E : ℝ) (hρ : ∀u∈rows,0≤ρ u) (hB : 1≤B) (hL : 1≤L) (hE : 0≤E)
    (n : ℕ) : n≤N → ∀{J : Type u} [Fintype J]
      (a : Row→J→A→ℂ) (v : J→A→ℝ), Fintype.card J≤n →
      (∀j p,0≤v j p) → (∀j p,v j p≤B) → (∀j,(∑p,(v j p)^2)≤L*B^2) →
      (∀u∈rows,∀j p,‖a u j p‖≤v j p) →
      (∀(K : Type u) [Fintype K] (f : K↪J) (R : K→Finset A),
        (∀k,(R k).card≤N*n) →
        (∑u∈rows,ρ u*‖D u*(∏k,∑p,mask (fun k=>a u (f k)) R k p)‖^2)≤E) →
      (∑u∈rows,ρ u*‖D u*injectiveTuplePolynomial (a u)‖^2)≤
        (stepCost N B L)^(n+1)*E := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn J instJ a v hsize hv0 hv he ha hsource
    let C := stepCost N B L
    have hC : 1≤C := stepCost_one_le N B L
    have hEn : 0≤C^n*E := mul_nonneg (pow_nonneg (zero_le_one.trans hC) _) hE
    have hEEn : E≤C^n*E := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hC (n:=n)) hE
    have hfull : (∑u∈rows,ρ u*‖D u*(∏j,∑p,a u j p)‖^2)≤C^n*E := by
      have hh := hsource J (Function.Embedding.refl J) (fun _=>∅) (by intros; simp)
      apply (le_of_eq ?_).trans (hh.trans hEEn)
      simp [mask]
    have hchild (r : Setoid J) (hr : r≠⊥) (t : {q // ¬singletonBlock r q}→A) :
        (∑u∈rows,ρ u*‖D u*injectiveTuplePolynomial
          (fun q : {q // singletonBlock r q}=>fun p=>
            if ∀j : {q // ¬singletonBlock r q},p≠t j then
              a u (singletonRepresentative r q) p else 0)‖^2)≤C^n*E := by
      let m := Fintype.card {q // singletonBlock r q}
      have hm : m<n := (fewer_singleton_labels r hr).trans_le hsize
      let R₀ : Finset A := Finset.univ.image t
      have hR₀ : R₀.card≤N := by
        calc
          _ ≤ Fintype.card {q // ¬singletonBlock r q} := by
            simpa only [Finset.card_univ] using (Finset.card_image_le (f:=t) (s:=Finset.univ))
          _ ≤ Fintype.card (Quotient r) := Fintype.card_subtype_le _
          _ ≤ Fintype.card J := quotient_card_le r
          _ ≤ N := hsize.trans hn
      let a' (u : Row) (q : {q // singletonBlock r q}) (p : A) :=
        if ∀j : {q // ¬singletonBlock r q},p≠t j then a u (singletonRepresentative r q) p else 0
      let v' (q : {q // singletonBlock r q}) (p : A) := v (singletonRepresentative r q) p
      have ha' : ∀u∈rows,∀q p,‖a' u q p‖≤v' q p := by
        intro u hu q p
        dsimp only [a',v']
        split_ifs
        · exact ha u hu _ p
        · simpa only [norm_zero] using hv0 (singletonRepresentative r q) p
      have hsource' (K : Type u) [Fintype K] (f : K↪{q // singletonBlock r q})
          (R : K→Finset A) (hR : ∀k,(R k).card≤N*m) :
          (∑u∈rows,ρ u*‖D u*(∏k,∑p,mask (fun k=>a' u (f k)) R k p)‖^2)≤E := by
        let g : K↪J := ⟨fun k=>singletonRepresentative r (f k),
          (singletonRepresentative_injective r).comp f.injective⟩
        have hbudget (k : K) : (R k∪R₀).card≤N*n := calc
          _ ≤ (R k).card+R₀.card := Finset.card_union_le _ _
          _ ≤ N*m+N := Nat.add_le_add (hR k) hR₀
          _ = N*(m+1) := by ring
          _ ≤ N*n := Nat.mul_le_mul_left N (Nat.succ_le_iff.mpr hm)
        have hh := hsource K g (fun k=>R k∪R₀) hbudget
        apply (le_of_eq ?_).trans hh
        apply Finset.sum_congr rfl
        intro u _
        apply congrArg (fun z : ℂ=>ρ u*‖D u*z‖^2)
        apply Finset.prod_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro p _
        dsimp only [mask,a',g]
        rw [avoid_image]
        exact mask_union (a u (singletonRepresentative r (f k))) (R k) R₀ p
      have hh := ih m hm (hm.le.trans hn) a' v' (le_refl _)
        (fun q=>hv0 (singletonRepresentative r q)) (fun q=>hv (singletonRepresentative r q))
        (fun q=>he (singletonRepresentative r q)) ha' hsource'
      exact hh.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hC (Nat.succ_le_iff.mpr hm)) hE)
    have hh := inverse_step rows ρ a v D B L (C^n*E) hρ hB hL hEn hv0 hv he ha
      N (hsize.trans hn) hfull hchild
    apply hh.trans_eq
    change C*(C^n*E)=C^(n+1)*E
    rw [pow_succ]
    ring

theorem injective_energy_of_full_products (rows : Finset Row) (ρ : Row→ℝ)
    (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L E : ℝ) (hρ : ∀u∈rows,0≤ρ u) (hB : 1≤B) (hL : 1≤L) (hE : 0≤E)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p)
    (N : ℕ) (hN : Fintype.card I≤N)
    (hfull : ∀(J : Type u) [Fintype J] (f : J↪I) (R : J→Finset A),
      (∀j,(R j).card≤N*N) →
      (∑u∈rows,ρ u*‖D u*(∏j,∑p,mask (fun j=>a u (f j)) R j p)‖^2)≤E) :
    (∑u∈rows,ρ u*‖D u*injectiveTuplePolynomial (a u)‖^2)≤
      (stepCost N B L)^(N+1)*E :=
  injective_depth N rows ρ D B L E hρ hB hL hE N le_rfl a v hN hv0 hv he ha hfull

/-- The collision mass may depend on the selected small exponent. The
exponent is chosen first; the constant K is quantified afterwards. -/
theorem stepCost_subpower (N : ℕ) (B ε : ℝ) (hB : 1≤B) (hε : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀K : ℝ,1≤K → ∃C : ℝ,0<C ∧ ∀X : ℝ,1≤X →
      (stepCost N B (K*X^δ))^(N+1)≤C*X^ε := by
  let δ := ε/(2*(N:ℝ)*((N:ℝ)+1)+1)
  have hd : 0<2*(N:ℝ)*((N:ℝ)+1)+1 := by positivity
  have hδ : 0<δ := div_pos hε hd
  refine ⟨δ,hδ,?_⟩
  intro K hK
  let D : ℝ := (2:ℝ)^(N*N)*(K*B^N)^N
  have hD : 1≤D := by
    dsimp only [D]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hB)))
  let C : ℝ := (4*D^2)^(N+1)
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro X hX
  have hX0 : 0<X := zero_lt_one.trans_le hX
  let P : ℝ := (2:ℝ)^(N*N)*(K*X^δ*B^N)^N
  have hP : 1≤P := by
    dsimp only [P]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX hδ.le)) (one_le_pow₀ hB)))
  have hstep : stepCost N B (K*X^δ)≤4*P^2 := by
    change 2*(1+P^2)≤4*P^2
    nlinarith [sq_nonneg (P-1)]
  have hpow : (4*P^2)^(N+1)=C*X^(δ*(N:ℝ)*2*((N:ℝ)+1)) := by
    have hp : P=D*(X^δ)^N := by
      dsimp only [P,D]
      rw [show K*X^δ*B^N=(K*B^N)*X^δ by ring,mul_pow]
      ring
    rw [hp,mul_pow D ((X^δ)^N)]
    rw [show 4*(D^2*((X^δ)^N)^2)=(4*D^2)*((X^δ)^N)^2 by ring,mul_pow]
    rw [←Real.rpow_natCast (X^δ) N,←Real.rpow_mul hX0.le,
      ←Real.rpow_natCast (X^(δ*(N:ℝ))) 2,←Real.rpow_mul hX0.le]
    simp only [Nat.cast_ofNat]
    rw [←Real.rpow_natCast (X^((δ*(N:ℝ))*2)) (N+1),←Real.rpow_mul hX0.le]
    simp only [Nat.cast_add,Nat.cast_one,C]
  have hexp : δ*(N:ℝ)*2*((N:ℝ)+1)≤ε := by
    have heq := div_mul_cancel₀ ε (ne_of_gt hd)
    change δ*(2*(N:ℝ)*((N:ℝ)+1)+1)=ε at heq
    nlinarith
  calc
    _ ≤ (4*P^2)^(N+1) := pow_le_pow_left₀ (zero_le_one.trans (stepCost_one_le _ _ _)) hstep _
    _ = C*X^(δ*(N:ℝ)*2*((N:ℝ)+1)) := hpow
    _ ≤ C*X^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp) hC.le

/-- A finite-subset interface matching the canonical source. No uniformity
over arbitrary new coefficient families is required: every slot is an
original slot with a bounded finite mask. -/
theorem injective_energy_of_subsets (rows : Finset Row) (ρ : Row→ℝ)
    (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L E : ℝ) (hρ : ∀u∈rows,0≤ρ u) (hB : 1≤B) (hL : 1≤L) (hE : 0≤E)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p)
    (N : ℕ) (hN : Fintype.card I≤N)
    (hfull : ∀T : Finset I,∀R : I→Finset A,(∀i∈T,(R i).card≤N*N) →
      (∑u∈rows,ρ u*‖D u*(∏i∈T,∑p,mask (a u) R i p)‖^2)≤E) :
    (∑u∈rows,ρ u*‖D u*injectiveTuplePolynomial (a u)‖^2)≤
      (stepCost N B L)^(N+1)*E := by
  apply injective_energy_of_full_products rows ρ a v D B L E hρ hB hL hE hv0 hv he ha N hN
  intro K instK f R hR
  let T : Finset I := Finset.univ.image f
  let Q (i : I) : Finset A := (Finset.univ.filter (fun k=>f k=i)).biUnion R
  have hQ (k : K) : Q (f k)=R k := by ext p; simp [Q,f.injective.eq_iff]
  have hbudget (i : I) (hi : i∈T) : (Q i).card≤N*N := by
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    rw [hQ]
    exact hR k
  have hh := hfull T Q hbudget
  apply (le_of_eq ?_).trans hh
  apply Finset.sum_congr rfl
  intro u _
  apply congrArg (fun z : ℂ=>ρ u*‖D u*z‖^2)
  symm
  dsimp only [T]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro k _
    simp only [mask,hQ]
  · intro k _ l _ hkl
    exact f.injective hkl

end
end Candidate.SilPrior.FourthPower.NativeCollisionEnergy
