/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Closed cardinality induction for collision removal. Its constant depends only
on the fixed slot count and coefficient bounds, never on slot widths/scales. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.Energy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
universe u v w
variable {A : Type v} [Fintype A] {Row : Type w}

def projectedSubsetBound {I : Type u} [Fintype I] (rows : Finset Row)
    (a : Row→I→A→ℂ) (D : Row→ℂ) (bound : ℝ) : Prop :=
  ∀ (J : Type u) [Fintype J] (f : J↪I),
    (∑u∈rows,‖D u*injectiveTuplePolynomial (fun j=>a u (f j))‖^2)≤bound

def collisionGrowth (B L : ℝ) (K : ℕ) : ℝ :=
  2*(1+((2:ℝ)^(K*K))^2*((L*B^K)^K)^2)

theorem collisionGrowth_one_le (B L : ℝ) (K : ℕ) : 1≤collisionGrowth B L K := by
  unfold collisionGrowth
  nlinarith [mul_nonneg (sq_nonneg ((2:ℝ)^(K*K))) (sq_nonneg ((L*B^K)^K))]

theorem edge_family_card_le {I : Type u} [Fintype I] (K : ℕ)
    (hK : Fintype.card I≤K) :
    (((equalityEdges (I:=I)).powerset.erase ∅).card:ℝ)≤(2:ℝ)^(K*K) := by
  have he : (equalityEdges (I:=I)).card≤K*K := calc
    _≤Fintype.card (I×I) := Finset.card_le_univ _
    _=Fintype.card I*Fintype.card I := Fintype.card_prod _ _
    _≤K*K := Nat.mul_self_le_mul_self hK
  have hh : ((equalityEdges (I:=I)).powerset.erase ∅).card≤2^(K*K) :=
    (Finset.card_erase_le).trans (by
      rw [Finset.card_powerset]
      exact Nat.pow_le_pow_right (by decide) he)
  exact_mod_cast hh

/-- All projected subset moments imply the full product moment. Embeddings
only reindex original slots; their coefficient functions are unchanged. -/
theorem full_energy_cardinality {I : Type u} [Fintype I]
    (rows : Finset Row) (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L bound : ℝ) (hB : 1≤B) (hL : 1≤L) (hbound : 0≤bound)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p) (K : ℕ) (hK : Fintype.card I≤K)
    (hproj : projectedSubsetBound rows a D bound) :
    (∑u∈rows,‖D u*(∏i,∑p,a u i p)‖^2)≤(collisionGrowth B L K)^K*bound := by
  have hg : 1≤collisionGrowth B L K := collisionGrowth_one_le B L K
  have aux : ∀n : ℕ,∀ (J : Type u) [Fintype J], Fintype.card J≤n → Fintype.card J≤K →
      ∀ (a : Row→J→A→ℂ) (v : J→A→ℝ),
      (∀i p,0≤v i p) → (∀i p,v i p≤B) →
      (∀i,(∑p,(v i p)^2)≤L*B^2) →
      (∀u∈rows,∀i p,‖a u i p‖≤v i p) → projectedSubsetBound rows a D bound →
      (∑u∈rows,‖D u*(∏i,∑p,a u i p)‖^2)≤(collisionGrowth B L K)^n*bound := by
    intro n
    induction n with
    | zero =>
      intro J _ hn hJK a v hv0 hv he ha hp
      have hc : Fintype.card J=0 := by omega
      letI : IsEmpty J := Fintype.card_eq_zero_iff.mp hc
      have hi := hp J (Function.Embedding.refl J)
      have hid (u : Row) : injectiveTuplePolynomial (a u)=∏i,∑p,a u i p := by
        unfold injectiveTuplePolynomial
        simp only [Function.injective_of_subsingleton,ite_true]
        exact (Fintype.prod_sum (a u)).symm
      simpa only [Function.Embedding.refl_apply,hid,pow_zero,one_mul] using hi
    | succ n ih =>
      intro J _ hn hJK a v hv0 hv he ha hp
      have hinj := hp J (Function.Embedding.refl J)
      simp only [Function.Embedding.refl_apply] at hinj
      have hs (E : Finset (J×J)) (hE : E⊆equalityEdges) (hne : E.Nonempty) :
          (∑u∈rows,‖D u*singletonPolynomial (edgeSetoid E) (a u)‖^2)≤
            (collisionGrowth B L K)^n*bound := by
        let f : {q // singletonBlock (edgeSetoid E) q}↪J :=
          ⟨singletonRepresentative (edgeSetoid E),singletonRepresentative_injective _⟩
        have hc := singleton_card_lt_of_edges E hE hne
        have hcn : Fintype.card {q // singletonBlock (edgeSetoid E) q}≤n := by omega
        apply ih _ hcn (Nat.le_trans (Nat.le_of_lt hc) hJK)
          (fun u j=>a u (f j)) (fun j=>v (f j))
          (fun j=>hv0 (f j)) (fun j=>hv (f j)) (fun j=>he (f j))
          (fun u hu j=>ha u hu (f j))
        intro H _ g
        exact hp H (g.trans f)
      have hstep := full_energy_of_injective_and_smaller rows a v D B L bound
        ((collisionGrowth B L K)^n*bound) hB hL hv0 hv he ha K hJK hinj hs
      have hc := edge_family_card_le (I:=J) K hJK
      have hcsq := (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hc
      have hp0 : 0≤(collisionGrowth B L K)^n := pow_nonneg (zero_le_one.trans hg) _
      have hp1 : 1≤(collisionGrowth B L K)^n := one_le_pow₀ hg
      have hn0 : 0≤(((L*B^K)^K)^2)*((collisionGrowth B L K)^n*bound) := by positivity
      have hdiag := mul_le_mul_of_nonneg_right hcsq hn0
      have hb := mul_le_mul_of_nonneg_right hp1 hbound
      apply hstep.trans
      calc
        _≤2*((collisionGrowth B L K)^n*bound)+
          2*((2:ℝ)^(K*K))^2*(((L*B^K)^K)^2*((collisionGrowth B L K)^n*bound)) := by
            nlinarith
        _=(collisionGrowth B L K)^(n+1)*bound := by
          rw [pow_succ]
          unfold collisionGrowth
          ring
  exact aux K I hK hK a v hv0 hv he ha hproj

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.full_energy_cardinality
