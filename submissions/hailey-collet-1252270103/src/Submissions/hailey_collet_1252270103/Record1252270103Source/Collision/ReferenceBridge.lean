/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Full reference subset moments pay the marked-squarefree subset moments by
exact inclusion-exclusion, with one fixed ambient-cardinality constant. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.ActualEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
universe u v w
variable {I : Type u} [Fintype I] {A : Type v} [Fintype A] {Row : Type w}

def fullSubsetBound (rows : Finset Row) (a : Row→I→A→ℂ) (D : Row→ℂ) (bound : ℝ) : Prop :=
  ∀ (J : Type u) [Fintype J] (f : J↪I),
    (∑u∈rows,‖D u*(∏j,∑p,a u (f j) p)‖^2)≤bound

def collisionProjectionCost (B L : ℝ) (K : ℕ) : ℝ :=
  ((2:ℝ)^(K*K))^2*((L*B^K)^K)^2

theorem full_edge_family_card_le {J : Type u} [Fintype J] (K : ℕ)
    (hK : Fintype.card J≤K) :
    ((equalityEdges (I:=J)).powerset.card:ℝ)≤(2:ℝ)^(K*K) := by
  have he : (equalityEdges (I:=J)).card≤K*K := calc
    _≤Fintype.card (J×J) := Finset.card_le_univ _
    _=Fintype.card J*Fintype.card J := Fintype.card_prod _ _
    _≤K*K := Nat.mul_self_le_mul_self hK
  have hh : (equalityEdges (I:=J)).powerset.card≤2^(K*K) := by
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by decide) he
  exact_mod_cast hh

theorem projectedSubsetBound_of_fullSubsetBound (rows : Finset Row)
    (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L bound : ℝ) (hB : 1≤B) (hL : 1≤L) (hbound : 0≤bound)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p) (K : ℕ) (hK : Fintype.card I≤K)
    (hfull : fullSubsetBound rows a D bound) :
    projectedSubsetBound rows a D (collisionProjectionCost B L K*bound) := by
  intro J _ f
  have hJ : Fintype.card J≤K := (Fintype.card_le_of_injective f f.injective).trans hK
  have hs (E : Finset (J×J)) (hE : E⊆equalityEdges) :
      (∑u∈rows,‖D u*singletonPolynomial (edgeSetoid E) (fun j=>a u (f j))‖^2)≤bound := by
    let g : {q // singletonBlock (edgeSetoid E) q}↪J :=
      ⟨singletonRepresentative (edgeSetoid E),singletonRepresentative_injective _⟩
    exact hfull _ (g.trans f)
  have hh := injective_energy_of_full_singletons rows (fun u j=>a u (f j)) (fun j=>v (f j)) D
    B L bound hB hL (fun j=>hv0 (f j)) (fun j=>hv (f j)) (fun j=>he (f j))
    (fun u hu j=>ha u hu (f j)) K hJ hs
  have hc := (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr
    (full_edge_family_card_le (J:=J) K hJ)
  apply hh.trans
  have hp := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg ((L*B^K)^K)) hbound)
  simpa only [collisionProjectionCost,mul_assoc] using hp

open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- Direct inlet for the original normalized prime slots and any fixed row
factor, including weightedPlain with the exact keep and radial profile. -/
theorem normalized_projectedSubsetBound_of_fullSubsetBound
    (η : Character) (m A : O) (t : ℝ) (rows : Finset O) (D : O→ℂ)
    (S : I→Finset (Ideal O)) (β : I→Ideal O→ℂ) (P : I→ℝ)
    (atoms : Finset (Ideal O)) (B bound : ℝ) (hB : 1≤B) (hbound : 0≤bound)
    (hP : ∀i,1≤P i) (hβ : ∀i,∀p∈S i,‖β i p‖≤B)
    (hp : ∀i,∀p∈S i,p≠0) (hN : ∀i,∀p∈S i,(p.absNorm:ℝ)≤2*P i)
    (K : ℕ) (hK : Fintype.card I≤K)
    (hfull : fullSubsetBound rows
      (fun z i (p : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) p) D bound) :
    projectedSubsetBound rows
      (fun z i (p : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) p) D
      (collisionProjectionCost B 256 K*bound) := by
  let v := fun i (p : atoms)=>‖normalizedPrimeCoeff (S i) (β i) (P i) p‖
  apply projectedSubsetBound_of_fullSubsetBound rows _ v D B 256 bound hB (by norm_num) hbound
    (fun _ _=>norm_nonneg _)
    (fun i p=>normalizedPrimeCoeff_bound (S i) (β i) (P i) B (hP i)
      (zero_le_one.trans hB) (hβ i) p) _
    (fun z _ i p=>normalizedRowCoeff_norm η m A z t (S i) (β i) (P i) p) K hK hfull
  intro i
  dsimp only [v]
  rw [Finset.sum_coe_sort atoms (fun p=>‖normalizedPrimeCoeff (S i) (β i) (P i) p‖^2)]
  exact normalizedPrimeCoeff_energy atoms (S i) (β i) (P i) B (hP i)
    (zero_le_one.trans hB) (hβ i) (hp i) (hN i)

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.projectedSubsetBound_of_fullSubsetBound
#print axioms QRH.Record1252270103Source.Collision.normalized_projectedSubsetBound_of_fullSubsetBound
