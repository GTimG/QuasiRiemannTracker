import Candidate.Lib.Cyclotomic.Stickelberger.GaussSums
import Candidate.Lib.ClassField.GreenbergWiles.SelmerRelations

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000

/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

Set-up used by: Greenberg–Wiles formula, as a lower bound for the dual side.

This file: Membership in Selmer groups of cocycles; dropping conditions and places where
unramified. -/


open Matrix.Module
variable {E : Type} {Λ n B} [Field E] [EmbeddedNumberField E] [CommRing Λ] [Fintype n]
  [AddCommGroup B] [Module Λ B] {ρ : Gal(Ω/E) → Matrix n n Λ} {S T L K c}

lemma mem_selmerModule_iff : c ∈ selmerModule ρ S L B ↔ (∀ g h, c (g * h) = c g + ρ g • c h) ∧
  (∀ g ∈ inertiaAbove Sᶜ, c g = 0) ∧ c ∈ obeying L B ∧ IsLocallyConstant
  c := by simp [selmerModule, obeying, ↓iInf_union, ← mem_obeying_cocycleRels]; tauto

/-- A member c of the Selmer module for (S, L) lies in that for (T, K) if K ⊆ L and c vanishes
on inertia at all places of S outside T. -/
lemma selmerModule_mono (k : c ∈ selmerModule ρ S L B) (l : K ⊆ L) (h : ∀ v ∈ S \ T,
  ∀ g ∈ inertiaAbove {v}, c g = 0 := by simp) :
  c ∈ selmerModule ρ T K B := by simp_all [mem_selmerModule_iff, obeying, inertiaAbove]; grind
