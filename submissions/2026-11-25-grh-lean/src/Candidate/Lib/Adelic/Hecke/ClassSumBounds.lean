import Candidate.Lib.Weil.Construction.FockThetaFunctions
import Candidate.Lib.CM.FormalGroup.FormalHeight
import Candidate.Lib.LocalGL.Green.LabelIdempotents
import Candidate.Lib.SiegelWeil.Formula.ZeroTermHeight
import Candidate.Lib.ClassField.HeckeCharacter.LevelModulus
import Candidate.Lib.Cohomology.Etale.TestRings

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000

/-! Part of: Abstract Hecke operators of a pair (G,K), level eigenspaces, weighted class sums (known
result; see Lib.Adelic.Hecke.ClassMean).

This file: Class sums stay integral after clearing automorphism orders; triangle inequality for
their norms. -/


open NumberField HasFiniteType Nat
variable {E V} [Field E] [CMType E] [Fintype V] {p} [Fact (Nat.Prime p)] {κ : InfinitePlace E → _}
  {G} [Group G] [TopologicalSpace G] {Γ K} [@HasFiniteType G _ Γ K _] {B} {f : G →
  WeylIndex V κ → ℂ}

lemma weylGauge_classSum_le_one g {e A} [PadicPlace p] (hA : ∀ x,
  Nat.card (classAut Γ K x) ∣ A) {c : ℂ} (h : ∀ x, weylGauge κ e g (c • f x) ≤ 1) : weylGauge κ e g
  ((A * c) • classSum Γ K f) ≤ 1 := by simpa [mul_smul,
  cast_smul_eq_nsmul] using! smul_classSum_mem (AddSubmonoid.mk ⟨{x | weylGauge .. ≤ 1},
  by simp_all [weylGauge, (IsUltrametricDist.norm_add_le_max ..).trans]⟩ (by simp [weylGauge])) hA h

lemma sqrt_weylNormSq_classSum_le (σ : ℂ ≃+* ℂ) (h : ∀ x, √(weylNormSq (σ ∘ f x)) ≤
  B) : √(weylNormSq (σ ∘ classSum Γ K f)) ≤ Nat.card (DoubleCosets Γ K) * B := by
  simp [classSum]; grw [sqrt_weylNormSq_sum_le]
  simp [← algebraMap_smul ℂ]; grw [cast_inv_le_one, h]; simp
