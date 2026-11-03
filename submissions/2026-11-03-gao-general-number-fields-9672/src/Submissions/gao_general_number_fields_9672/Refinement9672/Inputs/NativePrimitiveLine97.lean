/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Noncircular successor input module, 2026-11-03, Zhongpai Gao with AI assistance.
Apache-2.0. Original theorem/dependency attribution below is retained.
Input module paths are relocated only; declaration namespaces stay original.
The old Hecke endpoint is supplied from the disjoint frozen original proof DAG.
Full native-import checking and successor endpoint verification remain pending.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.Inputs.NativePrimitiveStripBootstrap
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.PrimitiveGrowth
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDiskBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.BaselinePrimitive97

noncomputable section
open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

/-- The independently frozen original theorem, retaining its original endpoint.
This is a parameter until the original proof DAG is imported under a disjoint name. -/
def OldHeckeZeroFree31 (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (m : Ideal (𝓞 F)) (_ : m ≠ ⊥) (χ : RayClassCharacter F m),
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 31 / 32 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0

structure PrimitiveEntire (F : Type) [Field F] [NumberField F] where
  ν : Detector.PrimitiveFrequencyCharacter F
  nonprincipal : ¬ ν.character.IsPrincipal
  L : ℂ → ℂ
  entire : Differentiable ℂ L
  eq_series : ∀ s : ℂ, 1 < s.re → L s = Detector.idealLSeries F ν.character s

def primitiveEulerLog (ν : Detector.PrimitiveFrequencyCharacter F) (s : ℂ) : ℂ :=
  ∑' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥},
    ∑' k : ℕ, ν.character (P.1 ^ (k + 1)) /
      (((k : ℂ) + 1) * (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s))

theorem primitiveEntire_nonzero (hbase : OldHeckeZeroFree31 F)
    (i : PrimitiveEntire F) (s : ℂ) (hs : (31 / 32 : ℝ) < s.re) : i.L s ≠ 0 := by
  obtain ⟨f, hf, hfentire, hfseries, hfnz⟩ :=
    hbase i.ν.conductor i.ν.conductor_ne_zero i.ν.character
  have hfEq : ∀ z : ℂ, 1 < z.re → f z = Detector.idealLSeries F i.ν.character z := by
    intro z hz
    rw [← (hfseries z hz).tsum_eq]
    unfold Detector.idealLSeries
    refine tsum_congr fun I => ?_
    by_cases hI : I = ⊥
    · subst I
      simp [(i.ν.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
    · simp [hI]
  have heq : i.L = f := RowHeckeBridge.entire_eq_of_eq_right i.entire
    (hfentire i.nonprincipal) (fun z hz => (i.eq_series z hz).trans (hfEq z hz).symm)
  rw [heq]
  exact hfnz s hs (Or.inr i.nonprincipal)

/-- Actual native polynomial growth and actual native Euler logarithms are closed
here. Only the independent old zero-free theorem remains an explicit parameter. -/
theorem primitive_line_97 (hF : NumberField.IsTotallyComplex F)
    (hbase : OldHeckeZeroFree31 F) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (g : ℂ → ℂ), Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ t : ℝ,
          ‖g (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ε * (2 + |t|) := by
  have hQ : ∀ i : PrimitiveEntire F,
      (1 : ℝ) ≤ 1 + (Ideal.absNorm i.ν.conductor : ℝ) := fun i => by
    have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm i.ν.conductor)
    linarith
  have hstrip : ∃ v : ℝ, 0 ≤ v ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (i : PrimitiveEntire F) (s : ℂ), (4 / 5 : ℝ) ≤ s.re → s.re ≤ 4 →
        ‖i.L s‖ ≤ K * (1 + (Ideal.absNorm i.ν.conductor : ℝ)) ^ ((11 : ℝ) / 10) *
          (2 + |s.im|) ^ v := by
    obtain ⟨v, hv, H⟩ := RawPrimitiveGrowth31.primitive_strip_growth hF
    obtain ⟨K, hK, HK⟩ := H 1 (by norm_num) 1 (by norm_num)
    refine ⟨v, hv, K, hK, fun i s hslo hshi => ?_⟩
    have hb := HK i.ν i.nonprincipal (1 + (Ideal.absNorm i.ν.conductor : ℝ))
      (hQ i) (by simp) i.L i.entire i.eq_series s.re hslo hshi s.im
    rw [show (1 : ℝ) / 10 + 1 = 11 / 10 by norm_num] at hb
    simpa only [Complex.re_add_im] using hb
  have hEuler : ∃ A : ℝ, 0 < A ∧ ∀ i : PrimitiveEntire F,
      AnalyticOnNhd ℂ (primitiveEulerLog i.ν) {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, (1 : ℝ) < s.re → Complex.exp (primitiveEulerLog i.ν s) = i.L s) ∧
      (∀ s : ℂ, (1001 / 1000 : ℝ) ≤ s.re → ‖primitiveEulerLog i.ν s‖ ≤ A) := by
    obtain ⟨A, hA, HA⟩ := ReciprocalLogDiskAux.euler_log_facts F
    refine ⟨A, hA, fun i => ⟨(HA i.ν).1, ?_, (HA i.ν).2.2⟩⟩
    intro s hs
    exact ((HA i.ν).2.1 s hs).trans (i.eq_series s hs).symm
  have H := PrimitiveStripBootstrap.subpower_line_97_of_strip
    (fun i : PrimitiveEntire F => i.L) (fun i => primitiveEulerLog i.ν)
    (fun i => 1 + (Ideal.absNorm i.ν.conductor : ℝ)) hQ
    (fun i => i.entire) (primitiveEntire_nonzero hbase) hstrip hEuler
  intro ε hε
  obtain ⟨C, hC, HC⟩ := H ε hε
  exact ⟨C, hC, fun ν hν g hg hgs t => HC ⟨ν, hν, g, hg, hgs⟩ t⟩

/-- Conductor normalization is uniform in the dyadic bound U, with height power 1. -/
theorem primitive_line_97_scaled (hF : NumberField.IsTotallyComplex F)
    (hbase : OldHeckeZeroFree31 F) :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (U : ℝ), 1 ≤ U → 1 + (Ideal.absNorm ν.conductor : ℝ) ≤ c * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ t : ℝ,
          ‖g (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ε * (2 + |t|) := by
  intro ε hε c hc
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  obtain ⟨C, hC, HC⟩ := primitive_line_97 hF hbase δ hδ
  refine ⟨C * max 1 c, by positivity, fun ν hν U hU hcond g hg hgs t => ?_⟩
  have hQ : (1 : ℝ) ≤ 1 + (Ideal.absNorm ν.conductor : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm ν.conductor)
    linarith
  have hscale := RawPrimitiveGrowth31.rpow_scale hc hU hQ hcond hδ.le (min_le_right ε 1)
  have hUexp : U ^ δ ≤ U ^ ε := Real.rpow_le_rpow_of_exponent_le hU (min_le_left ε 1)
  calc ‖g (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ δ * (2 + |t|) := HC ν hν g hg hgs t
    _ ≤ C * (max 1 c * U ^ ε) * (2 + |t|) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (hscale.trans (mul_le_mul_of_nonneg_left hUexp (by positivity))) hC.le
    _ = C * max 1 c * U ^ ε * (2 + |t|) := by ring

section Fixed

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem raw_primPlus_line_97 (hbase : OldHeckeZeroFree31 F) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 1 ≤ U → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (RawFixed.FixedData.primPlus D u).character s) →
          ∀ t : ℝ,
            ‖g (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C * U ^ ε * (2 + |t|) := by
  obtain ⟨c, hc, hcond⟩ := RawHeckeIdentification31.plus_conductor_bound D
  intro ε hε
  obtain ⟨C, hC, HC⟩ := primitive_line_97_scaled
    (RawPrimitiveGrowth31.totallyComplex D) hbase ε hε (2 * c) (by positivity)
  refine ⟨C, hC, fun u hu U hU hq g hg hgs t => ?_⟩
  refine HC (RawFixed.FixedData.primPlus D u) ((RawFixed.FixedData.pkg D).nonprincipal u hu).1
    U hU ?_ g hg hgs t
  have h2 := hcond u
  have h3 := mul_le_mul_of_nonneg_left hq.le hc.le
  linarith

theorem allowed_primPlus_line_97 (hbase : OldHeckeZeroFree31 F) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.toFrequency.u ≠ 1 →
        ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (D.inducers u).plus.character s) →
          ∀ t : ℝ,
            ‖g (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C * U ^ ε * (2 + |t|) := by
  obtain ⟨c, hc, hcond⟩ := ConvexBridge.conductor_bound' D
  have hF : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  intro ε hε
  obtain ⟨C, hC, HC⟩ := primitive_line_97_scaled hF hbase ε hε (2 * c) (by positivity)
  refine ⟨C, hC, fun u hu U hU hUq hq g hg hgs t => ?_⟩
  have hq1 : 1 ≤ D.q u := (by norm_num : (1 : ℝ) ≤ 2).trans (hU.trans hUq)
  refine HC (D.inducers u).plus (RowNonprincipal.inducers_nonprincipal D u hu).1
    U (by linarith) ?_ g hg hgs t
  have h2 := (hcond u hq1).1
  have h3 := mul_le_mul_of_nonneg_left hq.le hc.le
  linarith

end Fixed

#print axioms primitiveEntire_nonzero
#print axioms primitive_line_97
#print axioms primitive_line_97_scaled
#print axioms raw_primPlus_line_97
#print axioms allowed_primPlus_line_97

end

end DedekindZetaZeroFree.Quantitative.BaselinePrimitive97
