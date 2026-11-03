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

public import Submissions.gao_general_number_fields_9672.Refinement9672.Inputs.NativePrimitiveLine03
public import Submissions.gao_general_number_fields_9672.Refinement9672.Inputs.NativeConductorInterpolation

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.BaselinePrimitive97

noncomputable section
open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

/-- Conductor-uniform primitive numerator bound. The independent old endpoint
is consumed only by the .97 line; the original convexity supplies admissible
interior growth. No new subconvexity theorem is assumed. -/
theorem primitive_line_12 (hF : NumberField.IsTotallyComplex F)
    (hbase : OldHeckeZeroFree31 F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (g : ℂ → ℂ), Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ t : ℝ,
          ‖g (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((17 / 40 : ℝ) + ε) *
              (2 + |t|) ^ A := by
  obtain ⟨Aₗ, hAₗ, HL⟩ := primitive_line_03 hF hbase
  obtain ⟨A₀, hA₀, HC⟩ := RawPrimitiveGrowth31.convex_core hF
  obtain ⟨C₀, hC₀, HC₀⟩ := HC (1 / 10) (by norm_num) (by norm_num)
  let k : ℕ := Nat.ceil (max Aₗ 1)
  have hkA : Aₗ ≤ (k : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := (le_max_right _ _).trans (Nat.le_ceil _)
  refine ⟨(k : ℝ), by positivity, fun ε hε => ?_⟩
  obtain ⟨Cₗ, hCₗ, HLε⟩ := HL ε hε
  obtain ⟨Cᵣ, hCᵣ, HRε⟩ := primitive_line_97 hF hbase ε hε
  refine ⟨6 ^ k * (Cₗ + Cᵣ), by positivity, fun ν hν g hg hgs t => ?_⟩
  let Q : ℝ := 1 + (Ideal.absNorm ν.conductor : ℝ)
  have hQ : 1 ≤ Q := by
    have h := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm ν.conductor)
    dsimp [Q]
    linarith
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hquad : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, (3 / 100 : ℝ) < s.re ∧ s.re < 97 / 100 →
        ‖g s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
    refine ⟨C₀ * Q ^ (11 / 20 : ℝ), A₀, by positivity, hA₀, fun s hs => ?_⟩
    have hgr := HC₀ ν hν g hg hgs s (by linarith [hs.1]) (by linarith [hs.2])
    have hexp : (1 + (1 / 10 : ℝ) - s.re) / 2 ≤ 11 / 20 := by linarith [hs.1]
    have hp := Real.rpow_le_rpow_of_exponent_le hQ hexp
    calc
      ‖g s‖ ≤ C₀ * Q ^ ((1 + (1 / 10 : ℝ) - s.re) / 2) * (2 + |s.im|) ^ A₀ := hgr
      _ ≤ C₀ * Q ^ (11 / 20 : ℝ) * (2 + |s.im|) ^ A₀ := by gcongr
      _ ≤ (C₀ * Q ^ (11 / 20 : ℝ)) * Real.exp (A₀ * (1 + |s.im|) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (Refinement9672Interpolation.height_rpow_le_quadratic_exp A₀ hA₀ s.im) (by positivity)
  have hleft : ∀ s : ℂ, s.re = (3 / 100 : ℝ) →
      ‖g s‖ ≤ (Cₗ + Cᵣ) * Q ^ ((47 / 100 : ℝ) + ε) * (2 + |s.im|) ^ k := by
    intro s hs
    have hsrep : s = (((3 / 100 : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [hs]
    have h := HLε ν hν g hg hgs s.im
    rw [← hsrep] at h
    have hT : 1 ≤ (2 + |s.im| : ℝ) := by linarith [abs_nonneg s.im]
    have hp : (2 + |s.im|) ^ Aₗ ≤ (2 + |s.im|) ^ k := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hT hkA
    calc
      ‖g s‖ ≤ Cₗ * Q ^ ((47 / 100 : ℝ) + ε) * (2 + |s.im|) ^ Aₗ := h
      _ ≤ (Cₗ + Cᵣ) * Q ^ ((47 / 100 : ℝ) + ε) * (2 + |s.im|) ^ k := by gcongr; linarith
  have hright : ∀ s : ℂ, s.re = (97 / 100 : ℝ) →
      ‖g s‖ ≤ (Cₗ + Cᵣ) * Q ^ ε * (2 + |s.im|) ^ k := by
    intro s hs
    have hsrep : s = (((97 / 100 : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [hs]
    have h := HRε ν hν g hg hgs s.im
    rw [← hsrep] at h
    have hT : 1 ≤ (2 + |s.im| : ℝ) := by linarith [abs_nonneg s.im]
    have hp : (2 + |s.im| : ℝ) ≤ (2 + |s.im|) ^ k := by
      have hb := Real.rpow_le_rpow_of_exponent_le hT hk1
      simpa only [Real.rpow_one, Real.rpow_natCast] using hb
    calc
      ‖g s‖ ≤ Cᵣ * Q ^ ε * (2 + |s.im|) := h
      _ ≤ (Cₗ + Cᵣ) * Q ^ ε * (2 + |s.im|) ^ k := by gcongr; linarith
  have hout := Refinement9672Interpolation.numerator_interpolation Q (Cₗ + Cᵣ) ε
    hQ (by positivity) k g hg hquad hleft hright t
  simpa only [Real.rpow_natCast] using hout

/-- Uniform conversion from primitive conductor to an arbitrary dyadic scale. -/
theorem primitive_line_12_scaled (hF : NumberField.IsTotallyComplex F)
    (hbase : OldHeckeZeroFree31 F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (U : ℝ), 1 ≤ U → 1 + (Ideal.absNorm ν.conductor : ℝ) ≤ c * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ t : ℝ,
          ‖g (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((17 / 40 : ℝ) + ε) * (2 + |t|) ^ A := by
  obtain ⟨A, hA, H⟩ := primitive_line_12 hF hbase
  refine ⟨A, hA, fun ε hε c hc => ?_⟩
  let δ := min ε (1 / 100)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  obtain ⟨C, hC, HC⟩ := H δ hδ
  refine ⟨C * max 1 c, by positivity, fun ν hν U hU hcond g hg hgs t => ?_⟩
  have hQ : (1 : ℝ) ≤ 1 + (Ideal.absNorm ν.conductor : ℝ) := by
    have h := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm ν.conductor)
    linarith
  have hscale := RawPrimitiveGrowth31.rpow_scale hc hU hQ hcond
    (e := (17 / 40 : ℝ) + δ) (by dsimp [δ]; positivity) (by dsimp [δ]; linarith [min_le_right ε (1 / 100)])
  have hUexp : U ^ ((17 / 40 : ℝ) + δ) ≤ U ^ ((17 / 40 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hU (by dsimp [δ]; linarith [min_le_left ε (1 / 100)])
  calc
    ‖g (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((17 / 40 : ℝ) + δ) * (2 + |t|) ^ A :=
      HC ν hν g hg hgs t
    _ ≤ C * (max 1 c * U ^ ((17 / 40 : ℝ) + ε)) * (2 + |t|) ^ A := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (hscale.trans (mul_le_mul_of_nonneg_left hUexp (by positivity))) hC.le
    _ = C * max 1 c * U ^ ((17 / 40 : ℝ) + ε) * (2 + |t|) ^ A := by ring

#print axioms primitive_line_12
#print axioms primitive_line_12_scaled

end
end DedekindZetaZeroFree.Quantitative.BaselinePrimitive97
