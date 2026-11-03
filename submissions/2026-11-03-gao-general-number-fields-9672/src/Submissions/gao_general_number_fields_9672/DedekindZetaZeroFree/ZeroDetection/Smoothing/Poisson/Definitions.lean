/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/ZeroDetection/Smoothing/Poisson/Definitions.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorDef

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

def σ₀ : ℝ := 22 / 25

def qExp : ℝ := 9 / 5

def c : ℝ := 1 / 100

def r : ℝ := 131 / 50

def r' : ℝ := 21 / 8

def α : ℝ := 317 / 500

variable (F : Type) [Field F] [NumberField F]

def a (U : ℝ) (n : Ideal (𝓞 F)) : ℝ :=
  ∑ᶠ d : Ideal (𝓞 F),
    if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ qExp then
      (Detector.idealMoebius F d : ℝ) else 0

def D (U : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (s : ℂ) : ℂ :=
  ∑ᶠ d : Ideal (𝓞 F),
    if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ qExp then
      (Detector.idealMoebius F d : ℂ) * ω d * (Ideal.absNorm d : ℂ) ^ (-s) else 0

variable {F}

def IsLZero (ω : Detector.PrimitiveFrequencyCharacter F) (s : ℂ) : Prop :=
  0 < s.re ∧ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re} ∧
    (∀ z : ℂ, 1 < z.re → g z = Detector.idealLSeries F ω.character z) ∧ g s = 0

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D₀ : FixedData S η)

def exceptionalSet (ρ U : ℝ) : Set D₀.Row :=
  {u | FixedData.Row.u u ≠ 1 ∧ U ≤ D₀.q u ∧ D₀.q u < 2 * U ∧
    ∃ s : ℂ, IsLZero (D₀.omega u) s ∧ σ₀ ≤ s.re ∧ |s.im| ≤ 4 * U ^ ρ}

end

end DedekindZetaZeroFree.Quantitative.DetectorDef
