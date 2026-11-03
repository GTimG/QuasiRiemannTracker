/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/ZeroDetection/Smoothing/Poisson/Definitions.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.DetectorDef

noncomputable section

open _root_.DedekindZetaZeroFree
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

end Refinement9672
