/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/CharacterSums/DavenportHasse/PolynomialWeights.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib

@[expose] public section

open Polynomial

namespace DavenportHasse

noncomputable section
open scoped Classical

variable {k : Type*} [Field k] [Fintype k]

def monicOfCoeffs (d : ℕ) (c : Fin d → k) : k[X] :=
  X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ)

def wt (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (f : k[X]) : ℂ :=
  χ ((-1) ^ f.natDegree * f.coeff 0) * ψ (-f.nextCoeff)

def a (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (d : ℕ) : ℂ :=
  ∑ c : Fin d → k, wt χ ψ (monicOfCoeffs d c)

def b (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ m.divisors, ∑ c : Fin d → k,
    if Irreducible (monicOfCoeffs d c) then (d : ℂ) * wt χ ψ (monicOfCoeffs d c) ^ (m / d) else 0

end

end DavenportHasse
