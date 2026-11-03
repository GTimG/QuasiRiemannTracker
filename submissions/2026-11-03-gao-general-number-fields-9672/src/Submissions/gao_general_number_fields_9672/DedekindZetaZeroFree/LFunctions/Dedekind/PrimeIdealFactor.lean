/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Dedekind/PrimeIdealFactor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Dedekind.LocalFactor

@[expose] public section

/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/PrimeIdealFactor.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

open Ideal IsDedekindDomain

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

noncomputable def primeIdealNorm (P : HeightOneSpectrum (𝓞 K)) : ℕ :=
  absNorm P.asIdeal

lemma one_lt_primeIdealNorm (P : HeightOneSpectrum (𝓞 K)) :
    1 < primeIdealNorm K P := by
  apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
  constructor
  · simpa [primeIdealNorm, Ideal.absNorm_eq_zero_iff] using P.ne_bot
  · simpa [primeIdealNorm, Ideal.absNorm_eq_one_iff] using P.isPrime.ne_top

noncomputable def primeIdealFactor (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  localFactor (primeIdealNorm K P) s

end DedekindZetaZeroFree.Odlyzko
