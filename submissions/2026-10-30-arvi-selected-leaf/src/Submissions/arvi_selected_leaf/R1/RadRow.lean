/-
The radical row character of a natural row.

For a nonzero row `w` and a mask `m` (divisible by `λ` and `2`), a Hecke character `radRow η m w` whose
coefficients are `idealCoeff η I · idealRowHom (m⁶ w) I` and whose conductor is at most
`N(η) N(m) N(72) N(rad w)` (`exists_row_character_radical`). At `w = u g⁶` its coefficients are
`rootCommon η m g 0 I · idealRowHom u I` and its conductor is at most `N(η) N(m) N(72) N(u) N(g)`.
-/
import Submissions.arvi_selected_leaf.R1.Direct
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NonprincipalGate

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeRowClosure
open CenteredMomentHeckeExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-- The radical row character (the trivial character for `w = 0`). -/
def radRow (η : Character) (m w : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m) : Character :=
  if hw : w ≠ 0 then
    Classical.choose (ProbeRowRadicalConductor.exists_row_character_radical η m 1 w hm one_ne_zero hw
      hmLam hm2)
  else η

theorem radRow_spec (η : Character) (m w : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (hw : w ≠ 0) :
    (radRow η m w hm hmLam hm2).modulus.absNorm ≤ η.modulus.absNorm * (Ideal.span {m}).absNorm *
        (Ideal.span {(72 : O)}).absNorm * (Ideal.span {(1:O)^4*w}).radical.absNorm ∧
      ∀ n : O, elementCoeff (radRow η m w hm hmLam hm2) n = rowTwist (elementHom η) m 1 w n := by
  rw [radRow, dif_pos hw]
  exact Classical.choose_spec (ProbeRowRadicalConductor.exists_row_character_radical η m 1 w hm
    one_ne_zero hw hmLam hm2)

/-- The coefficients of the radical row character. -/
theorem radRow_coeff (η : Character) (m w : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (hw : w ≠ 0) (I : Ideal O) :
    idealCoeff (radRow η m w hm hmLam hm2) I = idealCoeff η I * idealRowHom (m^6 * w) I := by
  have h := idealCoeff_eq_row η (radRow η m w hm hmLam hm2) m 1 w (radRow_spec η m w hm hmLam hm2 hw).2 I
  simpa only [one_pow, mul_one] using h

/-- **At a sixth root** the radical row character is the root-common coefficient times the core row. -/
theorem radRow_coeff_root (η : Character) (m u g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m)
    (hm2 : (2:O) ∣ m) (hw : u * g^6 ≠ 0) (I : Ideal O) :
    idealCoeff (radRow η m (u * g^6) hm hmLam hm2) I = rootCommon η m g 0 I * idealRowHom u I := by
  rw [radRow_coeff η m (u * g^6) hm hmLam hm2 hw I]
  unfold rootCommon
  rw [show m^6 * (u * g^6) = (m^6 * g^6) * u by ring, idealRowHom_argument_mul]
  simp only [Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one]
  ring

/-- The radical of a row at a sixth root lies over the core times the root. -/
theorem radical_root_absNorm_le (u g : O) (hu : u ≠ 0) (hg : g ≠ 0) :
    ((Ideal.span {(1:O)^4 * (u * g^6)}).radical.absNorm : ℝ) ≤
      (Ideal.span {u}).absNorm * (Ideal.span {g}).absNorm := by
  have hle : (Ideal.span {u * g} : Ideal O) ≤ (Ideal.span {(1:O)^4 * (u * g^6)}).radical := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨6, ?_⟩
    rw [Ideal.mem_span_singleton]
    exact ⟨u^5, by ring⟩
  have hne : (Ideal.span {u * g} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hu hg)
  have : Finite (O ⧸ (Ideal.span {u * g} : Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient hne
  have h := FiniteConductor.absNorm_le_of_le hle
  have hspan : (Ideal.span {u * g} : Ideal O) = Ideal.span {u} * Ideal.span {g} :=
    (Ideal.span_singleton_mul_span_singleton u g).symm
  rw [hspan, map_mul] at h
  exact_mod_cast h

/-- **The conductor at a sixth root.** -/
theorem radRow_modulus_root (η : Character) (m u g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m)
    (hm2 : (2:O) ∣ m) (hu : u ≠ 0) (hg : g ≠ 0) :
    ((radRow η m (u * g^6) hm hmLam hm2).modulus.absNorm : ℝ) ≤
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm : ℕ) *
        ((Ideal.span {u}).absNorm * (Ideal.span {g}).absNorm) := by
  have hw : u * g^6 ≠ 0 := mul_ne_zero hu (pow_ne_zero 6 hg)
  have h := (radRow_spec η m (u * g^6) hm hmLam hm2 hw).1
  have hr := radical_root_absNorm_le u g hu hg
  have hc : (0:ℝ) ≤ (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm : ℕ) :=
    Nat.cast_nonneg _
  calc ((radRow η m (u * g^6) hm hmLam hm2).modulus.absNorm : ℝ)
      ≤ ((η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm *
          (Ideal.span {(1:O)^4*(u * g^6)}).radical.absNorm : ℕ) : ℝ) := by exact_mod_cast h
    _ = (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm : ℕ) *
          ((Ideal.span {(1:O)^4*(u * g^6)}).radical.absNorm : ℝ) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr hc

/-- **Non-principality** on a row that does not induce a fixed character. -/
theorem radRow_nonprincipal (η : Character) (Q : Ideal O) (m w : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m)
    (hm2 : (2:O) ∣ m) (hw : w ≠ 0)
    (hex : ¬CenteredExceptionalProfile.FixedInducingRow η Q m 1 w) :
    (radRow η m w hm hmLam hm2).residue ≠ 1 := by
  refine CenteredMomentNonprincipalGate.actual_row_nonprincipal η (radRow η m w hm hmLam hm2) Q m 1 w ?_ hex
  intro n
  rw [(radRow_spec η m w hm hmLam hm2 hw).2 n, one_mul]

end
end QRH.ArviSelectedLeaf.R1
