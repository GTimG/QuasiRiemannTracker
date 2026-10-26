import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace Cycle25.Energy

open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance zeroSlotFinite : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The energy without slots at every width and length, from the baseline's width induction at slot price
one, which needs only `β ≤ 1` of the zero supremum. -/
theorem nonfixed_zero_at (a b radial B L Mcap ε : ℝ)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hB : 0 ≤ B) (hM : 0 < Mcap) (hε : 0 < ε)
    (hbeta : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η₀) a b radial B L Mcap ε Z J S C := by
  have hcert := CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Fin 0) M ⊤ le_top (fun _ : ℝ => (0 : ℂ)) 1 1 a b radial B L 0 0 Mcap 1 ε
    (by norm_num) (by simp) contDiff_const (by norm_num) ha haUpper hb hrad hB hM
    (by norm_num) hε hbeta (by linarith [HeckeZeroSupremum.beta_le_one])
  obtain ⟨J, S, he⟩ := CenteredMomentEnergyCappedWidthInduction.certified_terminal
    (α := Fin 0) M ⊤ le_top (fun _ : ℝ => (0 : ℂ)) 1 a b radial B L 0 0 Mcap 1 ε
    hB hM.le (by norm_num) hε hcert
  refine ⟨J, S, fun η₀ Q hQM hQ0 hQt hQ72 => ?_⟩
  obtain ⟨C, _, hC, _, hz⟩ := he η₀ Q hQM hQ0 hQt hQ72
  exact ⟨C, hC, hz.mono fun _ hZ => ⟨hZ.1, hZ.2.1⟩⟩

end Cycle25.Energy

end
end Record1252270103Bootstrap.PR67
