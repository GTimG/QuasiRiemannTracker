import Candidate.Target836.Target836Unconditional
import Candidate.Target830.Parameters
import Candidate.Cycle25.Energy.Endpoint

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI.SevenEighths.Target830.Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
local notation "O" => HeckeFamily.O

def incumbentKappa : ℝ := kappa0

/-- This is the frozen accepted theorem, not the target currently being proved. -/
theorem accepted_beta : HeckeZeroSupremum.beta ≤ (218709/250000 : ℝ) := by
  exact Target836.FinalAssembly.beta_le_rational

theorem incumbent_kappa_bound : 2*HeckeZeroSupremum.beta-1 ≤ incumbentKappa := by
  have h := accepted_beta
  norm_num [incumbentKappa,kappa0]
  linarith

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Complete positive/zero incumbent pair at accepted kappa, with degree and
profile control fixed before the base character and the moving row data.
The common mesh is the existing compact mesh used by accepted callers. -/
theorem accepted_incumbent
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η0 : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η0 ≠ 0 → internalQ Q η0 ≠ ⊤ →
      internalQ Q η0 ≤ Ideal.span {(72 : O)} →
      ∃ C0 C1 : ℝ, 0 < C0 ∧ 0 < C1 ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η0) a b radial Bmask L Mcap ε Z degree S C0 ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε incumbentKappa
          Z η0 Q degree S C1 := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap incumbentKappa ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap
    (by norm_num [incumbentKappa,kappa0]) hε hbeta incumbent_kappa_bound
  obtain ⟨degree, S, hbound⟩ := certified_terminal (α := α) M H hH W bslot a b radial
    Bmask L lo hi Mcap incumbentKappa ε hmask hMcap.le
    (by norm_num [incumbentKappa,kappa0]) hε hcert
  have hmesh := Cycle25.Energy.compact_mesh_le Mcap Bmask L incumbentKappa ε hMcap.le hmask hε
    (by norm_num [incumbentKappa,kappa0]) (by norm_num [incumbentKappa,kappa0])
  refine ⟨degree, S, ?_⟩
  intro η0 Q hQM hQ0 hQt hQ72
  obtain ⟨C0, C1, hC0, hC1, hev⟩ := hbound η0 Q hQM hQ0 hQt hQ72
  refine ⟨C0, C1, hC0, hC1, ?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1, hZ.2.1, ?_⟩
  intro T theta w sigma v t height hw hwL hsiglo hsighi hheight hv s hQ hs p
    X1 X2 hX1 hX2 hLX1 hLX2 hcapacity
  exact hZ.2.2 T theta w sigma v t height hw (fun i => (hwL i).trans hmesh)
    hsiglo hsighi hheight hv s hQ hs p X1 X2 hX1 hX2 hLX1 hLX2 hcapacity

end
end OAI.SevenEighths.Target830.Source

#print axioms OAI.SevenEighths.Target830.Source.accepted_beta
#print axioms OAI.SevenEighths.Target830.Source.incumbent_kappa_bound
#print axioms OAI.SevenEighths.Target830.Source.accepted_incumbent
