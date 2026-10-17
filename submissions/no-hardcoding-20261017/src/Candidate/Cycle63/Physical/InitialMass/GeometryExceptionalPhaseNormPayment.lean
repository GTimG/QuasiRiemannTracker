import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical SchwartzMap
open CenteredMomentFirstAnnularInput
open HeckeFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The main exceptional consumer keeps the arbitrary first detector independent
of the second ball-profile norm. Saved constants precede the detector and all
moving source, allocation, ray and height data. -/
def actual_geometry_main_exceptional_phase_norm_payment
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (ε δ θ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0<slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1) :=
  actual_geometry_main_exceptional_norm_payment wlo whi hwlo hwhi lo hi
    ε δ θ hε hδ hθ η b bs hb hbs slotlo εalloc εcount ξ hslot hea hec hξ hξ₁

/-- The extracted exceptional consumer has independent first detector and
second ball-profile norm, independent first/second heights, and the literal
factor 56/P exactly once. Its saved constants precede these moving data. -/
theorem actual_geometry_error_exceptional_phase_norm_payment
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (ε δ θ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0<slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),
      ∀Qfix : Ideal O,Qfix≠0 → Qfix≠⊤ → Qfix≤Ideal.span {(72:O)} →
      ∃Kfix Cd Da : ℝ,0<Kfix ∧ 0<Cd ∧ 0<Da ∧
        ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ GeometryExceptionalErrorNormFullSpec wlo whi lo hi ε δ θ η
          b bs slotlo εalloc εcount ξ J Sp Ck Qfix Kfix Cd Da Z :=
  actual_geometry_error_exceptional_norm_full wlo whi hwlo hwhi lo hi
    ε δ θ hε hδ hθ η b bs hb hbs slotlo εalloc εcount ξ hslot hea hec hξ hξ₁

end
end OAI.SevenEighths.Cycle63InitialMass

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_exceptional_phase_norm_payment
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_error_exceptional_phase_norm_payment
