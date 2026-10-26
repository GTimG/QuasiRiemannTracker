import Candidate.Cycle63.Moment.PositiveRowFactors

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open HeckeFamily HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O

/-- The two genuine buffered plain estimates enter the literal retained row.
Every live normalized slot remains in the bound, to be charged at the same bin. -/
theorem actual_buffered_retained_plain_factors
    (R dmax τ ε e κ v : ℝ)
    (hR : 0 ≤ R) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1) (hv : 0 ≤ v)
    (hbudget : 12*e*(R+2)+8*κ+2*v ≤ ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax → 2 < Z^τ →
    ∀ {Dict : Type*} [Fintype Dict] (χ : Dict → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (a : ℝ) (i : ℕ),
      51/100 ≤ a → a ≤ 1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < a+2*e →
    ∀ (j : Dict) (η : Character) (m z : O) (reverse : Bool),
      (∀ I : Ideal O,
        idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I =
          if reverse then star (idealCoeff (χ j) I) else idealCoeff (χ j) I) →
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ),
      (∀ k, 0 < P k) →
    ∀ (W : Fin 2 → ℝ → ℂ) (X r A B : Fin 2 → ℝ) (t : ℝ),
      (∀ k, 0 < X k) → (∀ k, clippedScale (X k) = (Z^d)^(r k)) →
      (∀ k, 0 < A k) →
      (∀ k, Function.support (orientedProfile reverse (dilated (W k) (clipDilation (X k))))
        ⊆ Set.Icc (A k) (B k)) →
      (∀ k, ContDiff ℝ ∞ (orientedProfile reverse (dilated (W k) (clipDilation (X k))))) →
      (χ j).modulus.absNorm ≤ Z^d →
      (∀ k, 0 ≤ r k) → (∀ k, r k ≤ R) →
      |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^v →
      (∀ k, ∀ x ∈ Set.Icc (1-a-6*e) 2, ∀ u : ℝ,
        (1+|u|)^2*‖mellin (orientedProfile reverse (dilated (W k) (clipDilation (X k))))
          ((x : ℂ)+u*Complex.I)‖ ≤ profileBound 2) →
      (∀ k, ∀ x ∈ Set.Icc (1-a-6*e) 2, ∀ u : ℝ,
        (1+|u|)^(n+2)*‖mellin (orientedProfile reverse (dilated (W k) (clipDilation (X k))))
          ((x : ℂ)+u*Complex.I)‖ ≤ profileBound (n+2)) →
      ‖retainedPositiveRow η m 1 z (W 0) (W 1) S β P t (X 0) (X 1)‖^2 ≤
        C^2*(Z^d)^((2*a-1)*(r 0+r 1)+2*ε)*
          ∏ k, ‖normalizedSlot η m 1 z (S k) (β k) t (P k)‖^2 := by
  obtain ⟨n,C,hC,hplain⟩ := Cycle63.Physical.buffered_clipped_plain_bounds
    R dmax τ ε e κ v hR hdmax hτ hε he he' hκ hκ' hv hbudget profileBound hprofile
  refine ⟨n,C,hC,?_⟩
  intro Z d hZ hd hdm hT Dict _ χ hχ a i ha ha' hzero j η m z reverse hcoeff
    ι _ _ S β P hP W X r A B t hX hscale hA hsupport hsmooth hmod hr hrR
    hfreq hheight hm₂ hmn
  have hb (k : Fin 2) := (hplain Z d hZ hd hdm hT χ hχ a i ha ha' hzero
    j η m z reverse hcoeff (W k) (X k) (r k) t (A k) (B k)
    (hX k) (hscale k) (hA k) (hsupport k) (hsmooth k) hmod
    (hr k) (hrR k) hfreq hheight (hm₂ k) (hmn k)).1
  have hh := actual_retained_row_bound η m 1 z (W 0) (W 1) S β P t (X 0) (X 1)
    (hX 0) (hX 1) hP (C*(Z^d)^((2*a-1)*r 0+ε))
    (C*(Z^d)^((2*a-1)*r 1+ε))
    (fun k => ‖normalizedSlot η m 1 z (S k) (β k) t (P k)‖^2)
    (hb 0) (hb 1) (fun _ => le_rfl)
  apply hh.trans_eq
  have hZd : 0 < Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  rw [show (C*(Z^d)^((2*a-1)*r 0+ε))*(C*(Z^d)^((2*a-1)*r 1+ε)) =
      C^2*((Z^d)^((2*a-1)*r 0+ε)*(Z^d)^((2*a-1)*r 1+ε)) by ring,
    ←Real.rpow_add hZd]
  congr 2
  ring

#print axioms actual_buffered_retained_plain_factors
end
end OAI.SevenEighths.Cycle63Moment
