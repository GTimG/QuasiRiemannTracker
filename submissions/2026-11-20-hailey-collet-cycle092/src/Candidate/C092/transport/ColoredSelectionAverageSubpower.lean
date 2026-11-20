/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Actual selected-image multiplicity, uniformly subpower before pricing. -/
import Candidate.C092.transport.ColoredSelectionAverageMultiplicity
import Candidate.C092.transport.RawSidesZeroTailGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredSelectionAverage
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The common selected radius has a fixed polynomial cap. The exponent 48
    is used only inside a divisor subpower estimate. -/
theorem actual_radius_cap (Z K W : ℝ) (hZ : 3 ≤ Z) (hK : 0 ≤ K)
    (hKcap : K ≤ Z^(40:ℝ)) (hW : 0 ≤ W) (hWcap : W ≤ Z) :
    16*K*W^4 ≤ Z^(48:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) hZ
  have h16 : (16:ℝ) ≤ Z^4 := by
    calc (16:ℝ) ≤ 3^4 := by norm_num
         _ ≤ Z^4 := pow_le_pow_left₀ (by norm_num) hZ 4
  calc
    16*K*W^4 ≤ Z^4*Z^(40:ℝ)*Z^4 :=
      mul_le_mul (mul_le_mul h16 hKcap hK (by positivity))
        (pow_le_pow_left₀ hW hWcap 4) (by positivity) (by positivity)
    _ = Z^(48:ℝ) := by
      rw [←Real.rpow_natCast Z 4,←Real.rpow_add hz,←Real.rpow_add hz]
      norm_num

/-- Native divisor-image multiplicity is discharged for the actual selected
    scale and width quota, uniformly over every genuine finite source. -/
theorem actual_multBound_subpower (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,3 ≤ Z ∧
    ∀(ι : Type)[Fintype ι](s : Source ι (1/4) (9/4)),Fintype.card ι ≤ N →
    ∀(cover : OriginalEnclosure s)(w : ι→ℝ),(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀(G : Id)(J : (B : actualAllocations (tuplePools s) G)→Finset (liveIndices B.val)),
      (∀B,(∑j∈J B,w j.val) ≤ 3/5000) →
    ∀ K : ℝ,0 ≤ K → K ≤ Z^(40:ℝ) →
      MultBound s (by norm_num) cover G J K
        (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (J B))
        (clippedMultiplicity s (by norm_num) cover G J (fun _=>C*Z^δ)) := by
  obtain ⟨C,hC,hdiv⟩ := QRH.SilDensitySplit.CubeFree.Packet.Fibre.divisor_power_subpower N 48 δ (by norm_num) hδ
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  filter_upwards [RawSides.selected_width_Q N,eventually_ge_atTop (3:ℝ)] with Z hwidth hZ
  refine ⟨hZ,?_⟩
  intro ι _ s hN cover w hw hP G J hJ K hK hKcap
  apply multBound_clipped
  intro B
  have hNlive : Fintype.card (liveIndices B.val) ≤ N :=
    (Fintype.card_le_of_injective (fun j : liveIndices B.val=>j.val) Subtype.val_injective).trans hN
  have hNJ : Fintype.card (J B) ≤ N := by simpa using (Finset.card_le_univ (J B)).trans hNlive
  have hW := hwidth.2 (liveIndices B.val) (fun j=>w j.val) hNlive (fun j=>hw j.val) (J B) (hJ B)
  have hWeq : RawSides.selectionScaleQ s (by norm_num) cover G B (J B) =
      ∏j∈J B,2*Z^(w j.val) := by
    change (∏j∈J B,2*s.P j.val) = _
    simp_rw [hP]
  rw [←hWeq] at hW
  have hWcap : RawSides.selectionScaleQ s (by norm_num) cover G B (J B) ≤ Z :=
    hW.2.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hwidth.1.le (show (1/1000:ℝ) ≤ 1 by norm_num))
  have hrad := actual_radius_cap Z K _ hZ hK hKcap (zero_le_one.trans hW.1) hWcap
  refine ⟨mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (Real.rpow_nonneg (zero_le_one.trans hwidth.1.le) δ),?_⟩
  intro z hz hzn
  exact selected_mult_le (allocatedLiveSource s (by norm_num) cover G B) (J B) N hNJ
    48 δ C Z hwidth.1.le hδ.le (fun r hr hn=>hdiv Z hwidth.1.le r hr hn)
    z hz (hzn.trans hrad)

#print axioms actual_radius_cap
#print axioms actual_multBound_subpower
end
end QRH.Cycle092.ColoredSelectionAverage
