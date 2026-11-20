/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Every actual common, signed-primary and full-primary allocation is paid. -/
import Candidate.C092.transport.FixedPhysicalPaymentAll
import Candidate.C092.transport.FixedCubeGaussPayments
import Candidate.C092.transport.FixedFourierH15Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily IdealMobiusDivisorSum
open CenteredMomentCommonProfile CenteredMomentDivisorAllocation
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open QRH.Cycle092.FixedCubeGauss
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedFourierH15Allocations_be1517346a505155_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

lemma divisor_count_one (I : Id) (hI : I≠0) : 1 ≤ (idealDivisors I).card := by
  have hmem : (1:Id)∈idealDivisors I := (mem_idealDivisors hI).mpr (one_dvd _)
  exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨1,hmem⟩)

/-- The finite count is the actual sigma of native allocation labels. -/
lemma allocationCount_divisor_bound (r : Source ι a b) (N : ℕ) (hN : Fintype.card ι ≤ N)
    (G L : Id) (hG : G≠0) (hL : L≠0) :
    (allocationCount r G L:ℝ) ≤
      ((idealDivisors G).card:ℝ)^(N+2)*((2:ℝ)^(primeSupport L).card)^(N+2)*
        ((idealDivisors (L^4)).card:ℝ)^(N+2) := by
  have hGc : (1:ℝ) ≤ (idealDivisors G).card := by exact_mod_cast divisor_count_one G hG
  have hLc : (1:ℝ) ≤ (idealDivisors (L^4)).card := by exact_mod_cast divisor_count_one (L^4) (pow_ne_zero _ hL)
  have hBc (B : commonAlloc r G) : Fintype.card (liveIndices B.val⊕Fin 2) ≤ N+2 := by
    have hh := live_slots_card_le r G B
    simpa only [Fintype.card_sum,Fintype.card_fin] using hh.trans (by simpa using Nat.add_le_add_right hN 2)
  have hs (B : commonAlloc r G) :
      (Fintype.card (Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))):ℝ) ≤
        ((2:ℝ)^(primeSupport L).card)^(N+2) := by
    have hh : (Fintype.card (Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))):ℝ) ≤
        ((2:ℝ)^(primeSupport L).card)^Fintype.card (liveIndices B.val⊕Fin 2) := by
      exact_mod_cast signedPrimaryAlloc_card r G L B
    exact hh.trans (pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (hBc B))
  have he (B : commonAlloc r G) :
      ((fullPrimaryAlloc r G B L).card:ℝ) ≤ ((idealDivisors (L^4)).card:ℝ)^(N+2) := by
    have hh : ((fullPrimaryAlloc r G B L).card:ℝ) ≤
        ((idealDivisors (L^4)).card:ℝ)^Fintype.card (liveIndices B.val⊕Fin 2) := by
      exact_mod_cast fullPrimaryAlloc_card r G L hL B
    exact hh.trans (pow_le_pow_right₀ hLc (hBc B))
  have hg : ((commonAlloc r G).card:ℝ) ≤ ((idealDivisors G).card:ℝ)^(N+2) := by
    have hh : ((commonAlloc r G).card:ℝ) ≤
        ((idealDivisors G).card:ℝ)^Fintype.card (ι⊕Fin 2) := by
      exact_mod_cast commonAlloc_card r G hG
    exact hh.trans (pow_le_pow_right₀ hGc (by simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hN 2))
  simp only [allocationCount,Nat.cast_sum,Nat.cast_mul]
  calc
    _ ≤ ∑ _B : commonAlloc r G,((2:ℝ)^(primeSupport L).card)^(N+2)*((idealDivisors (L^4)).card:ℝ)^(N+2) :=
      Finset.sum_le_sum (fun B _=>mul_le_mul (hs B) (he B) (by positivity) (by positivity))
    _ = ((commonAlloc r G).card:ℝ)*
        (((2:ℝ)^(primeSupport L).card)^(N+2)*((idealDivisors (L^4)).card:ℝ)^(N+2)) := by simp
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_right hg (show 0 ≤ (((2:ℝ)^(primeSupport L).card)^(N+2)*((idealDivisors (L^4)).card:ℝ)^(N+2)) by positivity) using 1 <;> ring

/-- A genuine uniform subpower bound on every actual allocation index. -/
theorem allocationCount_subpower (N : ℕ) (Bcap ε : ℝ) (hB : 0 ≤ Bcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] {a b : ℝ} (r : Source ι a b),
      Fintype.card ι ≤ N → ∀ (U : ℝ),1 ≤ U → ∀ (G L : Id),G≠0 → L≠0 →
      (G.absNorm:ℝ) ≤ U^Bcap → (L.absNorm:ℝ) ≤ U^Bcap →
      (allocationCount r G L:ℝ) ≤ C*U^ε := by
  let δ : ℝ := ε/(3*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨Cg,hCg,hg⟩ := CenteredMomentMask.polynomial_mask_divisor_bound δ Bcap hδ hB
  obtain ⟨Cl,hCl,hl⟩ := CenteredMomentMask.polynomial_mask_divisor_bound δ (4*Bcap) hδ (by positivity)
  obtain ⟨Cp,hCp,hp⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (δ/(1+Bcap)) (by positivity)
  refine ⟨Cg^(N+2)*Cp^(N+2)*Cl^(N+2),by positivity,?_⟩
  intro κ _ a b r hN U hU G L hG hL hNG hNL
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hNL4 : ((L^4).absNorm:ℝ) ≤ U^(4*Bcap) := by
    rw [map_pow,Nat.cast_pow,mul_comm (4:ℝ),Real.rpow_mul hU0.le,Real.rpow_ofNat]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hNL _
  have hcg := hg U hU G hG hNG
  have hcl := hl U hU (L^4) (pow_ne_zero _ hL) hNL4
  have hcp : (2:ℝ)^(primeSupport L).card ≤ Cp*U^δ := by
    apply (hp L hL).trans
    apply mul_le_mul_of_nonneg_left _ hCp.le
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hNL (by positivity : 0 ≤ δ/(1+Bcap))).trans
    rw [←Real.rpow_mul hU0.le]
    apply Real.rpow_le_rpow_of_exponent_le hU
    have hh : (0:ℝ)<1+Bcap := by linarith
    rw [show Bcap*(δ/(1+Bcap))=Bcap*δ/(1+Bcap) by ring]
    exact (div_le_iff₀ hh).mpr (by nlinarith [hδ.le])
  have hh := allocationCount_divisor_bound r N hN G L hG hL
  apply hh.trans
  calc
    _ ≤ (Cg*U^δ)^(N+2)*(Cp*U^δ)^(N+2)*(Cl*U^δ)^(N+2) := by gcongr
    _ = _ := by
      simp only [mul_pow,←Real.rpow_mul_natCast hU0.le]
      have hid : δ*(N+2:ℕ)+δ*(N+2:ℕ)+δ*(N+2:ℕ)=ε := by dsimp [δ];field_simp;ring
      calc
        _ = Cg^(N+2)*Cp^(N+2)*Cl^(N+2)*
            (U^(δ*(N+2:ℕ))*U^(δ*(N+2:ℕ))*U^(δ*(N+2:ℕ))) := by ring
        _ = _ := by rw [←Real.rpow_add hU0,←Real.rpow_add hU0,hid]

#print axioms allocationCount_subpower
end QRH.Cycle092.FixedFourierH15
