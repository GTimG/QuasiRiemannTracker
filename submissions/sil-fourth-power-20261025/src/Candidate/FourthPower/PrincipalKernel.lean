/- Copyright (c) 2026 Sil. Apache-2.0.
For fixed marked primes and common punctures, the forward kernel is B at
avoided primes and H5 elsewhere. Its mass is finite for every sigma>1/5.
This is a forward identity; no inverse-series convergence is required.
-/
import Candidate.FourthPower.KernelPunctureRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.PrincipalKernel
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelRestrictedState KernelRowExpansion
open KernelSelectedMass KernelSelectedLocal KernelRowProfiles KernelRowPools
open OAI.IdealMobiusDivisorSum (idealDivisors)
local notation "Id" => Ideal ActualEisensteinCubic.O

def localSeries (avoid : Bool) : LocalSeries :=
  if avoid then LocalKernels.base formalX formalY else kernelSeries

theorem local_identity (avoid : Bool) :
    localSeries avoid*ordinarySeries = if avoid then 1 else truncatedSeries := by
  cases avoid
  · exact forward_divisor_identity
  · exact ordinary_geometric_identity

theorem divisor_identity (S : Finset PrimeIdeal) (live : S → Bool)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) (hs : pairSupport I J ⊆ primeValues S) :
    (∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      kernelOn S (fun P => localSeries (live P)) d.1 d.2) =
        if Restricted S live I J then 1 else 0 := by
  have h := divisor_convolution S (fun P => localSeries (live P))
    (fun _ => ordinarySeries) hI hJ hs
  simp_rw [ordinary_kernel_one,mul_one,local_identity] at h
  exact h.trans (restricted_kernel S live hI hJ hs)

theorem base_local (P : PrimeIdeal) (σ : ℝ) (hσ : 0 ≤ σ) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localWeight (LocalKernels.base formalX formalY) σ σ P ij) ≤ 4 := by
  let z := (Ideal.absNorm P.val : ℝ)^(-σ)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (ideal_norm_one_le P.property.ne_zero) (neg_nonpos.mpr hσ)
  have hm := KernelPunctureMass.base_mass hz hz1
  have hf := ((KernelSeriesMass.pairExponent.summable_iff).mpr hm.1).sum_le_tsum T
    (fun ij _ => KernelSeriesMass.weight_nonneg _ hz (KernelSeriesMass.pairExponent ij))
  rw [KernelSeriesMass.pairExponent.tsum_eq] at hf
  convert hf.trans hm.2 using 1
  apply Finset.sum_congr rfl
  intro ij _
  simp only [localWeight,KernelSeriesMass.weight,KernelSeriesMass.pairExponent,
    Equiv.coe_fn_mk,degree_exponent,pow_add,mul_assoc,z]

/-- Constants are chosen before the support, its prime pool and the cutoffs.
All marked primes may be included in F; their number is not assumed fixed here. -/
theorem ideal_mass (σ B ε : ℝ) (hσ : 1/5 < σ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B →
      ∀ (S : Finset PrimeIdeal) (live : S → Bool),
      (∀ P ∈ S, Supported P.val) → (∀ P : S, live P=true → P.val.val ∣ F) →
      ∀ D : Finset (Id × Id), (∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ d ∈ D, idealWeight S (fun P => localSeries (live P)) σ σ d) ≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩ := KernelFixedSupportMass.polynomial_support_mass 0 3 B ε
    (by norm_num) (by norm_num) hB hε
  let E := Real.exp (11*SieveDescent.rootMass (5*σ))
  have hE : 0 < E := Real.exp_pos _
  refine ⟨E*C,mul_pos hE hC,?_⟩
  intro Z hZ F hF hcut S live hS hlive D hd hdS
  have hσ0 : 0 ≤ σ := by linarith
  let H : Finset PrimeIdeal := S.filter (fun P => ∃ h : P ∈ S, live ⟨P,h⟩=true)
  have hH (P : S) : P.val ∈ H ↔ live P=true := by simp [H]
  have hlocal (P : S) :
      (∑ ij ∈ D.image (fun d => encodePair S d P), localWeight (localSeries (live P)) σ σ P.val ij) ≤
        (1+11*(Ideal.absNorm P.val.val : ℝ)^(-(5*σ)))*(if live P then 4 else 1) := by
    have ho : 1 ≤ 1+11*(Ideal.absNorm P.val.val : ℝ)^(-(5*σ)) := by
      have hn : 0 ≤ 11*(Ideal.absNorm P.val.val : ℝ)^(-(5*σ)) := by positivity
      linarith
    cases hh : live P
    · simpa only [localSeries,hh,Bool.false_eq_true,ite_false,mul_one] using
        ordinary_local P.val σ σ σ hσ0 le_rfl le_rfl _
    · simp only [localSeries,hh,ite_true]
      exact (base_local P.val σ hσ0 _).trans (by nlinarith)
  have hp : (∏ P : S, if live P then (4 : ℝ) else 1) =
      ∏ P ∈ primeValues H, (1+3*(Ideal.absNorm P : ℝ)^(-(0 : ℝ))) := by
    have hi (P : S) : (if live P then (4 : ℝ) else 1) = if P.val ∈ H then 4 else 1 := by
      simp only [hH]
    simp_rw [hi]
    rw [Finset.prod_coe_sort S (fun P : PrimeIdeal => if P ∈ H then (4 : ℝ) else 1),
      ← Finset.prod_filter]
    have he : S.filter (fun P => P ∈ H)=H := by ext P; simp [H]
    rw [he]
    unfold primeValues
    rw [Finset.prod_image (by intro P _ Q _ hh; exact Subtype.val_injective hh)]
    norm_num
  have hfixed : (∏ P : S, if live P then (4 : ℝ) else 1) ≤ C*Z^ε := by
    rw [hp]
    apply hbound Z hZ F hF hcut
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hQS,hQl⟩ := Finset.mem_filter.mp hQ
    obtain ⟨hQS',hh⟩ := hQl
    exact ⟨Q.property,hlive ⟨Q,hQS'⟩ hh⟩
  have hord : (∏ P : S, (1+11*(Ideal.absNorm P.val.val : ℝ)^(-(5*σ)))) ≤ E := by
    have hh := KernelForwardMass.finite_euler_mass (5*σ) 11 (by linarith) (by norm_num)
      (primeValues S) (by
        intro P hP
        obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
        exact hS Q hQ)
    unfold primeValues at hh
    rw [Finset.prod_image (by intro P _ Q _ h; exact Subtype.val_injective h)] at hh
    rw [Finset.prod_coe_sort S
      (fun P : PrimeIdeal => (1+11*(Ideal.absNorm P.val : ℝ)^(-(5*σ))))]
    exact hh
  calc
    _ ≤ ∏ P : S, ∑ ij ∈ D.image (fun d => encodePair S d P),
        localWeight (localSeries (live P)) σ σ P.val ij := finite_ideal_product S _ σ σ D hd hdS
    _ ≤ ∏ P : S, (1+11*(Ideal.absNorm P.val.val : ℝ)^(-(5*σ)))*(if live P then 4 else 1) :=
      Finset.prod_le_prod₀ (fun P _ => Finset.sum_nonneg
        (fun ij _ => localWeight_nonneg _ _ _ _ _)) (fun P _ => hlocal P)
    _ = (∏ P : S, (1+11*(Ideal.absNorm P.val.val : ℝ)^(-(5*σ))))*
        (∏ P : S, if live P then 4 else 1) := Finset.prod_mul_distrib
    _ ≤ E*(C*Z^ε) := mul_le_mul hord hfixed
      (Finset.prod_nonneg (fun P _ => by split_ifs <;> norm_num)) hE.le
    _ = _ := by ring

end
end Candidate.FourthPower.PrincipalKernel
