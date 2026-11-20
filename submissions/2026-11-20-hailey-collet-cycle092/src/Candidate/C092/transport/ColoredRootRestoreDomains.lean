/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact zero extension on the common signed ordinary domain, before any norm. -/
import Candidate.C092.transport.ColoredRootRestoreSigned
set_option autoImplicit false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentSourceMass
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP
open KernelRowExpansion KernelRowProfiles KernelRowPools KernelMarkedRows KernelAssignmentReindex
open QRH.Cycle092.RegularColoredForward
local notation "Id"=>Ideal HeckeFamily.O

theorem supported_rectangle_mono (S:Finset PrimeIdeal) {b X₁ X₂ M₁ M₂:ℝ}
    (hb:0≤b) (h₁:X₁≤M₁) (h₂:X₂≤M₂) :
    supportedRectangle S b X₁ X₂ ⊆ supportedRectangle S b M₁ M₂ := by
  intro n hn
  obtain ⟨hn,hs⟩:=Finset.mem_filter.mp hn
  obtain ⟨hi,hj⟩:=Finset.mem_product.mp hn
  obtain ⟨hi0,hi⟩:=(mem_idealBall _ _).mp hi
  obtain ⟨hj0,hj⟩:=(mem_idealBall _ _).mp hj
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr
    ⟨(mem_idealBall _ _).mpr ⟨hi0,hi.trans (mul_le_mul_of_nonneg_left h₁ hb)⟩,
      (mem_idealBall _ _).mpr ⟨hj0,hj.trans (mul_le_mul_of_nonneg_left h₂ hb)⟩⟩,hs⟩

/-- A larger common rectangle changes neither ordinary arm. Terms outside
its own physical profile support are exactly zero. -/
theorem row_common_domain (χ:Character) (ω₁ ω₂:Id→*₀ℂ) (S:Finset PrimeIdeal)
    (r:IdealPair→ℂ) (W₁ W₂:ℝ→ℂ) {b X₁ X₂ M₁ M₂:ℝ}
    (hb:0≤b) (hX₁:0<X₁) (hX₂:0<X₂) (h₁:X₁≤M₁) (h₂:X₂≤M₂)
    (hs₁:Function.support W₁⊆Set.Iic b) (hs₂:Function.support W₂⊆Set.Iic b) :
    row χ ω₁ ω₂ (supportedRectangle S b M₁ M₂) r W₁ W₂ X₁ X₂ =
      row χ ω₁ ω₂ (supportedRectangle S b X₁ X₂) r W₁ W₂ X₁ X₂ := by
  unfold row normalizedRow
  congr 1
  symm
  apply Finset.sum_subset (supported_rectangle_mono S hb h₁ h₂)
  intro n hn hnsmall
  have hnSup:pairSupport n.1 n.2⊆primeValues S := (Finset.mem_filter.mp hn).2
  have hlarge:=Finset.mem_product.mp (Finset.mem_filter.mp hn).1
  have hn₁: n.1≠0 := ((mem_idealBall _ _).mp hlarge.1).1
  have hn₂: n.2≠0 := ((mem_idealBall _ _).mp hlarge.2).1
  have hnot: ¬((n.1.absNorm:ℝ)≤b*X₁ ∧ (n.2.absNorm:ℝ)≤b*X₂) := by
    intro hh
    apply hnsmall
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_idealBall _ _).mpr ⟨hn₁,hh.1⟩,(mem_idealBall _ _).mpr ⟨hn₂,hh.2⟩⟩,hnSup⟩
  have hzero:pairProfile W₁ W₂ X₁ X₂ n=0 := by
    by_cases hi:(n.1.absNorm:ℝ)≤b*X₁
    · have hj:¬(n.2.absNorm:ℝ)≤b*X₂ := fun hj=>hnot ⟨hi,hj⟩
      have hw:W₂ ((n.2.absNorm:ℝ)/X₂)=0 := by
        apply Function.notMem_support.mp
        intro hmem
        exact hj ((div_le_iff₀ hX₂).mp (hs₂ hmem))
      simp only [pairProfile,hw,mul_zero]
    · have hw:W₁ ((n.1.absNorm:ℝ)/X₁)=0 := by
        apply Function.notMem_support.mp
        intro hmem
        exact hi ((div_le_iff₀ hX₁).mp (hs₁ hmem))
      simp only [pairProfile,hw,zero_mul]
  rw [hzero,mul_zero]

/-- Native divisor restoration supplies one smaller common rectangle.
Each arm then returns to its own exact supported rectangle. -/
theorem residual_row_domain (χ:Character) (ω₁ ω₂:Id→*₀ℂ) (S:Finset PrimeIdeal)
    (r:IdealPair→ℂ) (W₁ W₂:ℝ→ℂ) {b X₁ X₂ M₁ M₂:ℝ} {d:IdealPair}
    (hb:0≤b) (hX₁:0<X₁) (hX₂:0<X₂) (h₁:X₁≤M₁) (h₂:X₂≤M₂)
    (hs₁:Function.support W₁⊆Set.Iic b) (hs₂:Function.support W₂⊆Set.Iic b)
    (hd:d∈divisorPool (supportedRectangle S b M₁ M₂)) :
    row χ ω₁ ω₂ (residualPool (supportedRectangle S b M₁ M₂) d) r W₁ W₂
      (X₁/d.1.absNorm) (X₂/d.2.absNorm) =
    row χ ω₁ ω₂ (supportedRectangle S b (X₁/d.1.absNorm) (X₂/d.2.absNorm)) r W₁ W₂
      (X₁/d.1.absNorm) (X₂/d.2.absNorm) := by
  rw [residual_rectangle hd]
  have hd₁:0<(d.1.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le (divisor_supported hd).1)
  have hd₂:0<(d.2.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le (divisor_supported hd).2.1)
  exact row_common_domain χ ω₁ ω₂ S r W₁ W₂ hb (div_pos hX₁ hd₁) (div_pos hX₂ hd₂)
    (div_le_div_of_nonneg_right h₁ hd₁.le) (div_le_div_of_nonneg_right h₂ hd₂.le) hs₁ hs₂

#print axioms row_common_domain
#print axioms residual_row_domain
end
end QRH.Cycle092.ColoredRootRestore
