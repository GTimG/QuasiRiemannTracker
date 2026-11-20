/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Strictly positive ordinary-escape errors, with the frequency exponent late. -/
import Candidate.C092.transport.StrongPairOrdinaryPrice

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open QRH.Cycle092.SourceFurtherWitness

/-- These errors precede the finite cap bank, slot family, source degree
and actual rows. Each analytic source error is freely small and positive. -/
theorem ordinary_early_errors {M : ℝ} (hM : 0 ≤ M) :
    ∃ conductor capGap ε εsource : ℝ,
      0 < conductor ∧ 0 < capGap ∧ 0 < ε ∧ ε ≤ 1/7500 ∧
      0 < εsource ∧ εsource ≤ 1 ∧
      3*conductor ≤ (rho:ℝ)/128 ∧
      (responseUpper:ℝ)*(M*((3/4:ℝ)*capGap)+M*capGap+capGap) ≤ (rho:ℝ)/128 ∧
      (15/4:ℝ)*M*ε ≤ (rho:ℝ)/128 ∧ M*εsource ≤ (rho:ℝ)/128 := by
  have hr : (0:ℝ) < (rho:ℝ) := by norm_num [rho]
  have hE : (0:ℝ) < (responseUpper:ℝ) := by norm_num [responseUpper]
  let conductor : ℝ := (rho:ℝ)/384
  let capGap : ℝ := (rho:ℝ)/(512*((responseUpper:ℝ)+1)*(M+1))
  let ε : ℝ := min (1/7500) ((rho:ℝ)/(512*(M+1)))
  let εsource : ℝ := min 1 ((rho:ℝ)/(128*(M+1)))
  have hc : 0 < conductor := by dsimp [conductor]; positivity
  have hg : 0 < capGap := by dsimp [capGap]; positivity
  have he : 0 < ε := lt_min (by norm_num) (by positivity)
  have hes : 0 < εsource := lt_min (by norm_num) (by positivity)
  have hge : capGap*(512*((responseUpper:ℝ)+1)*(M+1))=(rho:ℝ) := by
    dsimp [capGap]
    field_simp
  have hee : ε*(512*(M+1)) ≤ (rho:ℝ) := by
    have h := min_le_right (1/7500:ℝ) ((rho:ℝ)/(512*(M+1)))
    exact (le_div_iff₀ (by positivity)).1 h
  have hse : εsource*(128*(M+1)) ≤ (rho:ℝ) := by
    exact (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  refine ⟨conductor,capGap,ε,εsource,hc,hg,he,min_le_left _ _,hes,min_le_left _ _,?_,?_,?_,?_⟩
  · dsimp [conductor]; ring_nf; rfl
  · have hh : (responseUpper:ℝ)*capGap*(M+1) ≤ (rho:ℝ)/512 := by
      nlinarith [mul_nonneg hg.le (show 0 ≤ M+1 by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ (responseUpper:ℝ)*capGap by positivity) hM]
  · nlinarith
  · nlinarith

/-- Slot buffers and polynomial-height losses are chosen after their true
finite count and degree. An arbitrary positive detector height limit is kept. -/
theorem ordinary_late_errors (K degree : ℕ) {τlimit : ℝ} (hlimit : 0 < τlimit) :
    ∃ buffer τ : ℝ,0 < buffer ∧ 0 < τ ∧ τ < τlimit ∧
      buffer*(K:ℝ) ≤ (rho:ℝ)/128 ∧ τ*(degree:ℝ) ≤ (rho:ℝ)/128 := by
  have hr : (0:ℝ) < (rho:ℝ) := by norm_num [rho]
  let buffer : ℝ := (rho:ℝ)/(128*((K:ℝ)+1))
  let τ : ℝ := min (τlimit/2) ((rho:ℝ)/(128*((degree:ℝ)+1)))
  have hb : 0 < buffer := by dsimp [buffer]; positivity
  have ht : 0 < τ := lt_min (by positivity) (by positivity)
  have hbe : buffer*(128*((K:ℝ)+1))=(rho:ℝ) := by dsimp [buffer]; field_simp
  have hte : τ*(128*((degree:ℝ)+1)) ≤ (rho:ℝ) :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  exact ⟨buffer,τ,hb,ht,(min_le_left _ _).trans_lt (by linarith),by nlinarith,by nlinarith⟩

/-- The positive choices above leave ample room for the genuine P4's third
witness error, the source error, whole-slot rounding and both height factors. -/
theorem ordinary_fee_bound {M conductor capGap ε εsource buffer τ d e B mbar dec rounding collar : ℝ}
    {K degree k : ℕ}
    (hM : 0 ≤ M) (hd0 : 0 ≤ d) (hd : d ≤ M)
    (he : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hg : 0 ≤ capGap) (hgap0 : 0 ≤ B-mbar) (hgap : B-mbar ≤ capGap)
    (hdec0 : 0 ≤ dec) (hdec : dec ≤ capGap) (hr0 : 0 ≤ rounding) (hr : rounding ≤ capGap)
    (hε : 0 ≤ ε) (hs : 0 ≤ εsource) (hb : 0 ≤ buffer) (ht : 0 ≤ τ) (hk : k ≤ K)
    (hcollar : collar ≤ 3*conductor) (hc : 3*conductor ≤ (rho:ℝ)/128)
    (hcap : (responseUpper:ℝ)*(M*((3/4:ℝ)*capGap)+M*capGap+capGap) ≤ (rho:ℝ)/128)
    (hwit : (15/4:ℝ)*M*ε ≤ (rho:ℝ)/128) (hsource : M*εsource ≤ (rho:ℝ)/128)
    (hbuffer : buffer*(K:ℝ) ≤ (rho:ℝ)/128) (hheight : τ*(degree:ℝ) ≤ (rho:ℝ)/128) :
    collar+(15/4:ℝ)*d*ε+e*(d*((3/4:ℝ)*(B-mbar))+d*dec+rounding)+
      (d*εsource+buffer*(k:ℝ)+τ*(degree:ℝ)) ≤ (3/4:ℝ)*(rho:ℝ) := by
  have hE : (0:ℝ) ≤ (responseUpper:ℝ) := by norm_num [responseUpper]
  have hcap' : e*(d*((3/4:ℝ)*(B-mbar))+d*dec+rounding) ≤
      (responseUpper:ℝ)*(M*((3/4:ℝ)*capGap)+M*capGap+capGap) := by gcongr
  have hwit' : (15/4:ℝ)*d*ε ≤ (15/4:ℝ)*M*ε := by gcongr
  have hsource' : d*εsource ≤ M*εsource := by gcongr
  have hb' : buffer*(k:ℝ) ≤ buffer*(K:ℝ) := by gcongr
  have hrho : (0:ℝ) ≤ (rho:ℝ) := by norm_num [rho]
  linarith

#print axioms ordinary_early_errors
#print axioms ordinary_late_errors
#print axioms ordinary_fee_bound
end
end QRH.Cycle092.StrongPair
