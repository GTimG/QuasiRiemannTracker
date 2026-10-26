/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section

/-- Adapted from liqsweep/A48 PR52 Bern.lean, Apache-2.0,
cbb3e1faac3f4dd711b06628a6b0052d388f12a5. -/
theorem tensor_nonneg {n m : ℕ} {fee : ℝ} {g : Fin (n+1) → Fin (m+1) → ℝ}
 {a z c t b ν : ℝ} (hm : 0 ≤ fee) (hg : ∀ i j, 0 ≤ g i j)
 (hb : b ∈ Set.Icc a z) (hν : ν ∈ Set.Icc c t) :
 0 ≤ Record12518109.Bernstein.bsum n m fee g a z c t b ν := by
 unfold Record12518109.Bernstein.bsum
 apply add_nonneg hm
 apply Finset.sum_nonneg
 intro i _
 apply Finset.sum_nonneg
 intro j _
 exact mul_nonneg (hg i j) (Record12518109.Bernstein.bterm_nonneg hb hν)

def residue (i j : ℕ) : ℤ := ((i:ℤ)-(j:ℤ))%6
def localR (i j : ℕ) : ℝ := if residue i j=0 then 0 else 1
def localL (i j : ℕ) : ℝ := if residue i j=0 ∨ residue i j=5 then 0 else (residue i j:ℝ)+1
def localO (i j : ℕ) : ℝ := if residue i j=5 then 1 else 0
def localB (i j : ℕ) : ℝ := max (3*(i:ℝ)-5*(j:ℝ)-localR i j) 0/6
def localSigma (i j : ℕ) : ℝ := ((i:ℝ)+(j:ℝ)-localR i j-2-localB i j-localB j i)/2
def localizationReserve (i j : ℕ) : ℝ := 3*min (i:ℝ) (j:ℝ)+4*localSigma i j-i-j

def orderedLow (c : Cell) (i j : ℕ) : ℝ :=
 let k := c.q/K
 let ell := c.q/c.priorL
 let B := c.priorB
 let ws : ℝ := 17/50
 let wl : ℝ := 17/25
 show ℝ from
 -(2-ws-wl)*k*i-i-j+localR i j+2+
 ws*((-2+ell*B)*localR i j+(1-ell*B)*localL i j+localO i j-ell*i)+
 wl*((-2+ell*B)*localR i j+(1-ell*B)*localL j i+localO j i-ell*j+ell*B*((j:ℝ)-i))

def etaD (ν : ℝ) : ℝ := 4*ν^2-d ν/25

def mixedLowHigh (c : Cell) (i j : ℕ) (ν : ℝ) : ℝ :=
 let k := c.q/K
 let ell := c.q/c.priorL
 let natural := -k*min (i:ℝ) (j:ℝ)-localB i j-localSigma i j
 let raw := -2*localR i j-localB i j+localL i j+localO i j-localSigma i j-
   ell*((i:ℝ)+c.priorB*(localL i j-localR i j-max ((i:ℝ)-j) 0))
 let low := (1-omega)*natural+omega*raw
 let high := (d ν-rr ν)*max ((j:ℝ)-i) 0-(d ν+rr ν)*localR i j-d ν*localB j i+
   rr ν*localL j i+d ν*localO j i-d ν*localSigma i j-etaD ν*j
 show ℝ from
 -d ν*low-high

def floorCore (i j : ℕ) (ν : ℝ) : ℝ :=
 -d ν*((i:ℝ)+j)+2*d ν-rr ν*localR i j+(d ν-rr ν)*max ((j:ℝ)-i) 0+
 rr ν*localL j i+d ν*localO j i-etaD ν*j

def naturalFloor (c : Cell) (i j : ℕ) (positiveDefect : Bool) (ν : ℝ) : ℝ :=
 -floorCore i j ν+if positiveDefect then c.q/K*d ν*min (i:ℝ) (j:ℝ)-c.q/K*d ν*((i:ℝ)+j)/3 else 0

def complementaryFloor (i j : ℕ) (ν : ℝ) : ℝ := -floorCore i j ν-d ν*localB i j

def pairedGap (c : Cell) (i j : ℕ) (l r : ℝ) : ℝ :=
 l*i+r*j-
 ((1-rho l)*max ((i:ℝ)-j) 0+(1-rho r)*max ((j:ℝ)-i) 0-i-j+2-
  (1+rho l+rho r)*localR i j+rho l*localL i j+rho r*localL j i+localO i j+localO j i)
 -gamma c*((i:ℝ)+j)

def pairedCleared (c : Cell) (i j : ℕ) (l r : ℝ) : ℝ :=
 (l*i+r*j+i+j-2-localO i j-localO j i-gamma c*((i:ℝ)+j))*d l*d r-
 (d l-rr l)*max ((i:ℝ)-j) 0*d r-(d r-rr r)*max ((j:ℝ)-i) 0*d l+
 (d l*d r+rr l*d r+rr r*d l)*localR i j-rr l*d r*localL i j-rr r*d l*localL j i

theorem paired_clearing (c : Cell) (i j : ℕ) {l r : ℝ} (hl : d l ≠ 0) (hr : d r ≠ 0) :
 (d l*d r)*pairedGap c i j l r=pairedCleared c i j l r := by
 unfold pairedGap pairedCleared rho rr
 field_simp
 <;> ring

theorem pairedGap_nonneg_of_cleared {c : Cell} {i j : ℕ} {l r : ℝ}
 (hl : 0 < d l) (hr : 0 < d r) (h : 0 ≤ pairedCleared c i j l r) :
 0 ≤ pairedGap c i j l r := by
 rw [← paired_clearing c i j (ne_of_gt hl) (ne_of_gt hr)] at h
 exact (mul_nonneg_iff_of_pos_left (mul_pos hl hr)).mp h
theorem localization_six (i j : Fin 6) :
 0 ≤ localizationReserve (i.val+1) (j.val+1) := by
 fin_cases i <;> fin_cases j <;>
 norm_num [localizationReserve, localSigma, localB, localR, localL, localO, residue]

theorem incumbent_range : 7/10 < incumbent ∧ incumbent < 3/4 := by
 norm_num [incumbent]
end
end Record12518109Admission
