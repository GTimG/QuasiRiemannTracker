/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact row arithmetic only; analytic source transfer is separate. -/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Sil.Uneven.RoundedRows

def theta : ℝ := (874828524351/1000000000000:ℝ)
def h : ℝ := (99633825209167184656216186179/125000000000000000000000000000:ℝ)
def ell : ℝ := (125514426947/750000000000:ℝ)
def y : ℝ := (173387048680501553968648558537/375000000000000000000000000000:ℝ)
def reserve : ℝ := (1/100000000:ℝ)
def frozen_kappa : ℝ := (1874143/2500000:ℝ)
def upper_padding : ℝ := (1/10000000000000000:ℝ)

def planeB : ℕ → ℝ
  | 0 => (1/1:ℝ)
  | 1 => (987047/1000000:ℝ)
  | 2 => (142100527/143610000:ℝ)
  | 3 => (9816147/10000000:ℝ)
  | 4 => (3915977/4000000:ℝ)
  | 5 => (1005451199/1000000000:ℝ)
  | 6 => (49061544613/50000000000:ℝ)
  | 7 => (97851371081/100000000000:ℝ)
  | _ => 1

def planeLambda : ℕ → ℝ
  | 0 => (5622429/1250000:ℝ)
  | 1 => (19793/5000:ℝ)
  | 2 => (19312/4787:ℝ)
  | 3 => (37961251/10000000:ℝ)
  | 4 => (372765011/100000000:ℝ)
  | 5 => (44999/10000:ℝ)
  | 6 => (1891221821/500000000:ℝ)
  | 7 => (18557733993/5000000000:ℝ)
  | _ => 1

def rowHeight : ℕ → ℝ
  | 0 => (1/200:ℝ)
  | 1 => (99446325209167184656216186179/125000000000000000000000000000:ℝ)
  | 2 => (99446325209167184656216186179/125000000000000000000000000000:ℝ)
  | 3 => (99633825209167197156216186179/125000000000000000000000000000:ℝ)
  | _ => 0

def rowCapacity : ℕ → ℝ
  | 0 => (6250/5622429:ℝ)
  | 1 => (48435121733501553968648558537/1686728700000000000000000000000:ℝ)
  | 2 => (2141778267845387159759678457981167511181/70920818287500000000000000000000000000000:ℝ)
  | 3 => (2113125386690197749567601445481167511181/70920818287500000000000000000000000000000:ℝ)
  | _ => 0

def denominator (i : ℕ) (d p : ℝ) : ℝ :=
  (5/6-d)*(3-p-4*p/planeLambda i)+d*(1-p)*(2-4*p/planeLambda i)
def numerator (i : ℕ) (d p : ℝ) : ℝ :=
  (1-d)*denominator i d p+(5/6-d)*d*(1-p)*(1-2*p*planeB i/planeLambda i)
def base (r : ℕ) (d p : ℝ) : ℝ :=
  (1+d)/2+13*h/75-y/2-ell/2+ell*d*p+
    rowHeight r*(1/4-17/50)-d*p*rowCapacity r/2
def row (r i : ℕ) (d p : ℝ) : ℝ :=
  base r d p+3*rowHeight r/4*(numerator i d p/denominator i d p)
def gap (r i : ℕ) (d p : ℝ) : ℝ :=
  (theta-reserve-base r d p)*denominator i d p-3*rowHeight r*numerator i d p/4

theorem denominator_pos {i : ℕ} (hi : i ≤ 7) {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    0 < denominator i d p := by
  have hL : (3:ℝ) ≤ planeLambda i := by
    interval_cases i <;> norm_num [planeLambda]
  have hL0 : 0 < planeLambda i := by linarith only [hL]
  have hv : 4*p/planeLambda i ≤ 2/3 := by
    apply (div_le_iff₀ hL0).mpr
    linarith only [hp.2,hL]
  have hD : 0 < 3-p-4*p/planeLambda i := by linarith only [hp.2,hv]
  have hA : 0 ≤ 2-4*p/planeLambda i := by linarith only [hv]
  have hd' : 0 < 5/6-d := by linarith only [hd.2]
  have hp' : 0 ≤ 1-p := by linarith only [hp.2]
  exact add_pos_of_pos_of_nonneg (mul_pos hd' hD)
    (mul_nonneg (mul_nonneg hd.1 hp') hA)

theorem row_bound_of_gap {r i : ℕ} {d p : ℝ}
    (hJ : 0 < denominator i d p) (hg : 0 ≤ gap r i d p) :
    row r i d p ≤ theta-reserve := by
  have hnum : 3*rowHeight r*numerator i d p/4 ≤
      (theta-reserve-base r d p)*denominator i d p := by
    unfold gap at hg
    linarith only [hg]
  have hq := (div_le_iff₀ hJ).mpr hnum
  have he : 3*rowHeight r/4*(numerator i d p/denominator i d p) =
      (3*rowHeight r*numerator i d p/4)/denominator i d p := by ring
  unfold row
  rw [he]
  linarith only [hq]

def available (i : ℕ) (d p : ℝ) : Prop :=
  i = 0 ∨
  (i = 5 ∧ (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 5 ∧ (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) ∧ (127/256:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 2 ∧ (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) ∧ (255/512:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 2 ∧ (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) ∧ (127/256:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 1 ∧ (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) ∧ (127/256:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 3 ∧ (465/1024:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) ∧ (127/256:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 4 ∧ (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 4 ∧ (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 4 ∧ (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 4 ∧ (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 6 ∧ (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) ∧ (127/256:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 7 ∧ (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 7 ∧ (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 7 ∧ (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2) ∨
  (i = 7 ∧ (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2)

end Sil.Uneven.RoundedRows
