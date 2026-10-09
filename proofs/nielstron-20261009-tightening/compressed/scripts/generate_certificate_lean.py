#!/usr/bin/env python3
"""Emit explicit proof obligations from discovered rationals.
The generator is untrusted: Lean checks the identities and inequalities.
"""
from pathlib import Path
import json
from fractions import Fraction
j=json.loads(Path('audit/discovered-coefficients.json').read_text())
def rat(s):
 v=Fraction(s);return f'({v.numerator} / {v.denominator} : ℝ)'
def sumtext(terms):return ' +\n      '.join(terms)
text='''import QRH.Geometry
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Continuous rational exponent certificate. No analytic conclusion is asserted. -/
namespace QRH.Certificate
noncomputable section
open QRH

def c : ℝ := 1 / (3 * kappa0)
def D (x : ℝ) : ℝ := 3 - (1 + 2 * c) * x
def P (x : ℝ) : ℝ := (2 - 2 * c * x) * (1 - x)
def J (δ x : ℝ) : ℝ := (5 / 6 - δ) * D x + δ * P x

def F (δ y : ℝ) : ℝ :=
  -J δ (1 / 2 - y) * ((1 + δ) / 2 - theta - h / 6 -
    (1 + δ) / 2 * ly - ell / 2 + (1 / 2 - y) * δ * ell + h * (1 - δ / 2)) -
    h * (5 / 6 - δ) * δ * P (1 / 2 - y) / 2

def E (δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - theta - h / 6 - (1 + δ) / 2 * ly - ell / 2 + x * δ * ell +
    h * (1 - δ + (5 / 6 - δ) * δ * P x / (2 * J δ x) + δ / 2)

'''
text+=f'def Av : ℝ := {rat(j["Av"])}\ndef Dv : ℝ := {rat(j["Dv"])}\ndef dv : ℝ := {rat(j["dv"])}\n\n'
text+='''theorem Av_pos : 0 < Av := by norm_num [Av]
theorem Dv_margin : (5 / 1000000000000 : ℝ) < Dv := by norm_num [Dv]

'''
terms=[]
for i,row in enumerate(j['shift_coefficients'],1):
 terms.append(f'y ^ {i} * ('+' + '.join(f'{rat(v)} * (δ - 1 / 3) ^ {k}' for k,v in enumerate(row))+')')
expr=sumtext(terms)
text+=f'''theorem square_identity (δ y : ℝ) :
    F δ y = Av * (δ - dv) ^ 2 + Dv +
      {expr} := by
  norm_num [F, J, D, P, c, kappa0, theta, h, lx, ly, M, ell, b, Av, Dv, dv]
  <;> ring

theorem near_margin {{δ y : ℝ}} (hδ : (1 / 3 : ℝ) ≤ δ) (hy : 0 ≤ y) :
    (5 / 1000000000000 : ℝ) < F δ y := by
  have hu : 0 ≤ δ - 1 / 3 := sub_nonneg.mpr hδ
  have hv : 0 ≤ Av * (δ - dv) ^ 2 := mul_nonneg Av_pos.le (sq_nonneg _)
  have hrest : 0 ≤ {expr} := by positivity
  rw [square_identity]
  linarith [Dv_margin]

'''
basis2=['(1 - t)^2','(2*t*(1-t))','t^2'];basis3=['(1-v)^3','(3*v*(1-v)^2)','(3*v^2*(1-v))','v^3']
for idx,mat in enumerate(j['bernstein']):
 terms=[f'{rat(Fraction(mat[i][k])-Fraction(723,10**6))} * {basis2[i]} * {basis3[k]}' for i in range(3) for k in range(4)]
 expr=sumtext(terms)
 arg='t / 4' if idx==0 else '1 / 4 + t / 12'
 text+=f'''theorem bernstein_identity_{idx} (t v : ℝ) :
    F ({arg}) (v / 2) = (723 / 1000000 : ℝ) +
      {expr} := by
  norm_num [F, J, D, P, c, kappa0, theta, h, lx, ly, M, ell, b]
  <;> ring

theorem bernstein_margin_{idx} {{t v : ℝ}} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    (5 / 1000000000000 : ℝ) < F ({arg}) (v / 2) := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hv' : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  have hrest : 0 ≤ {expr} := by positivity
  rw [bernstein_identity_{idx}]
  linarith

'''
text+='''theorem continuous_margin {δ y : ℝ} (hδ : 0 ≤ δ)
    (hy : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    (5 / 1000000000000 : ℝ) < F δ y := by
  by_cases hd0 : δ ≤ 1 / 4
  · have hh := bernstein_margin_0 (t := 4 * δ) (v := 2 * y)
      (by linarith) (by linarith) (by linarith) (by linarith)
    convert hh using 1 <;> ring
  · by_cases hd1 : δ ≤ 1 / 3
    · have hh := bernstein_margin_1 (t := 12 * (δ - 1 / 4)) (v := 2 * y)
        (by linarith) (by linarith) (by linarith) (by linarith)
      convert hh using 1 <;> ring
    · exact near_margin (by linarith) hy

end
end QRH.Certificate
'''
Path('research/drafts/Certificate.lean').write_text(text)
print('Emitted draft, unverified Lean source:',len(text),'bytes')
