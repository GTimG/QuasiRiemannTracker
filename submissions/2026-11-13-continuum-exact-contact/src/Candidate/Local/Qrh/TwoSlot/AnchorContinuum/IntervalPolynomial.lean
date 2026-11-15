/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Interval-enclosed real coefficients over ArviFoxy's Q1/Q2 polynomial layout
(Apache-2.0). The existing rational Bernstein checker remains unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.RationalInterval
import Submissions.arvi_selected_leaf.Tuning.Poly2

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.IntervalPolynomial
noncomputable section
open RationalInterval QRH.ArviReturnTuning

structure Coeff where
  box : Box
  value : ℝ
  sound : box.Contains value

def Coeff.rat (q : ℚ) : Coeff := ⟨point q,q,point_sound q⟩
def Coeff.add (a b : Coeff) : Coeff := ⟨RationalInterval.add a.box b.box,a.value+b.value,
  add_sound a.sound b.sound⟩
def Coeff.neg (a : Coeff) : Coeff := ⟨RationalInterval.neg a.box,-a.value,neg_sound a.sound⟩
def Coeff.sub (a b : Coeff) : Coeff := a.add b.neg
def Coeff.mul (a b : Coeff) : Coeff := ⟨RationalInterval.mul a.box b.box,a.value*b.value,
  mul_sound a.sound b.sound⟩
def Coeff.div (a b : Coeff) (hb : 0 < b.box.lo) : Coeff :=
  ⟨RationalInterval.div a.box b.box,a.value/b.value,div_sound a.sound b.sound hb⟩

abbrev P1 := List Coeff
namespace P1
def add : P1 → P1 → P1
  | [],q => q
  | a::p,[] => a::p
  | a::p,b::q => a.add b :: add p q
def smul (c : Coeff) (p : P1) : P1 := p.map c.mul
def mul : P1 → P1 → P1
  | [],_ => []
  | a::p,q => add (smul a q) (Coeff.rat 0 :: mul p q)
def ev : P1 → ℝ → ℝ
  | [],_ => 0
  | a::p,x => a.value+x*ev p x
def lower (p : P1) : Q1 := p.map (fun c => c.box.lo)

@[simp] theorem ev_nil (x : ℝ) : ev [] x = 0 := rfl
@[simp] theorem ev_cons (a : Coeff) (p : P1) (x : ℝ) : ev (a::p) x = a.value+x*ev p x := rfl
theorem ev_add (p q : P1) (x : ℝ) : ev (add p q) x = ev p x+ev q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp only [add,ev_cons,ih,Coeff.add]; ring
theorem ev_smul (c : Coeff) (p : P1) (x : ℝ) : ev (smul c p) x = c.value*ev p x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih => simp only [smul,List.map_cons,ev_cons,Coeff.mul] at ih ⊢; rw [ih]; ring
theorem ev_mul (p q : P1) (x : ℝ) : ev (mul p q) x = ev p x*ev q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp only [mul,ev_add,ev_smul,ev_cons,ih,Coeff.rat]; norm_num; ring
theorem lower_le (p : P1) {x : ℝ} (hx : 0 ≤ x) : Q1.ev (lower p) x ≤ ev p x := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih =>
    have hm := mul_le_mul_of_nonneg_left ih hx
    simpa only [lower,List.map_cons,Q1.ev_cons,ev_cons] using add_le_add a.sound.1 hm
end P1

abbrev P2 := List P1
namespace P2
def add : P2 → P2 → P2
  | [],q => q
  | a::p,[] => a::p
  | a::p,b::q => P1.add a b :: add p q
def smul (c : Coeff) (p : P2) : P2 := p.map (P1.smul c)
def mulP1 (a : P1) (p : P2) : P2 := p.map (P1.mul a)
def mul : P2 → P2 → P2
  | [],_ => []
  | a::p,q => add (mulP1 a q) ([] :: mul p q)
def sub (p q : P2) : P2 := add p (smul (Coeff.rat (-1)) q)
def C (c : Coeff) : P2 := [[c]]
def X : P2 := [[],[Coeff.rat 1]]
def Y : P2 := [[Coeff.rat 0,Coeff.rat 1]]
def ev : P2 → ℝ → ℝ → ℝ
  | [],_,_ => 0
  | a::p,x,y => P1.ev a y+x*ev p x y
def lower (p : P2) : Q2 := p.map P1.lower
def lift (p : Q2) : P2 := p.map (fun row => row.map Coeff.rat)

@[simp] theorem ev_nil (x y : ℝ) : ev [] x y = 0 := rfl
@[simp] theorem ev_cons (a : P1) (p : P2) (x y : ℝ) : ev (a::p) x y = P1.ev a y+x*ev p x y := rfl
theorem ev_add (p q : P2) (x y : ℝ) : ev (add p q) x y = ev p x y+ev q x y := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp only [add,ev_cons,P1.ev_add,ih]; ring
theorem ev_smul (c : Coeff) (p : P2) (x y : ℝ) : ev (smul c p) x y = c.value*ev p x y := by
  induction p with
  | nil => simp [smul]
  | cons a p ih => simp only [smul,List.map_cons,ev_cons,P1.ev_smul] at ih ⊢; rw [ih]; ring
theorem ev_mulP1 (a : P1) (p : P2) (x y : ℝ) : ev (mulP1 a p) x y = P1.ev a y*ev p x y := by
  induction p with
  | nil => simp [mulP1]
  | cons b p ih => simp only [mulP1,List.map_cons,ev_cons,P1.ev_mul] at ih ⊢; rw [ih]; ring
theorem ev_mul (p q : P2) (x y : ℝ) : ev (mul p q) x y = ev p x y*ev q x y := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp only [mul,ev_add,ev_mulP1,ev_cons,P1.ev_nil,ih]; ring
theorem ev_sub (p q : P2) (x y : ℝ) : ev (sub p q) x y = ev p x y-ev q x y := by
  simp only [sub,ev_add,ev_smul,Coeff.rat]
  norm_num
  ring
@[simp] theorem ev_C (c : Coeff) (x y : ℝ) : ev (C c) x y = c.value := by simp [C,ev,P1.ev]
@[simp] theorem ev_X (x y : ℝ) : ev X x y = x := by norm_num [X,ev,P1.ev,Coeff.rat]
@[simp] theorem ev_Y (x y : ℝ) : ev Y x y = y := by norm_num [Y,ev,P1.ev,Coeff.rat]

theorem ev_lift (p : Q2) (x y : ℝ) : ev (lift p) x y = Q2.ev p x y := by
  have hrow (q : Q1) : P1.ev (q.map Coeff.rat) y = Q1.ev q y := by
    induction q with
    | nil => rfl
    | cons a q ih => simp only [List.map_cons,P1.ev_cons,Q1.ev_cons,Coeff.rat,ih]
  induction p with
  | nil => rfl
  | cons a p ih => simpa only [lift,List.map_cons,ev_cons,Q2.ev_cons,hrow] using congrArg (fun z => Q1.ev a y+x*z) ih

theorem lower_le (p : P2) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Q2.ev (lower p) x y ≤ ev p x y := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih =>
    have hm := mul_le_mul_of_nonneg_left ih hx
    simpa only [lower,List.map_cons,Q2.ev_cons,ev_cons] using add_le_add (P1.lower_le a hy) hm

/-- The rational checker bounds the actual polynomial only after the signed
coefficient containment and the nonnegative monomial coordinates are paid. -/
theorem positive_of_bernCheck (p : P2) (a b c d : ℚ)
    (hcheck : QRH.ArviReturnTuning.bernCheck (lower p) a b c d = true)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : (a:ℝ) ≤ x) (hb : x ≤ (b:ℝ)) (hc : (c:ℝ) ≤ y) (hd : y ≤ (d:ℝ)) :
    0 < ev p x y :=
  (QRH.ArviReturnTuning.bernCheck_sound _ _ _ _ _ hcheck ha hb hc hd).trans_le (lower_le p hx hy)
end P2

end
end Qrh.TwoSlot.AnchorContinuum.IntervalPolynomial
