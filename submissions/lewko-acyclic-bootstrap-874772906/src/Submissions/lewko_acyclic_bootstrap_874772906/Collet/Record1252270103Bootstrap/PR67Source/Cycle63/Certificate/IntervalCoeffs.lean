import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Bernstein
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Interval
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Coefficient arithmetic whose positivity test treats the innermost variables by interval
arithmetic. For parameters confined to very short intervals, a Bernstein expansion in them only
multiplies the number of coefficients. Instead, every coefficient polynomial in those parameters is
replaced by the midpoint of its exact rational interval enclosure (Horner's rule), the deviation
bound is subtracted, and the resulting polynomial in the outer variables gets the Bernstein test.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Certificate

open QInterval

/-- An enclosure of a polynomial `c₀ + x₀ (c₁ + x₀ (…))` with `x₀ ∈ X`, by Horner's rule, from
enclosures of its coefficients; `none` when a coefficient has none. -/
def hornerEnclose {R : Type} (encl : R → Option QInterval) (X : QInterval) :
    List R → Option QInterval
  | [] => some (point 0)
  | a :: p =>
    match encl a, hornerEnclose encl X p with
    | some A, some S => some (A.add (X.mul S))
    | _, _ => none

theorem hornerEnclose_sound {R : Type} (C : Coeffs R) (encl : R → Option QInterval)
    (X : QInterval) (x : ℕ → ℝ) (hX : X.Mem (x 0))
    (hencl : ∀ a A, encl a = some A → A.Mem (C.eval a (tailPt x))) :
    ∀ (p : List R) (I : QInterval), hornerEnclose encl X p = some I → I.Mem (peval C p x)
  | [], I, h => by
    simp only [hornerEnclose, Option.some.injEq] at h
    subst h
    simpa [peval] using mem_point (0 : ℚ)
  | a :: p, I, h => by
    simp only [hornerEnclose] at h
    cases ha : encl a with
    | none => simp [ha] at h
    | some A =>
      cases hp : hornerEnclose encl X p with
      | none => simp [ha, hp] at h
      | some S =>
        simp only [ha, hp, Option.some.injEq] at h
        subst h
        rw [peval_cons]
        exact mem_add (hencl a A ha) (mem_mul hX (hornerEnclose_sound C encl X x hX hencl p S hp))

/-- An enclosure of a polynomial in `k` variables over a box, by Horner's rule in exact rational
interval arithmetic; `none` when the box has no interval for a variable. -/
def polyEnclose : (k : ℕ) → PolyN k → List (ℚ × ℚ) → Option QInterval
  | 0, c, _ => some (point c)
  | _ + 1, _, [] => none
  | k + 1, p, (lo, hi) :: rest => hornerEnclose (fun a => polyEnclose k a rest) ⟨lo, hi⟩ p

theorem polyEnclose_sound : ∀ (k : ℕ) (p : PolyN k) (box : List (ℚ × ℚ)) (I : QInterval),
    polyEnclose k p box = some I → ∀ x, InBox box x → I.Mem ((coeffsN k).eval p x)
  | 0, c, _, I, h, _, _ => by
    simp only [polyEnclose, Option.some.injEq] at h
    subst h
    exact mem_point c
  | _ + 1, _, [], _, h, _, _ => by simp [polyEnclose] at h
  | k + 1, p, (lo, hi) :: rest, I, h, x, hx => by
    simp only [polyEnclose] at h
    exact hornerEnclose_sound (coeffsN k) _ ⟨lo, hi⟩ x ⟨hx.1, hx.2.1⟩
      (fun a A ha => polyEnclose_sound k a rest A ha (tailPt x) hx.2.2) p I h

/-- The largest absolute value on an interval. -/
def absMax (lo hi : ℚ) : ℚ := max |lo| |hi|

theorem abs_le_absMax {lo hi : ℚ} {t : ℝ} (h : (lo : ℝ) ≤ t ∧ t ≤ hi) : |t| ≤ absMax lo hi := by
  unfold absMax
  push_cast
  rw [abs_le]
  constructor
  · have := neg_abs_le (lo : ℝ)
    have := le_max_left |(lo : ℝ)| |(hi : ℝ)|
    linarith [h.1]
  · have := le_abs_self (hi : ℝ)
    have := le_max_right |(lo : ℝ)| |(hi : ℝ)|
    linarith [h.2]

theorem InBox.append_left : ∀ {a b : List (ℚ × ℚ)} {x : ℕ → ℝ}, InBox (a ++ b) x → InBox a x
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1, h.2.1, InBox.append_left h.2.2⟩

/-- A coefficient list reduced coefficient by coefficient, with the deviations combined by
Horner's rule for `|x₀| ≤ M`. -/
def reduceList {R S : Type} (red : R → Option (S × ℚ)) (M : ℚ) : List R → Option (List S × ℚ)
  | [] => some ([], 0)
  | a :: p =>
    match red a, reduceList red M p with
    | some (a', K), some (p', L) => some (a' :: p', K + M * L)
    | _, _ => none

theorem reduceList_sound {R S : Type} (C : Coeffs R) (D : Coeffs S) (red : R → Option (S × ℚ))
    (M : ℚ) (x : ℕ → ℝ) (hM : |x 0| ≤ M)
    (hred : ∀ a a' K, red a = some (a', K) → |C.eval a (tailPt x) - D.eval a' (tailPt x)| ≤ K) :
    ∀ (p : List R) (p' : List S) (L : ℚ), reduceList red M p = some (p', L) →
      |peval C p x - peval D p' x| ≤ L
  | [], p', L, h => by
    simp only [reduceList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [peval]
  | a :: p, p', L, h => by
    simp only [reduceList] at h
    cases ha : red a with
    | none => simp [ha] at h
    | some A =>
      obtain ⟨a', K⟩ := A
      cases hp : reduceList red M p with
      | none => simp [ha, hp] at h
      | some B =>
        obtain ⟨q', L'⟩ := B
        simp only [ha, hp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := hred a a' K ha
        have h2 := reduceList_sound C D red M x hM hred p q' L' hp
        rw [peval_cons, peval_cons]
        have hx0 : 0 ≤ |x 0| := abs_nonneg _
        have hprod : |x 0 * (peval C p x - peval D q' x)| ≤ M * L' := by
          rw [abs_mul]
          exact mul_le_mul hM h2 (abs_nonneg _) (hx0.trans hM)
        calc |C.eval a (tailPt x) + x 0 * peval C p x - (D.eval a' (tailPt x) + x 0 * peval D q' x)|
            = |(C.eval a (tailPt x) - D.eval a' (tailPt x)) + x 0 * (peval C p x - peval D q' x)| := by
              ring_nf
          _ ≤ |C.eval a (tailPt x) - D.eval a' (tailPt x)| + |x 0 * (peval C p x - peval D q' x)| :=
              abs_add_le _ _
          _ ≤ K + M * L' := add_le_add h1 hprod
          _ = ((K + M * L' : ℚ) : ℝ) := by push_cast; ring

/-- For a polynomial in `j + m` variables whose last `j` lie in the box `inner`, the polynomial in
the first `m` whose coefficients are the midpoints of the interval enclosures of the coefficient
polynomials in the last `j`, and a bound of the deviation from it over the box `outer ++ inner`;
`none` when an enclosure fails or `outer` does not have `m` intervals. -/
def reduceInner (j : ℕ) (inner : List (ℚ × ℚ)) : (m : ℕ) → PolyN (j + m) → List (ℚ × ℚ) →
    Option (PolyN m × ℚ)
  | 0, q, [] =>
    match polyEnclose j q inner with
    | some I => some ((I.lo + I.hi) / 2, (I.hi - I.lo) / 2)
    | none => none
  | 0, _, _ :: _ => none
  | _ + 1, _, [] => none
  | m + 1, p, (lo, hi) :: outer =>
    reduceList (fun a => reduceInner j inner m a outer) (absMax lo hi) p

theorem reduceInner_sound (j : ℕ) (inner : List (ℚ × ℚ)) : ∀ (m : ℕ) (p : PolyN (j + m))
    (outer : List (ℚ × ℚ)) (p' : PolyN m) (K : ℚ), reduceInner j inner m p outer = some (p', K) →
      ∀ x, InBox (outer ++ inner) x → |(coeffsN (j + m)).eval p x - (coeffsN m).eval p' x| ≤ K
  | 0, q, [], p', K, h, x, hx => by
    simp only [reduceInner] at h
    cases he : polyEnclose j q inner with
    | none => simp [he] at h
    | some I =>
      simp only [he, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hm := polyEnclose_sound j q inner I he x hx
      show |(coeffsN j).eval q x - (((I.lo + I.hi) / 2 : ℚ) : ℝ)| ≤ (((I.hi - I.lo) / 2 : ℚ) : ℝ)
      push_cast
      rw [abs_le]
      constructor <;> linarith [hm.1, hm.2]
  | 0, _, _ :: _, _, _, h, _, _ => by simp [reduceInner] at h
  | _ + 1, _, [], _, _, h, _, _ => by simp [reduceInner] at h
  | m + 1, p, (lo, hi) :: outer, p', K, h, x, hx => by
    simp only [reduceInner] at h
    exact reduceList_sound (coeffsN (j + m)) (coeffsN m) _ (absMax lo hi) x
      (abs_le_absMax ⟨hx.1, hx.2.1⟩)
      (fun a a' K' ha => reduceInner_sound j inner m a outer a' K' ha (tailPt x) hx.2.2) p p' K h

/-- The arithmetic of polynomials in `j + m` variables whose positivity test reduces the last `j`
variables to the midpoints of interval enclosures, with the deviation bound subtracted, and tests
the resulting polynomial in the first `m` by its Bernstein coefficients. -/
def reducedCoeffs (j m : ℕ) : Coeffs (PolyN (j + m)) :=
  { coeffsN (j + m) with
    posOn := fun p box =>
      match reduceInner j (box.drop m) m p (box.take m) with
      | some (p', K) => (coeffsN m).posOn ((coeffsN m).add p' ((coeffsN m).ofRat (-K))) (box.take m)
      | none => false
    posOn_sound := by
      intro p box h x hx
      cases hr : reduceInner j (box.drop m) m p (box.take m) with
      | none => simp [hr] at h
      | some PK =>
        obtain ⟨p', K⟩ := PK
        simp only [hr] at h
        have hx' : InBox (box.take m ++ box.drop m) x := by rw [List.take_append_drop]; exact hx
        have hdev := reduceInner_sound j (box.drop m) m p (box.take m) p' K hr x hx'
        have hpos := (coeffsN m).posOn_sound _ _ h x (InBox.append_left hx')
        rw [(coeffsN m).eval_add, (coeffsN m).eval_ofRat] at hpos
        push_cast at hpos
        rw [abs_le] at hdev
        show 0 < (coeffsN (j + m)).eval p x
        linarith [hdev.1] }

end Cycle63.Certificate

end Record1252270103Bootstrap.PR67
