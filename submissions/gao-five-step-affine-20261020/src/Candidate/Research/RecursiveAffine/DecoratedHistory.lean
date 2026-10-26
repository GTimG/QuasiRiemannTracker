/- Actual source-prefix keys retain the seed and the complete dyad code.
The native physical block injects into precisely these keys. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.FiniteDepthPrefix
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic Cycle63Moment
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- No residual ideal is enumerated. The seed is a squarefree divisor of the second common C,
and the four integer coordinates are the native second-block dyad. -/
def DecoratedPrefix := ChildPrefix × Ideal O × (Fin 4 → ℤ)

def forgetDecoration {P : Type*} (x : P × DecoratedPrefix) : P × ChildPrefix := (x.1,x.2.1)

structure DecoratedFacts {P : Type*} (v : P → O) (left : Bool)
    (unit : P → FirstSourceLabel → O) (Z B : ℝ) (box : Finset (Fin 4 → ℤ))
    (x : P × DecoratedPrefix) : Prop where
  source : StepFacts v left unit Z B (forgetDecoration x)
  seed_squarefree : Squarefree x.2.2.1
  seed_divides : x.2.2.1 ∣ x.2.1.2.1.1
  dyad_mem : x.2.2.2 ∈ box

/-- Source-native decoration multiplicity. The only extra labels are squarefree divisors and fixed dyads. -/
theorem decoration_fibre_bound (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {P : Type*} (v : P → O) (left : Bool)
      (unit : P → FirstSourceLabel → O) (Z : ℝ), 2 ≤ Z →
      ∀ (box : Finset (Fin 4 → ℤ)) (S : Finset (P × DecoratedPrefix)),
      (∀ x ∈ S, DecoratedFacts v left unit Z B box x) →
      ∀ y : P × ChildPrefix,
        ((S.filter (fun x => forgetDecoration x = y)).card : ℝ) ≤ C*Z^loss*box.card := by
  let eps := loss/(B+1)
  have heps : 0 < eps := div_pos hloss (by positivity)
  obtain ⟨C, hC, hdiv⟩ := SquarefreeDivisorBound.squarefree_divisor_small_power eps heps
  refine ⟨C, hC, ?_⟩
  intro P v left unit Z hZ box S hfact y
  let F := S.filter (fun x => forgetDecoration x = y)
  rcases F.eq_empty_or_nonempty with hempty | ⟨x₀,hx₀⟩
  · change (F.card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  have hx₀S := (Finset.mem_filter.mp hx₀).1
  have hxy := (Finset.mem_filter.mp hx₀).2
  have hCy : y.2.2.1.1 ≠ ⊥ := by
    have hh := (hfact x₀ hx₀S).source.supported.2.2.1.1
    change (forgetDecoration x₀).2.2.1.1 ≠ ⊥ at hh
    rwa [hxy] at hh
  have hCcap : (y.2.2.1.1.absNorm : ℝ) ≤ Z^B := by
    have hh := (hfact x₀ hx₀S).source.ideal_cap.2.2.1
    change ((forgetDecoration x₀).2.2.1.1.absNorm : ℝ) ≤ Z^B at hh
    rwa [hxy] at hh
  let code := fun x : P × DecoratedPrefix => x.2.2
  have hmaps : ∀ x ∈ F, code x ∈ ((idealDivisors y.2.2.1.1).filter Squarefree) ×ˢ box := by
    intro x hx
    obtain ⟨hxS,hxy'⟩ := Finset.mem_filter.mp hx
    have hfx := hfact x hxS
    have hCeq : x.2.1.2.1.1 = y.2.2.1.1 := congrArg (fun z : P × ChildPrefix => z.2.2.1.1) hxy'
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨(mem_idealDivisors hCy).mpr (by rw [← hCeq]; exact hfx.seed_divides), hfx.seed_squarefree⟩,
      hfx.dyad_mem⟩
  have hinj : Set.InjOn code (F : Set (P × DecoratedPrefix)) := by
    intro x hx x' hx' hc
    have he : forgetDecoration x = forgetDecoration x' :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hx').2.symm
    have hp : x.1 = x'.1 := congrArg (fun z : P × ChildPrefix => z.1) he
    have hcpre : x.2.1 = x'.2.1 := congrArg (fun z : P × ChildPrefix => z.2) he
    exact Prod.ext hp (Prod.ext hcpre hc)
  have hc := Finset.card_le_card_of_injOn code hmaps hinj
  rw [Finset.card_product] at hc
  have he : B*eps ≤ loss := by
    have hid : eps*(B+1)=loss := by dsimp [eps]; field_simp
    nlinarith
  have hb : (((idealDivisors y.2.2.1.1).filter Squarefree).card : ℝ) ≤ C*Z^loss := by
    calc (((idealDivisors y.2.2.1.1).filter Squarefree).card : ℝ)
        ≤ C*(y.2.2.1.1.absNorm : ℝ)^eps := hdiv _ hCy
      _ ≤ C*(Z^B)^eps := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hCcap heps.le) hC.le
      _ = C*Z^(B*eps) := by rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ Z)]
      _ ≤ C*Z^loss := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith) he) hC.le
  exact (show (F.card : ℝ) ≤ (((idealDivisors y.2.2.1.1).filter Squarefree).card : ℝ)*box.card by
    exact_mod_cast hc).trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))

/-- Append one complete physical key, including its seed and dyad. Constants precede all moving sources.
Historical missing radicals retain coefficient one; the decoration consumes only an arbitrary small loss. -/
theorem append_decorated_fibre_count (B Q loss : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hloss : 0 < loss)
    (box : Finset (Fin 4 → ℤ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {P : Type*} (v : P → O) (left : Bool)
      (unit : P → FirstSourceLabel → O) (oldMissing : P → ℝ) (Z : ℝ), 2 ≤ Z →
      ∀ (S : Finset (P × DecoratedPrefix)) (A : ℝ), 0 ≤ A →
      (∀ x ∈ S, DecoratedFacts v left unit Z B box x) →
      (∀ p ∈ S.image Prod.fst, 0 ≤ oldMissing p ∧ oldMissing p ≤ Q) →
      (∀ t : ℝ, ∀ D : Ideal O,
        ((((S.image Prod.fst).filter (fun p => oldMissing p ≤ t)).filter
          (fun p => Ideal.span {v p} = D)).card : ℝ) ≤ A*Z^t) →
      ∀ m : ℝ, ∀ D : Ideal O,
        ((S.filter (fun x => oldMissing x.1 + stepMissing left Z x.2.1 ≤ m ∧
          Ideal.span {appendMultiplier v left unit (forgetDecoration x)} = D)).card : ℝ) ≤ C*A*Z^(m+loss) := by
  obtain ⟨Ca,hCa,ha⟩ := append_prefix_fibre_count B Q (loss/2) hB hQ (by positivity)
  obtain ⟨Cd,hCd,hd⟩ := decoration_fibre_bound B (loss/2) hB (by positivity)
  refine ⟨Ca*Cd*((box.card : ℝ)+1), by positivity, ?_⟩
  intro P v left unit oldMissing Z hZ S A hA hfact hrange hpre m D
  let F := S.filter (fun x => oldMissing x.1 + stepMissing left Z x.2.1 ≤ m ∧
    Ideal.span {appendMultiplier v left unit (forgetDecoration x)} = D)
  let Sb := S.image forgetDecoration
  have hparents : Sb.image Prod.fst = S.image Prod.fst := by
    simp only [Sb, Finset.image_image]
    rfl
  have hfb : ∀ x ∈ Sb, StepFacts v left unit Z B x := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (hfact y hy).source
  have hb := ha v left unit oldMissing Z hZ Sb A hA hfb
    (by rw [hparents]; exact hrange) (by rw [hparents]; exact hpre) m D
  have hsub : F.image forgetDecoration ⊆ Sb.filter (fun x => oldMissing x.1 + stepMissing left Z x.2 ≤ m ∧
      Ideal.span {appendMultiplier v left unit x} = D) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hy).1,
      (Finset.mem_filter.mp hy).2⟩
  have hFsub : F ⊆ S := Finset.filter_subset _ _
  have hcard (x : P × ChildPrefix) : ((F.filter (fun y => forgetDecoration y = x)).card : ℝ) ≤
      Cd*Z^(loss/2)*box.card := by
    have hh := hd v left unit Z hZ box F (fun y hy => hfact y (hFsub hy)) x
    exact hh
  have hfib := Finset.card_eq_sum_card_fiberwise
    (fun x (hx : x ∈ F) => Finset.mem_image_of_mem forgetDecoration hx)
  have hZ0 : 0 < Z := by linarith
  change (F.card : ℝ) ≤ _
  calc (F.card : ℝ)
      = ∑ x ∈ F.image forgetDecoration, ((F.filter (fun y => forgetDecoration y = x)).card : ℝ) := by
          exact_mod_cast hfib
    _ ≤ ∑ _x ∈ F.image forgetDecoration, Cd*Z^(loss/2)*box.card :=
        Finset.sum_le_sum (fun x _ => hcard x)
    _ = ((F.image forgetDecoration).card : ℝ)*(Cd*Z^(loss/2)*box.card) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (Ca*A*Z^(m+loss/2))*(Cd*Z^(loss/2)*box.card) :=
        mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hb) (by positivity)
    _ ≤ (Ca*A*Z^(m+loss/2))*(Cd*Z^(loss/2)*((box.card : ℝ)+1)) := by
        gcongr
        linarith
    _ = (Ca*Cd*((box.card : ℝ)+1))*A*Z^(m+loss) := by
        have he : Z^(m+loss/2)*Z^(loss/2)=Z^(m+loss) := by
          rw [← Real.rpow_add hZ0]
          congr 1
          ring
        calc (Ca*A*Z^(m+loss/2))*(Cd*Z^(loss/2)*((box.card : ℝ)+1))
            = (Ca*Cd*((box.card : ℝ)+1))*A*(Z^(m+loss/2)*Z^(loss/2)) := by ring
          _ = _ := by rw [he]

/-- A depth-n history is the complete chain of arithmetic prefix, seed and dyad keys. -/
def History : ℕ → Type
  | 0 => Unit
  | n+1 => History n × DecoratedPrefix

def historyMultiplier (units : ∀ n, History n → FirstSourceLabel → O) (left : ℕ → Bool) (root : O) :
    ∀ n, History n → O
  | 0, _ => root
  | n+1, x => appendMultiplier (historyMultiplier units left root n) (left n) (units n) (forgetDecoration x)

/-- Every descendant remains a literal row multiplier in the original fixed dictionary. -/
theorem root_dvd_historyMultiplier (units : ∀ n, History n → FirstSourceLabel → O)
    (left : ℕ → Bool) (root : O) : ∀ n (x : History n), root ∣ historyMultiplier units left root n x := by
  intro n
  induction n with
  | zero => intro x; exact dvd_refl root
  | succ n ih =>
    intro x
    exact dvd_trans (ih x.1)
      (old_multiplier_dvd_append (historyMultiplier units left root n) (left n) (units n) (forgetDecoration x))

def historyMissing (left : ℕ → Bool) (Z : ℝ) : ∀ n, History n → ℝ
  | 0, _ => 0
  | n+1, x => historyMissing left Z n x.1 + stepMissing (left n) Z x.2.1

def HistoryFacts (units : ∀ n, History n → FirstSourceLabel → O) (left : ℕ → Bool)
    (root : O) (Z B : ℝ) (boxes : ℕ → Finset (Fin 4 → ℤ)) : ∀ n, History n → Prop
  | 0, _ => True
  | n+1, x => HistoryFacts units left root Z B boxes n x.1 ∧
    DecoratedFacts (historyMultiplier units left root n) (left n) (units n) Z B (boxes n) x

theorem historyMissing_bounds (units : ∀ n, History n → FirstSourceLabel → O) (left : ℕ → Bool)
    (root : O) (Z B : ℝ) (hZ : 1 < Z) (boxes : ℕ → Finset (Fin 4 → ℤ)) :
    ∀ n (x : History n), HistoryFacts units left root Z B boxes n x →
      0 ≤ historyMissing left Z n x ∧ historyMissing left Z n x ≤ (n : ℝ)*B := by
  intro n
  induction n with
  | zero => intro x hx; simp [historyMissing]
  | succ n ih =>
    intro x hx
    have hp := ih x.1 hx.1
    have hs := stepMissing_bounds _ _ _ Z B hZ (forgetDecoration x) hx.2.source
    change 0 ≤ stepMissing (left n) Z x.2.1 ∧ stepMissing (left n) Z x.2.1 ≤ B at hs
    change 0 ≤ historyMissing left Z n x.1 + stepMissing (left n) Z x.2.1 ∧
      historyMissing left Z n x.1 + stepMissing (left n) Z x.2.1 ≤ (↑(n+1) : ℝ)*B
    rw [Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith

/-- The joint prefix count at every fixed finite depth, derived from native arithmetic counts.
All previous missing radical logs enter once. Restricting to earlier LOW histories only removes keys. -/
theorem finite_history_fibre_count (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss)
    (boxes : ℕ → Finset (Fin 4 → ℤ)) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (units : ∀ k, History k → FirstSourceLabel → O) (left : ℕ → Bool)
      (root : O) (Z : ℝ), 2 ≤ Z → ∀ S : Finset (History n),
      (∀ x ∈ S, HistoryFacts units left root Z B boxes n x) →
      ∀ m : ℝ, ∀ D : Ideal O,
      ((S.filter (fun x => historyMissing left Z n x ≤ m ∧
        Ideal.span {historyMultiplier units left root n x} = D)).card : ℝ) ≤ C*Z^(m+loss) := by
  induction n generalizing loss with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro units left root Z hZ S hf m D
    let F := S.filter (fun x => historyMissing left Z 0 x ≤ m ∧
      Ideal.span {historyMultiplier units left root 0 x} = D)
    rcases F.eq_empty_or_nonempty with hempty | ⟨x,hx⟩
    · change (F.card : ℝ) ≤ _
      rw [hempty,Finset.card_empty,Nat.cast_zero]
      positivity
    have hm : 0 ≤ m := (Finset.mem_filter.mp hx).2.1
    letI : Fintype (History 0) := inferInstanceAs (Fintype Unit)
    have hc : F.card ≤ 1 := by
      calc F.card ≤ Fintype.card Unit := Finset.card_le_univ F
        _ = 1 := Fintype.card_unit
    have hz : (1 : ℝ) ≤ Z^(m+loss) := Real.one_le_rpow (by linarith) (by linarith)
    change (F.card : ℝ) ≤ _
    have hc' : (F.card : ℝ) ≤ 1 := by exact_mod_cast hc
    simpa only [one_mul] using hc'.trans hz
  | succ n ih =>
    obtain ⟨Ci,hCi,hi⟩ := ih (loss/2) (by positivity)
    obtain ⟨Ca,hCa,ha⟩ := append_decorated_fibre_count B ((n : ℝ)*B) (loss/2) hB
      (mul_nonneg (Nat.cast_nonneg _) hB) (by positivity) (boxes n)
    refine ⟨Ca*Ci, mul_pos hCa hCi, ?_⟩
    intro units left root Z hZ S hf m D
    have hZ0 : 0 < Z := by linarith
    let A := Ci*Z^(loss/2)
    have hp : ∀ x ∈ S.image Prod.fst, HistoryFacts units left root Z B boxes n x := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (hf y hy).1
    have hrange : ∀ x ∈ S.image Prod.fst,
        0 ≤ historyMissing left Z n x ∧ historyMissing left Z n x ≤ (n : ℝ)*B := by
      intro x hx
      exact historyMissing_bounds units left root Z B (by linarith) boxes n x (hp x hx)
    have hpre : ∀ t : ℝ, ∀ I : Ideal O,
        ((((S.image Prod.fst).filter (fun x => historyMissing left Z n x ≤ t)).filter
          (fun x => Ideal.span {historyMultiplier units left root n x} = I)).card : ℝ) ≤ A*Z^t := by
      intro t I
      have hh := hi units left root Z hZ (S.image Prod.fst) hp t I
      rw [Finset.filter_filter]
      calc _ ≤ Ci*Z^(t+loss/2) := hh
        _ = A*Z^t := by
          dsimp [A]
          rw [mul_assoc, ← Real.rpow_add hZ0]
          congr 1
          ring
    have hh := ha (historyMultiplier units left root n) (left n) (units n) (historyMissing left Z n) Z hZ S A
      (by dsimp [A]; positivity) (fun x hx => (hf x hx).2) hrange hpre m D
    change _ ≤ _ at hh
    calc _ ≤ Ca*A*Z^(m+loss/2) := hh
      _ = (Ca*Ci)*Z^(m+loss) := by
        dsimp [A]
        have he : Z^(loss/2)*Z^(m+loss/2)=Z^(m+loss) := by
          rw [← Real.rpow_add hZ0]
          congr 1
          ring
        calc Ca*(Ci*Z^(loss/2))*Z^(m+loss/2)
            = (Ca*Ci)*(Z^(loss/2)*Z^(m+loss/2)) := by ring
          _ = _ := by rw [he]

#print axioms append_decorated_fibre_count
#print axioms finite_history_fibre_count
end
end OAI.SevenEighths.Cycle153JointCount
