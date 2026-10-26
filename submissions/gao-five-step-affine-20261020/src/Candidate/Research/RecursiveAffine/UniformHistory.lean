/- Uniform joint history count with moving dyad boxes kept explicit. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.DecoratedHistory
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic Cycle63Moment
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

theorem append_decorated_fibre_count_uniform (B Q loss : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {P : Type*} (v : P → O) (left : Bool)
      (unit : P → FirstSourceLabel → O) (oldMissing : P → ℝ) (Z : ℝ), 2 ≤ Z →
      ∀ (box : Finset (Fin 4 → ℤ)) (S : Finset (P × DecoratedPrefix)) (A : ℝ), 0 ≤ A →
      (∀ x ∈ S, DecoratedFacts v left unit Z B box x) →
      (∀ p ∈ S.image Prod.fst, 0 ≤ oldMissing p ∧ oldMissing p ≤ Q) →
      (∀ t : ℝ, ∀ D : Ideal O,
        ((((S.image Prod.fst).filter (fun p => oldMissing p ≤ t)).filter
          (fun p => Ideal.span {v p} = D)).card : ℝ) ≤ A*Z^t) →
      ∀ m : ℝ, ∀ D : Ideal O,
        ((S.filter (fun x => oldMissing x.1 + stepMissing left Z x.2.1 ≤ m ∧
          Ideal.span {appendMultiplier v left unit (forgetDecoration x)} = D)).card : ℝ) ≤ C*((box.card : ℝ)+1)*A*Z^(m+loss) := by
  obtain ⟨Ca,hCa,ha⟩ := append_prefix_fibre_count B Q (loss/2) hB hQ (by positivity)
  obtain ⟨Cd,hCd,hd⟩ := decoration_fibre_bound B (loss/2) hB (by positivity)
  refine ⟨Ca*Cd, by positivity, ?_⟩
  intro P v left unit oldMissing Z hZ box S A hA hfact hrange hpre m D
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

/-- Constants are uniform in the boxes, which may now depend on the moving height Z.
The source's existing dyad-box subpower estimates can be applied to the explicit product. -/
theorem finite_history_fibre_count_uniform (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (boxes : ℕ → Finset (Fin 4 → ℤ))
      (units : ∀ k, History k → FirstSourceLabel → O) (left : ℕ → Bool)
      (root : O) (Z : ℝ), 2 ≤ Z → ∀ S : Finset (History n),
      (∀ x ∈ S, HistoryFacts units left root Z B boxes n x) →
      ∀ m : ℝ, ∀ D : Ideal O,
      ((S.filter (fun x => historyMissing left Z n x ≤ m ∧
        Ideal.span {historyMultiplier units left root n x} = D)).card : ℝ) ≤
        C*(∏ k ∈ Finset.range n, (((boxes k).card : ℝ)+1))*Z^(m+loss) := by
  induction n generalizing loss with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro boxes units left root Z hZ S hf m D
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
    have hc' : (F.card : ℝ) ≤ 1 := by exact_mod_cast hc
    simpa only [Finset.range_zero,Finset.prod_empty,one_mul] using hc'.trans hz
  | succ n ih =>
    obtain ⟨Ci,hCi,hi⟩ := ih (loss/2) (by positivity)
    obtain ⟨Ca,hCa,ha⟩ := append_decorated_fibre_count_uniform B ((n : ℝ)*B) (loss/2) hB
      (mul_nonneg (Nat.cast_nonneg _) hB) (by positivity)
    refine ⟨Ca*Ci, mul_pos hCa hCi, ?_⟩
    intro boxes units left root Z hZ S hf m D
    have hZ0 : 0 < Z := by linarith
    let Pc : ℝ := ∏ k ∈ Finset.range n, (((boxes k).card : ℝ)+1)
    let A := Ci*Pc*Z^(loss/2)
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
      have hh := hi boxes units left root Z hZ (S.image Prod.fst) hp t I
      rw [Finset.filter_filter]
      calc _ ≤ Ci*Pc*Z^(t+loss/2) := hh
        _ = A*Z^t := by
          dsimp [A]
          have he : Z^(t+loss/2)=Z^(loss/2)*Z^t := by
            rw [← Real.rpow_add hZ0]
            congr 1
            ring
          rw [he]
          ring
    have hh := ha (historyMultiplier units left root n) (left n) (units n) (historyMissing left Z n) Z hZ
      (boxes n) S A (by dsimp [A,Pc]; positivity) (fun x hx => (hf x hx).2) hrange hpre m D
    calc _ ≤ Ca*((boxes n).card+1)*A*Z^(m+loss/2) := hh
      _ = (Ca*Ci)*(∏ k ∈ Finset.range (n+1), (((boxes k).card : ℝ)+1))*Z^(m+loss) := by
        rw [Finset.prod_range_succ]
        have he : Z^(loss/2)*Z^(m+loss/2)=Z^(m+loss) := by
          rw [← Real.rpow_add hZ0]
          congr 1
          ring
        dsimp [A,Pc]
        calc Ca*((boxes n).card+1)*(Ci*(∏ k ∈ Finset.range n, (((boxes k).card : ℝ)+1))*Z^(loss/2))*Z^(m+loss/2)
            = (Ca*Ci)*((∏ k ∈ Finset.range n, (((boxes k).card : ℝ)+1))*((boxes n).card+1))*
              (Z^(loss/2)*Z^(m+loss/2)) := by ring
          _ = _ := by rw [he]

#print axioms finite_history_fibre_count_uniform
end
end OAI.SevenEighths.Cycle153JointCount
