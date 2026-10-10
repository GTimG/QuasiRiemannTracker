import OAI.NumberTheory.DirichletL.Moments.ReflectionWeightedEnergy

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.WeightedNumeratorReflection
open HeckeFamily CenteredMomentReflectionWeightedEnergy

/-- Row-dependent absolutely summable coefficient packets preserve a fourth moment
when every independent rowwise choice has that fourth moment. -/
theorem weighted_fourth_selection {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀i, α i) (w f : ∀i, α i → ℂ) (M E : ℝ) (_hM : 0 ≤ M)
    (hs : ∀i, Summable (fun a => ‖w i a‖))
    (hm : ∀i, (∑'a, ‖w i a‖) ≤ M)
    (hselection : ∀a : ∀i, α i, (∑i, ‖f i (a i)‖^4) ≤ E) :
    (∀i, Summable (fun a => ‖w i a*f i a‖)) ∧
      (∑i, ‖∑'a, w i a*f i a‖^4) ≤ M^4*E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  have hpoint (i : ι) (a : α i) : ‖f i a‖^4 ≤ E := by
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j => ‖f j (Function.update base i a j)‖^4)
      (fun j _ => by positivity) (Finset.mem_univ i)
    exact (by simpa using hh : ‖f i a‖^4 ≤ ∑j, ‖f j (Function.update base i a j)‖^4).trans
      (hselection (Function.update base i a))
  let v (i : ι) : ℝ := ⨆a, ‖f i a‖^4
  have hbd (i : ι) : BddAbove (Set.range (fun a => ‖f i a‖^4)) :=
    ⟨E, by rintro _ ⟨a,rfl⟩; exact hpoint i a⟩
  have hv (i : ι) (a : α i) : ‖f i a‖^4 ≤ v i := le_ciSup (hbd i) a
  have hv0 (i : ι) : 0 ≤ v i := (by positivity : 0 ≤ ‖f i (base i)‖^4).trans (hv i (base i))
  have hnorm (i : ι) (a : α i) : ‖f i a‖ ≤ Real.sqrt (Real.sqrt (v i)) := by
    apply (Real.le_sqrt (norm_nonneg _) (Real.sqrt_nonneg _)).mpr
    apply (Real.le_sqrt (sq_nonneg _) (hv0 i)).mpr
    convert hv i a using 1 <;> ring
  have hw (i : ι) : Summable (fun a => ‖w i a*f i a‖) := by
    apply ((hs i).mul_right (Real.sqrt (Real.sqrt (v i)))).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _)
  have hsum (i : ι) : ‖∑'a, w i a*f i a‖ ≤ M*Real.sqrt (Real.sqrt (v i)) := by
    apply (norm_tsum_le_tsum_norm (hw i)).trans
    apply ((hw i).tsum_le_tsum (fun a => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _))
      ((hs i).mul_right (Real.sqrt (Real.sqrt (v i))))).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hm i) (Real.sqrt_nonneg _)
  have hroot (i : ι) : (Real.sqrt (Real.sqrt (v i)))^4 = v i := by
    calc
      _ = ((Real.sqrt (Real.sqrt (v i)))^2)^2 := by ring
      _ = v i := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (hv0 i)]
  refine ⟨hw,?_⟩
  calc
    (∑i, ‖∑'a, w i a*f i a‖^4) ≤ ∑i, (M*Real.sqrt (Real.sqrt (v i)))^4 :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hsum i) 4)
    _ = M^4*∑i, v i := by simp only [mul_pow,hroot,Finset.mul_sum]
    _ ≤ M^4*E := mul_le_mul_of_nonneg_left
      (sum_iSup_le_of_selection base (fun i a => ‖f i a‖^4) E hselection) (by positivity)

/-- The natural primitive restoration and annular weights have only a subpower cost
for fourth moments, including an arbitrary row-dependent mask of norm at most one. -/
theorem actual_masked_reflection_fourth (ε : ℝ) (hε : 0 < ε) :
    ∃C : ℝ, 0 < C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι → Finset (Ideal HeckeFamily.O)), (∀i P, P ∈ S i → Prime P) →
      ∀(η ηi : ι → Character) (B : ι → ℕ), (∀i, 2 ≤ B i) →
      ∀R E : ℝ, 1 ≤ R → (∀i, (Ideal.absNorm (∏P∈S i,P):ℝ) ≤ R) →
      ∀(mask f : ∀i, Index (S i) → ℂ), (∀i a, ‖mask i a‖ ≤ 1) →
      (∀a : ∀i, Index (S i), (∑i, ‖f i (a i)‖^4) ≤ E) →
      (∀i, Summable (fun a => ‖(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖)) ∧
      (∑i, ‖∑'a, (mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖^4)
        ≤ C*R^ε*E := by
  obtain ⟨C,hC,hb⟩ := uniform_signed_mass (ε/4) (by positivity)
  refine ⟨C^4,by positivity,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap mask f hmask hselection
  have hR0 : 0 ≤ R := by linarith
  let M := C*R^(ε/4)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hs (i : ι) := masked_signedWeight_summable_norm (η i) (ηi i) (S i)
    (hS i) (B i) (hB i) (mask i) (hmask i)
  have hm (i : ι) :
      (∑'a, ‖mask i a*signedWeight (η i) (ηi i) (S i) (B i) a‖) ≤ M := by
    apply (masked_signedWeight_mass_le (η i) (ηi i) (S i) (hS i) (B i) (hB i)
      (mask i) (hmask i)).trans
    apply (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hcap i) (by positivity : 0 ≤ ε/4)) hC.le
  have hh := weighted_fourth_selection (fun i => baseIndex (S i))
    (fun i a => mask i a*signedWeight (η i) (ηi i) (S i) (B i) a) f M E hM hs hm hselection
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hr : (R^(ε/4))^4 = R^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0]
    congr 1
    ring
  dsimp [M]
  rw [mul_pow,hr]

end SevenEighths.WeightedNumeratorReflection
end
end OAI
