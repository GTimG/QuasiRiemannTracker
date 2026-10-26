import Candidate.Cycle63.Marked.DeletionRawLift

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open LocalMoment ConcretePrimeRowBridge
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- All actual zero cores, including the finite inducing exceptions,
satisfy the ordinary density bound on every window of size at least one. -/
theorem actual_core_density_uniform {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0<loss) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀(a T Y : ℝ),4/5≤a → a≤7/8 → 0≤T → 1≤Y →
      ∀F : Finset FreeRow,
      (∀u∈F,rowNorm u≤Y ∧
        (rawZeroBin D.data a (7/8) T ⟨u.val,u.property.1⟩ ∨ D.exceptionalCore u)) →
      (F.card : ℝ)≤C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,hJ⟩ := fixed_dictionary_eventual_with_exceptions (Label := Label) loss hloss
  obtain ⟨C,hC,hf⟩ := hJ D
  let P : DensityParameter → FreeRow → Prop := fun p u=>
    rawZeroBin D.data p.val.1 (7/8) p.val.2 ⟨u.val,u.property.1⟩ ∨ D.exceptionalCore u
  let exponent : DensityParameter → ℝ := fun p=>unmarkedDensity (2*p.val.1-1)+loss
  let weight : DensityParameter → ℝ := fun p=>(1+p.val.2)^J
  have hρ (p : DensityParameter) : 2/7≤exponent p := by
    dsimp [exponent]
    linarith [unmarkedDensity_ge_two_sevenths
      (show 2*p.val.1-1≤3/4 by linarith [p.property.2.1])]
  have hw (p : DensityParameter) : 1≤weight p := one_le_pow₀ (by linarith [p.property.2.2])
  have hevent : ∀ᶠY : ℝ in atTop,∀p : DensityParameter,∀F : Finset FreeRow,
      (∀u∈F,rowNorm u≤Y ∧ P p u) → (F.card : ℝ)≤C*weight p*Y^exponent p := by
    filter_upwards [hf] with Y hf
    intro p
    exact hf p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2
  obtain ⟨C',hC',_,hfree⟩ := uniform_free_density_weighted_of_eventually P C exponent weight
    (fun p=>by linarith [hρ p]) hw hevent
  refine ⟨J,C',hC',?_⟩
  intro a T Y ha ha' hT hY F hF
  exact hfree Y hY ⟨(a,T),ha,ha',hT⟩ F hF

/-- The large-root half of the marked raw convolution is unconditional:
actual zero transport, all exceptional cores, and the ordinary pointwise
slot envelope supply its fiber estimate. -/
theorem actual_ordinary_weighted_fibers {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0<loss) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀(reverse : Label→Bool)(a T H envelope : ℝ),
      4/5≤a → a≤7/8 → 0≤T → 0<H → 0≤envelope →
      ∀(R : Finset NonzeroFrequency)(f : NonzeroFrequency→ℝ),
      (∀u∈R,rawFrequencyNorm u≤H ∧ orientedActualZeroRow D.data reverse a T u) →
      (∀u∈R,f u≤envelope) → ∀B : NZIdeal,
      (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
        (C*(1+T)^J)*envelope*(H/(B.val.absNorm : ℝ)^6)^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hfree⟩ := actual_core_density_uniform D loss hloss
  refine ⟨J,C,hC,?_⟩
  intro reverse a T H envelope ha ha' hT hH henv R f hR hf B
  let Y : ℝ := H/(B.val.absNorm : ℝ)^6
  have hBp : 0<(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hraw (u : FreeRow) (hu : u∈sixthFreeFiber R B) : sixthFrequencyEquiv (u,B)∈R := by
    obtain ⟨p,hp,hpu⟩ := Finset.mem_image.mp hu
    obtain ⟨hp,hpB⟩ := Finset.mem_filter.mp hp
    have he : p=(u,B) := Prod.ext hpu hpB
    subst p
    exact (mem_sixthPairs R (u,B)).mp hp
  have hmem (u : FreeRow) (hu : u∈sixthFreeFiber R B) : rowNorm u≤Y ∧
      (rawZeroBin D.data a (7/8) T ⟨u.val,u.property.1⟩ ∨ D.exceptionalCore u) := by
    have hr := hR _ (hraw u hu)
    rw [raw_sixth_norm] at hr
    refine ⟨(le_div_iff₀ (pow_pos hBp 6)).mpr hr.1,?_⟩
    simpa only [Equiv.symm_apply_apply] using
      oriented_zero_core_predicate D reverse a T ha (sixthFrequencyEquiv (u,B)) hr.2
  by_cases hY : 1≤Y
  · have hc := hfree a T Y ha ha' hT hY (sixthFreeFiber R B) hmem
    calc
      _ ≤ ∑u∈sixthFreeFiber R B,envelope := Finset.sum_le_sum (fun u hu=>hf _ (hraw u hu))
      _ = ((sixthFreeFiber R B).card : ℝ)*envelope := by simp
      _ ≤ (C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss))*envelope :=
        mul_le_mul_of_nonneg_right hc henv
      _ = _ := by dsimp [Y];ring
  · have hempty : sixthFreeFiber R B=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hY ((rowNorm_ge_one u).trans (hmem u hu).1)
    rw [hempty,Finset.sum_empty]
    positivity

end
end OAI.SevenEighths.Deletion26
