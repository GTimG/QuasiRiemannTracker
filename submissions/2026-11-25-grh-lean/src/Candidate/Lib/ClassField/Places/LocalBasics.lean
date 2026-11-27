import Candidate.Lib.Cyclotomic.Voronoi.StickelbergerInteger
import Candidate.Lib.Cyclotomic.Kolyvagin.Components

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Principal units, places above q, primes 1 mod m split in cyclotomic fields. -/


variable {q m : ℕ} [NeZero m] {B : ClosurePlace} [Fact q.Prime]

/-- The action of Gal(Ω/ℚ) on the multiplicative group Ω^×, written additively, as a ℤ-linear
representation. -/
noncomputable abbrev galUnitsRep := @unitsRep Gal(Ω/ℚ) Ω _ _ _

/-- The principal units of the valuation subring B of ℚ̄ (elements congruent to 1 modulo its
maximal ideal), as a subgroup of ℚ̄^× written additively. -/
noncomputable def principalUnits (B : ClosurePlace) : AddSubgroup (DiscreteUnits Ω) :=
  B.principalUnitGroup.toAddSubgroup

lemma exists_isPlaceOver_prime (h : B.valuation q < 1) : ∃ v : FinPlace ℚ, IsPlaceOver B v ∧ v.q =
  q ∧ ordRat ℚ B (.ofNeZero q NeZero.out) = 1 := (exists_rat_place_of_prime Fact.out).imp fun _ ⟨e,
  _, H⟩ ↦ ⟨H B h, e.1, by convert (H B h).ordRat_ofBase (Γ := Gal(Ω/ℚ)) (.mk0 ..) <;> aesop⟩

lemma decompGroup_le_cycloGalGroup (h : B q < 1) (k : q ≡ 1 [MOD m]) : decompGroup _ B ≤
  cycloGalGroup m := by
  obtain ⟨⟨_, v, ⟨⟩, _⟩, c⟩ := exists_isPlaceOver_prime h, k.coprime_of_modEq_one.valuation_eq_one h
  exact (v.exists_isFrob _).rec fun _ f ↦ v.decompGroup_le f Fact.out (fun _ ↦
    (cycCharMod_of_mem_inertiaGroup · c)) ((f.mem_ker_cycCharMod_iff c).2 k)
