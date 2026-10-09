# Unresolved analytic implication — not a claim of a manuscript error

The precise first major unfinished claim is `lem:plain`, accepted-answer.tex lines 7874–7926. It asserts an actual row sum

    ∑ k ∈ R_z, ‖S_{ψ_k}(n₁; W₁) S_{ψ_k}(n₂; W₂) ∏ i, Q_{ψ_k,i}‖² ≪ Z^(M+ε)

for κ ∈ [13/18,1]. For z=0 it permits all bounded nonnegative plain lengths and no lower conductor bound. For z>0 its capacity condition is n₁+n₂+6κz≤M; when κ<1 it assumes β_*≤(1+κ)/2. For κ=1 it does not assume a zero-free region. The row family is nonprincipal for z=0 and excludes the fixed inducing-character family Θ for z>0.

The missing proof must use the actual Eisenstein ray characters and polynomials, the full displayed moving radical before phase cancellation, all zero extensions, and a common admissible puncture mask. The mesh is chosen for each ε and bounded length range uniformly in κ, independently of the fixed slot count. The constants for each fixed arithmetic datum and slot count use finitely many smooth seminorms and a fixed polynomial in the separated norm-twist heights, uniformly in moving moduli, masks and frozen labels. An unproved proposition or a structure field asserting this estimate would not discharge it.

At the pinned upstream source, `OAI.SevenEighths.CenteredMomentEnergyCertifiedExistence.terminal_certificate` (Energy/CertifiedExistence.lean:40) and its band/successor proof require `(3/4 : ℝ) ≤ κ`. The application here requires κ=2B−1 for θ<B≤1. For θ<B<7/8 this hypothesis is false. `QRH.old_moment_range_insufficient` gives an explicit checked witness. `QRH.dynamic_kappa` proves the correct extended interval, but supplies no analytic estimate.

The real inequalities needed for the revised centering and reflected low branch have been proved in `QRH.Geometry` and `QRH.PlainReflectionGeometry`, including κ≥13/18, z<M/20, and the 23M/30 and 14M/15 comparison constants. They still need integration through the actual common-coefficient transport, both transforms, equality of product-scale main terms before absolute estimates, and the capped-width analytic induction. `audit/plain-extension-sites.tsv` inventories affected parameter sites; it is not a proof that textual replacement is sound.

After that extension, independent obligations remain: identify the actual probe in both representations for the optimized geometry; obtain the inverse/plain row counts, detector and nonprincipal/local-error estimates with all uniform losses; use the checked continuous exponent bounds to prove an actual uniform probe saving; discharge the Mellin/supremum continuation premises; then transfer to all Dirichlet characters, the zeta convention at one, and all finite-order Hecke characters over the Eisenstein field. None of these final analytic statements is asserted by the partial library.

No mathematical contradiction or counterexample to the manuscript has been established. This is a precise record of missing formal proofs, not an invented analytic assumption and not a declaration that the original theorem is false.

A narrower resumption inventory, `audit/analytic-extension-frontier.json`, follows the actual successor's import graph: 2,210 OpenAI modules, with 56 explicit old κ lower-bound sites in 41 files. This is a source inventory only, not a source-build result. The next analytic build command is:

```sh
python3 scripts/build_source.py OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor --jobs 6
```

After checking this slice, generalize its low/reference-branch consumers to the proved extended bounds and propagate the changed reserve constants through the high/zero stages. Each module must compile and retain its actual mask/character/coefficient hypotheses. The current partial-library build does not include this full analytic successor. Do not treat the 56 sites as a safe search-and-replace operation.
