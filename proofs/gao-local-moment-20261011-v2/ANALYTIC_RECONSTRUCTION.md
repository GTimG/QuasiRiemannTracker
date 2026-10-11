# Joint-label reconstruction: a general counting lemma and its source boundary

11 October 2026. Mathematical development note; not a full local-moment proof.

This note separates a general arithmetic counting argument from the unresolved
identification of the physical transformed expression with that argument.
It supplements, and does not overwrite, the earlier published snapshot.

## 1. Fix the character convention first

In the pinned formal source, `CenteredMomentActive.netExponent c d` is
`(c + 5*d) % 6`. The first separated coefficients are literally

\[
 L(n)=\operatorname{idealRowHom}(er,(n))\rho(n),\qquad
 D(n)=\operatorname{idealRowHom}(er,(n))\overline{\rho(n)}.
\]

Here `rho` is `finiteSexticRow` with that net exponent. These are the
definitions `leftCoefficient` and `rightCoefficient` in
`OAI/NumberTheory/DirichletL/Moments/FirstColumns.lean`.
`FirstNormalization.normalized_active_coefficient` has the factor
`finiteSexticRow ... (a*b)` with no conjugation, and conjugates its value
at the frequency instead. `FirstWholeAssembly.finite_whole_children` retains
these coefficients in the actual first-transform expression.

Thus, when the signed exponent t is the formal net exponent c-d, reciprocity
gives the candidate reduced row exponents **1+t on the left and 1-t on the
right**, modulo six, up to the fixed ray phases. The earlier manuscript-side
convention called the opposite phase t, yielding 1-t and 1+t. These conventions
cannot be identified without changing the sign of t. For example, formal
t=1 gives residues 2 and 0, not 0 and 2.

The scalar estimates use only that each residue is in {0,...,5} and explicitly
count the zero residues. They therefore survive this interchange. The actual
character identity, however, must use the formal convention. This note fixes
that convention; it does not claim that all subsequent row and mask identities
have been proved in Lean.

Primary source: Cycle25 at
`58344dfdbe756cf2f743da1908ffe0582418cf5b`, with its retained OAI import closure.

## 2. Ideals with a prescribed prime support

Work in the fixed ring of Eisenstein integers. Let B,T>0 be fixed. For every
epsilon>0, uniformly for Z>=2 and squarefree ideals Q with NQ<=Z^B,

\[
 \#\{I\ne0: NI\le Z^T,\ \operatorname{rad} I\mid Q\}
 \ll_{B,T,\epsilon} Z^\epsilon.                         \tag{1}
\]

Proof. For any a>0, summing the geometric series at the primes of Q gives

\[
 \#\{I\}\le Z^{aT}\prod_{\mathfrak p\mid Q}
                 (1-(N\mathfrak p)^{-a})^{-1}.
\]

Choose aT<=epsilon/2. Given b>0, all sufficiently large prime norms satisfy
`(1-(Np)^(-a))^(-1) <= (Np)^b`. The remaining primes form a fixed finite set
and contribute a constant depending on a,b and the field. Consequently the
product is at most a constant times `(NQ)^b`. Choose bB<=epsilon/2. This
proves (1), including Q=1.

Likewise, for any fixed integer K, `K^(omega(Q)) << (NQ)^b`: apply
`K <= (Np)^b` at all sufficiently large prime norms, and absorb the finitely
many smaller primes into the constant. This pays any fixed finite choice
of a local allocation at each prime. Uniformity in an unbounded number of
slots is not asserted; the slot system is fixed before the final threshold,
as in the source quantifier order.

## 3. Reconstruction at a fixed effective row

Consider tuples of nonzero integral ideals/elements with first common
support S=rad(CD), active subradical r, and a squarefree divisor e of S/r.
Let f(p) be either of the corrected residues in Section 1 at primes of r;
put F=product p^(f(p)), and r0=product over p|r with f(p)=0.
Let D2,E2 have the same complete prime support, let G=gcd(D2,E2), and let
V be a squarefree divisor of that support. Suppose the actual row is

\[
 w=F e G V h\ne0.                                      \tag{2}
\]

The elements representing ideals use the fixed primary-generator convention;
the remaining unit choices have bounded cardinality. Suppose also that the
first projector s is squarefree and divides rad(D2 E2). Write

\[
 p=\log_Z NS,\quad R=\log_Z Nr,\quad E=\log_Z Ne,
 \quad R_0=\log_Z Nr_0.
\]

Define the *missing first radical* L to be the product of primes of S not
dividing the ideal (w). Then

\[
 \log_Z NL\le p-R-E+R_0.                              \tag{3}
\]

Indeed every prime of e divides w. Every prime of r outside r0 has positive
exponent in F and also divides w. The two groups are disjoint. All other
first primes lie in `(S/(r e))*r0`; primes in this latter product that happen
to divide G,V,h only make L smaller. This proves (3) without falsely calling
the canceled first primes divisors of w.

At fixed w and L, every first common prime lies in `rad(w)L`. Every second
common prime divides G and hence w, because both its multiplicities in D2,E2
are positive. The projector s divides this second radical. Thus all the
prime supports of C,D,e,D2,E2,V,s are contained in `rad(w)L`.

Assume every displayed ideal label has norm at most Z^T for a fixed T,
and Nw*NL<=Z^B for fixed B. There are only a fixed number of these ideal
labels. Apply (1) with a sufficiently small share of epsilon to each of
them. Their total number at fixed w,L is `O(Z^epsilon)`. This also pays
the fixed local partitions and slot allocations by the last observation
of Section 2. Once these labels have been chosen, h is determined by (2),
up to the bounded unit convention; it is not counted again. In particular,
the first projector has no separate `Z^(log_Z Ns)` factor.

This is a proof for arbitrary ideal norms and valuations under the stated
factorization and allocation assumptions. It is stronger than checking a
finite box of valuations. It does not yet establish those assumptions for
the full Fourier-separated physical source.

## 4. Combining reconstruction with density

Assume that the allowed rows w belong to a single set D with

\[
 \#\{w\in D:Nw\le H\}\ll H^{\rho+\eta}(1+T_h)^J
 \quad\text{for every }H\ge1,                         \tag{4}
\]

uniformly over the fixed finite ray-character family, with rho in a fixed
bounded interval. The set D must be chosen independently of the live common
labels. Polynomial-size masks may vary only after proving that their Euler
deletions preserve the primitive zero conditions used to define D.

For W,Lambda>=0 bounded above by fixed constants, tuples satisfying
`Nw <= Z^W` and `NL <= Z^Lambda` therefore number at most

\[
 O\bigl(Z^{\rho W+\Lambda+\epsilon}(1+T_h)^J\bigr).    \tag{5}
\]

The count of integral ideals of norm at most X in this fixed imaginary
quadratic ring is O(X) for X>=1: choose generators in the fixed lattice,
count points in the disk of radius sqrt(X), and divide by the six units.
Use this with X=Z^Lambda, apply (4) to w, then apply Section 3 to each
pair (w,L). Choose eta sufficiently small relative to the upper bound for W
and the desired total epsilon. All bounds then have constants independent
of the live labels. Bounded windows are included in (4); an eventual density
statement alone is insufficient without the uniform completion already
proved by `UniformDensity`.

For a supported row with `Nw <= Z^(W+omega)` and small omega>=0, a negative
W causes no difficulty provided the row set is nonempty: necessarily
W+omega>=0. Apply (4) at W+omega and charge the extra rho*omega to the
reserved support loss. If W+omega<0, there is no nonzero integral row.

Taking `Lambda = p-R-E+R0` gives exactly the missing-label exponent used by
the manual high-row calculation. This establishes the abstract arithmetic
population estimate. It still depends on the actual source supplying (2),
the uniform character dictionary, the full projector allocation, and (4).

## 5. What the new compiled component closes

`ActualUnmarkedInputs.lean` now proves:

1. The incumbent inverse raw profile estimates with one constant for a fixed
   finite family of `RowData`, uniform in scale, orientation, and frequencies.
   An inverse moment is no longer a postulated input to that result.
2. Construction of `UnmarkedMoments` from those inverse estimates and the
   remaining plain unmarked field.
3. Construction of a nonempty supported batch from actual buffered zero
   maxima, retaining nonprincipal, modulus, row-norm, and coefficient conditions.
4. Absorption of both dyadic counts and the fixed label cardinality at an
   arbitrarily small power cost.

The inverse estimate comes from `ProbeDetectorInverseRawField.fixed_raw_profiles`;
the witness construction comes from `actual_supported_witness_family`;
the dyadic bound comes from `dyadic_cost_eventually`. These are genuine upstream
analytic inputs with their original hypotheses, not new assumptions disguised
as conclusions.

## 6. The remaining analytic obstruction

The upstream plain-moment adapter `source_batch_plain_unmarked` is specialized
to the original **marked** batch, its source dictionary, large-row restriction,
and initial-state admission. Its use of an empty selected product does not
make its batch hypotheses disappear. Our `UnmarkedBatch` deliberately has no
positive prime-slot-supply assumption, so that adapter cannot simply be applied
by setting the slots empty.

A valid next proof must generalize the actual zero-slot source/eligibility
adapter to our unmarked family, deal with the small-core rows uniformly, and
then instantiate its zero-slot moment. It must also prove (2) for the actual
signed twists with both sets of Euler holes retained. Finally the complete
norm/Fourier/height assembly remains necessary. None of (1)–(5), the witness
constructor, or the exact endpoint certificate supplies those missing steps.

Accordingly the full local moment and the all-family endpoint remain open.
