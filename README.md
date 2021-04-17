# A formalized proof of the Erdős–Szekeres theorem
This is a proof of the [Erdős–Szekeres theorem][wiki:es] formalized in [Lean][wiki:lean], an [interactive theorem prover][wiki:proof]. The theorem says that

> Any sequence of real numbers with length at least (r − 1)(s − 1) + 1 contains a monotonically increasing subsequence of length r or a monotonically decreasing subsequence of length s.

The corresponding statement in Lean is

```lean
theorem erdos_szekeres
{X : Type*} [linear_order X]
(A : list X)
(r s : ℕ)
(h : (r-1)*(s-1) < A.length)
: (∃ (R : list X), R <+ A ∧ R.length = r ∧ R.pairwise (≤))
∨ (∃ (S : list X), S <+ A ∧ S.length = s ∧ S.pairwise (≥))
```

Note that the theorem has been generalized to any [linear order][wiki:total], not just the real numbers.

There is also another version stated using an ordered `finset` instead of `list`.
```lean
theorem erdos_szekeres''
{X Y: Type*} [linear_order X] [linear_order Y]
(r s : ℕ)
(A : finset X)
(h : (r-1)*(s-1) < A.card)
(f : X → Y)
: (∃ R ⊆ A, R.card = r ∧ ∀ (x ∈ R) (y ∈ R), x ≤ y → f x ≤ f y)
∨ (∃ S ⊆ A, S.card = s ∧ ∀ (x ∈ S) (y ∈ S), x ≤ y → f y ≤ f x)
```

The [axiom of choice][wiki:ac] has not been avoided.

[wiki:es]:    https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Szekeres_theorem
[wiki:lean]:  https://en.wikipedia.org/wiki/Lean_(proof_assistant)
[wiki:proof]: https://en.wikipedia.org/wiki/Proof_assistant
[wiki:total]: https://en.wikipedia.org/wiki/Total_order
[wiki:ac]:    https://en.wikipedia.org/wiki/Axiom_of_choice