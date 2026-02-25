# Leonardo's Prime Factors

A solution to the [Leonardo's Prime Factors](https://www.hackerrank.com/challenges/leonardo-and-prime) HackerRank problem, with a formal correctness proof in Rocq (formerly Coq).

This repository was a personal learning exercise in bridging competitive programming with formal verification.

---

## The Problem

Given an integer $n$, find the **maximum number of distinct prime factors** that any integer in $[1, n]$ can have.

**Example:**
```
n = 30   →   answer is 3
```
Because $30 = 2 \times 3 \times 5$ has 3 distinct prime factors, and no integer $\leq 30$ has 4 (the smallest with 4 would be $2 \times 3 \times 5 \times 7 = 210 > 30$).

---

## Key Insight

The smallest optimal integer is always a **primorial** — the product of the first $k$ distinct primes:

$$2,\quad 2 \cdot 3,\quad 2 \cdot 3 \cdot 5,\quad 2 \cdot 3 \cdot 5 \cdot 7,\quad \ldots$$

Any other selection of only $k$ distinct primes produces a strictly larger product (by the minimality of the smallest primes), so the $k$-th primorial is the *tightest* witness. If it exceeds $n$, no integer in $[1, n]$ can have $k$ distinct prime factors.

The algorithm therefore just multiplies primes greedily until the running product would exceed $n$, and counts how many fit.

---

## Repository Structure

```
.
├── README.md
├── cpp/
│   └── solution.cpp          # C++ solution (HackerRank submission)
└── rocq/
    └── PrimeFactors.v         # Rocq formalization and correctness proof
```

---

## C++ Solution (`cpp/solution.cpp`)

### How it works

The `TrialDivision` namespace exposes one function:

```cpp
int TrialDivision::primeCount(long long n)
```

It generates primes in ascending order using trial division, multiplying them into a running product. At each step it checks whether including the next prime $p$ would push the product over $n$, using the overflow-safe comparison:

```cpp
if (product > (ull)n / p) return count;
```

This is equivalent to `product * p > n` but avoids unsigned overflow by dividing instead.

### Build and run

```bash
g++ -O2 -std=c++17 -o solution cpp/solution.cpp
echo "2
10
30" | ./solution
# Output:
# 2
# 3
```

Input format: first line is $t$ (number of test cases), then $t$ lines each containing $n$.

---

## Rocq Formalization (`rocq/PrimeFactors.v`)

### Requirements

- [Rocq](https://rocq-prover.org/) (formerly Coq) ≥ 8.18, or a recent Coq installation

### Check the proof

```bash
coqc rocq/PrimeFactors.v
```

A clean run with no output means all proofs are accepted.

### Proof structure

The file is organized in layers, each building on the last:

| Section | Contents |
|---|---|
| Basic Definitions | `prime`, `divides`, `product`, `all_primes` |
| Fundamental Theorem of Arithmetic | Axiomatised (existence + uniqueness up to permutation) |
| Largest Divisor | `largest_divisor` via downward trial division; maximality proof |
| Prime Factorisation | `primefactors` via `Program Fixpoint`; correctness + sorted order |
| Deduplication | `dedup` on sorted lists; NoDup + sorted preservation |
| Distinct Prime Factors | `distinct_primefactors = dedup ∘ primefactors` |
| Primality Test | `is_prime` boolean function; reflection lemma `is_prime_correct` |
| Max Distinct Aux | `max_distinct_aux` with fuel for termination |
| **Soundness** | `max_distinct_sound`: the answer is achieved by some $m \leq n$ |
| **Maximality** | `max_distinct_maximal`: no $m \leq n$ can do better |

### The two main theorems

**Soundness** — the answer is achievable:
```coq
Theorem max_distinct_sound :
  forall n, 1 <= n ->
    exists m, m <= n /\
      length (distinct_primefactors m) = max_distinct_prime_factors n.
```
*Witness:* the primorial accumulated inside `max_distinct_aux`.

**Maximality** — nothing does better:
```coq
Theorem max_distinct_maximal :
  forall n m,
    m <= n ->
    length (distinct_primefactors m) <= max_distinct_prime_factors n.
```
*Proof sketch:* any $m$ with $k$ distinct prime factors $p_1, \ldots, p_k$ satisfies $p_1 \cdots p_k \mid m$, so $p_1 \cdots p_k \leq m \leq n$. The smallest possible $p_1 \cdots p_k$ is the $k$-th primorial (using the first $k$ primes). If `max_distinct_aux` stopped before reaching $k$, that primorial exceeded $n$ — contradiction.

The coprimality argument (`nodup_primes_product_divides`) is the technical core: distinct primes are pairwise coprime, so their product divides any number they individually divide, via repeated application of Gauss's lemma.

### Note on FTA

The Fundamental Theorem of Arithmetic is **axiomatised** rather than proved. Proving it from scratch in Rocq is substantial work and orthogonal to the problem. The two axioms used are:

- `FTA_existence`: every $n > 1$ has a prime factorisation.
- `FTA_uniqueness`: the factorisation is unique up to permutation.

`FTA_uniqueness` is used only in `primefactors_product_id` to identify two sorted factor lists. `FTA_existence` is used to establish that composite numbers have a largest proper divisor $\geq 2$.

---

## Correspondence Between C++ and Rocq

| C++ | Rocq |
|---|---|
| `TrialDivision::primeCount` | `max_distinct_prime_factors` / `max_distinct_aux` |
| `TrialDivision::nextPrime` | `is_prime` / `has_divisor` (primality test inside `max_distinct_aux`) |
| `product > n / p` | `product * candidate <=? n` (same check, opposite sense) |
| Greedy primorial loop | `max_distinct_aux_counts_ge` (the inductive step of maximality) |
| Loop termination (implicit) | `fuel` parameter decremented each step |
| Stateless per-call execution | Pure functional style; no mutable state |

The C++ version calls `nextPrime` to generate primes lazily, while the Rocq version tests each candidate `2, 3, 4, ...` directly with `is_prime`, skipping composites. These are computationally equivalent.

---

## Notes on the C++ Design

The original implementation used a global mutable vector with `-1` sentinels to mark composites (a rough sieve-style structure). The version here refactors this into a stateless `nextPrime` helper, which:

- eliminates the `reset` flag workaround for resetting global state between calls,
- makes the intent clearer (generate the next prime, given the ones already found),
- matches more closely the structure reasoned about in the Rocq proof.

The algorithm is still **trial division**, not a true Sieve of Eratosthenes. For this problem only $\sim$15 primes are ever needed (since $2 \cdot 3 \cdot 5 \cdots 47 < 10^{18}$), so the distinction is irrelevant in practice.
