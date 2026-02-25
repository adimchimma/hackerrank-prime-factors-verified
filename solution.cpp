// Leonardo's Prime Factors — HackerRank
//
// Problem: given n, find the maximum number of distinct prime factors
// any integer in [1, n] can have.
//
// Key insight: the optimal integer is always a primorial — the product
// of the first k distinct primes 2 * 3 * 5 * 7 * ... * p_k.
// Any other arrangement of k distinct primes produces a larger product,
// so if the k-th primorial exceeds n, no integer in [1, n] can have
// k distinct prime factors.
//
// Strategy: generate primes in order via trial division, accumulate
// their product, and count how many fit before the product exceeds n.

#include <iostream>
#include <vector>

using ull = unsigned long long;

namespace TrialDivision {

    // Returns the smallest prime strictly greater than `last`.
    // `known_primes` must contain every prime up to sqrt(last + 1)
    // for the trial-division check to be correct; in practice we always
    // call this with the full list of primes found so far, which satisfies
    // that invariant because primes grow slowly enough.
    ull nextPrime(ull last, const std::vector<ull>& known_primes) {
        ull candidate = last + 1;
        while (true) {
            bool is_prime = true;
            for (ull p : known_primes) {
                if (p * p > candidate) break;          // no factor found below sqrt
                if (candidate % p == 0) {
                    is_prime = false;
                    break;
                }
            }
            if (is_prime) return candidate;
            ++candidate;
        }
    }

    // Returns the maximum number of distinct prime factors any integer
    // in [1, n] can have.
    //
    // We greedily multiply the smallest primes together.  At each step we
    // check whether including the next prime p would push the running
    // product above n.  The check is written as
    //
    //     product > n / p          (integer division)
    //
    // rather than  product * p > n  to avoid unsigned overflow.
    int primeCount(long long n) {
        if (n < 2) return 0;

        std::vector<ull> primes;   // primes found so far, in ascending order
        ull product = 1;
        int count   = 0;
        ull last    = 1;           // largest prime generated so far (seed value)

        while (true) {
            ull p = nextPrime(last, primes);

            // Overflow-safe: would product * p exceed n?
            if (product > static_cast<ull>(n) / p) return count;

            product *= p;
            count++;
            primes.push_back(p);
            last = p;
        }
    }

} // namespace TrialDivision

int main() {
    int t;
    std::cin >> t;
    while (t--) {
        long long n;
        std::cin >> n;
        std::cout << TrialDivision::primeCount(n) << "\n";
    }
    return 0;
}