# IBNFS — Index-Based Number Field Sieve (PARI/GP Proof of Concept)

A self-contained PARI/GP proof-of-concept implementation of a blind, one-sided **Index-Based Number Field Sieve (IBNFS)** for factoring composite integers dividing the discriminant or index of a monic irreducible polynomial $f \in \mathbb{Z}[x]$.

## Overview

`factorindex(f, B, n, n_deps)` operates strictly on the user-supplied defining polynomial $f$ without calling `polredbest`, `bnfinit`, or factoring `poldisc(f)` globally:

- **Local bad primes only:** Uses `nfinit([f, P_bad])` restricted to primes $\ell \le B$ dividing $\mathrm{disc}(f)$ (and not $n$).
- **One-sided expanding-shell line sieve:** Collects $B$-smooth relations $(a, b)$ over $b^d f(a/b)$ alongside free relations for completely split primes.
- **Pruned $\mathbb{F}_2$ linear algebra:** Performs iterative singleton pruning on the factor base, appends real sign embeddings and 32 quadratic characters, and extracts the sparsest kernel dependencies.
- **Blind Hensel square root:** Recovers exact algebraic square roots $w(v) = \pm f'(v)\sqrt{\prod (a_i - b_i v)} \in \mathbb{Z}[v]$ via inert-prime Newton lifting (`blind_sqrt_hensel`) over $\mathbb{F}_q[v]/(f)$ lifted modulo $q^K$.
- **Factor extraction:** Extracts factors of $n$ from the power-basis denominator $D(\gamma)$ (and from $w(m), w'(m) \bmod n$ when a double root $m \bmod n$ exists). Any incidental GCDs encountered during setup or sieving are reported separately and excluded from the NFS factor count.

## Requirements

- **PARI/GP** (2.15+ recommended).
- Because the linear algebra and square-root stages can allocate significant memory for larger smoothness bounds $B$, set a generous maximum stack size before running (e.g., `default(parisizemax, 2G)`).

## Usage

Load the script in a `gp` session:

```gp
\r indexfactor.gp
```

### Main Function

```gp
factorindex(f, B, n = 0, n_deps = 20)
```

| Parameter | Description |
| :--- | :--- |
| `f` | Monic irreducible polynomial in $\mathbb{Z}[x]$. |
| `B` | Smoothness bound for the factor base. |
| `n` | Target composite dividing $\mathrm{disc}(f)$ (defaults to $\lvert \mathrm{disc}(f) \rvert$). |
| `n_deps` | Number of sparsest $\mathbb{F}_2$ kernel dependencies to test (default `20`). |

**Returns:** `[fmat, top10, stats]`, where:
- `fmat` is the matrix of recovered factors and exponents.
- `top10` lists the first 10 full relations `[a, b, fa]`.
- `stats` is `[B, n_fb, R, R_f, n_sieved, #free_rels, n_ker, max_test, n_sq, n_splits, t_sieve, t_tot]`.

### Polynomial Selection Helpers

| Function | Purpose |
| :--- | :--- |
| `make_16_9_bal(d, B0)` | Generates a balanced test instance `[f, n, p, q]` with $n = p^2 q$ and $p \approx q \approx n^{1/3}$. |
| `getindexpolyflat(d, B, aut=1, exact_ok=0)` | Generates a flat-coefficient monic polynomial `[f, n]` with coefficients bounded by `B` and nontrivial index $n$. |
| `make_16_9_lll(p, d, s=1)` | Generates an LLL-reduced monic polynomial `[f, n, p, n/p^2]` with $p \mid I(f)$. |
| `getindexpolyf(n, m, d, s=1)` | LLL + Babai construction of a monic degree-$d$ polynomial with index divisible by $n$. |
| `getdiscpolyf(n, m, d, s=1)` | LLL construction of a degree-$d$ polynomial with discriminant divisible by $n$. |
| `getmonicdiscpoly(n, m, d, s=1, bound=0)` | Monic degree-$d$ polynomial with discriminant divisible by $n$ via LLL + CVP (`qfcvp`). |

## Examples

### Example 1: Balanced Discriminant Instance (`make_16_9_bal`)

Generate a degree-5 balanced instance with $n = p^2 q$ (both $p, q$ pseudoprime) and factor $n$ with $B = 10000$:

```gp
? while(1,[f,n,p,q]=make_16_9_bal(5, 3);if(ispseudoprime(p)&&ispseudoprime(q),break;););
? n
%234 = 12622654865350114256254619679893
? f
%235 = x^5 - 22*x^4 - 1040*x^3 + 37373*x^2 - 300317*x + 4946314
? factorindex(f,10000,n);
[setup] deg=5, r1=1 | B=10000, #FB=1229, bad=0, free=14, qc=32, need=1273 (0.89s)
[sieve] shell 1 (A=5833, B=268) b=11/268 | rels=536/1273 | tested=793 | 1.5s
[sieve] shell 1 (A=5833, B=268) b=22/268 | rels=849/1273 | tested=1240 | 3.0s
[sieve] shell 1 (A=5833, B=268) b=33/268 | rels=1106/1273 | tested=1606 | 4.5s
[sieve] shell 1 done (A=5833, B=268) | rels=1273/1273 | tested=1864 | 5.86s
  *** _*_: Warning: increasing stack size to 16000000.
  *** _*_: Warning: increasing stack size to 32000000.
  *** _*_: Warning: increasing stack size to 64000000.
[linalg] pruned 1262x1287 -> 779x963 F_2 matrix -> ker_dim=215 (0.21s)
[sqrt] tested 20 deps -> 20/20 squares, 11/20 split n (55.0%) (14.71s)

Factors of n = 12622654865350114256254619679893 (total 21.68s):
  5233425103^2 * 460870257077

First 10 full relations:
  [ 1] (a, b) = (    -39,    1) | N = -19 * 109 * 2861
  [ 2] (a, b) = (  -5555,    1) | N = -37 * 43 * 103 * 673 * 2081 * 3061 * 7559
  [ 3] (a, b) = (  -4104,    1) | N = -2 * 47 * 79 * 97 * 431 * 607 * 857 * 7247
  [ 4] (a, b) = (  -3594,    1) | N = -2^9 * 29 * 37 * 41 * 617 * 4649 * 9337
  [ 5] (a, b) = (  -2764,    1) | N = -2 * 13 * 29 * 109 * 389 * 601 * 1013 * 8353
  [ 6] (a, b) = (  -2602,    1) | N = -2^5 * 79 * 1213 * 1297 * 3803 * 7951
  [ 7] (a, b) = (  -1802,    1) | N = -2^8 * 13^2 * 61 * 643 * 2897 * 3911
  [ 8] (a, b) = (  -1518,    1) | N = -2^2 * 13 * 53^3 * 431 * 773 * 3169
  [ 9] (a, b) = (  -1485,    1) | N = -7 * 37 * 97 * 181 * 409 * 947 * 4159
  [10] (a, b) = (  -1204,    1) | N = -2 * 13 * 1471 * 1553 * 5023 * 8629
```

### Example 2: Flat-Coefficient Index Polynomial (`getindexpolyflat`)

Generate a degree-5 flat-coefficient polynomial whose index $n$ is a semiprime with both prime factors $> 10^9$, and factor $n$ with $B = 40000$:

```gp
? while(1,[f,n]=getindexpolyflat(5,10^6,1);ff=factor(abs(n));if(#ff[,1]==2&&ff[1,1]>1000000000,break;););
? f
%265 = x^5 - 329589*x^4 + 339649*x^3 - 950713*x^2 + 412549*x - 130063
? n
%266 = 1251293455319733535793
? factorindex(f,40000,n);
[setup] deg=5, r1=1 | B=40000, #FB=4173, bad=2, free=31, qc=32, need=4200 (2.94s)
[sieve] shell 1 (A=5000, B=5000) b=13/5000 | rels=255/4200 | tested=367 | 1.6s
[sieve] shell 1 (A=5000, B=5000) b=26/5000 | rels=400/4200 | tested=558 | 3.2s
[sieve] shell 1 (A=5000, B=5000) b=39/5000 | rels=529/4200 | tested=718 | 4.7s
[sieve] shell 1 (A=5000, B=5000) b=52/5000 | rels=637/4200 | tested=851 | 6.3s
[sieve] shell 1 (A=5000, B=5000) b=65/5000 | rels=727/4200 | tested=962 | 7.9s
[sieve] shell 1 (A=5000, B=5000) b=78/5000 | rels=805/4200 | tested=1054 | 9.4s
[sieve] shell 1 (A=5000, B=5000) b=91/5000 | rels=888/4200 | tested=1151 | 11.0s
...
[sieve] shell 1 (A=5000, B=5000) b=1196/5000 | rels=4119/4200 | tested=4479 | 144.5s
[sieve] shell 1 (A=5000, B=5000) b=1209/5000 | rels=4146/4200 | tested=4506 | 146.1s
[sieve] shell 1 (A=5000, B=5000) b=1222/5000 | rels=4162/4200 | tested=4522 | 147.7s
[sieve] shell 1 (A=5000, B=5000) b=1235/5000 | rels=4180/4200 | tested=4540 | 149.3s
[sieve] shell 1 (A=5000, B=5000) b=1248/5000 | rels=4199/4200 | tested=4559 | 150.8s
[sieve] shell 1 done (A=5000, B=5000) | rels=4200/4200 | tested=4560 | 150.91s
  *** matrix: Warning: increasing stack size to 16000000.
  *** matrix: Warning: increasing stack size to 32000000.
  *** matrix: Warning: increasing stack size to 64000000.
  *** matrix: Warning: increasing stack size to 128000000.
  *** _*_: Warning: increasing stack size to 256000000.
  *** _*_: Warning: increasing stack size to 512000000.
  *** _*_: Warning: increasing stack size to 1024000000.
[linalg] pruned 4206x4231 -> 2713x3196 F_2 matrix -> ker_dim=515 (1.59s)
[sqrt] tested 20 deps -> 20/20 squares, 10/20 split n (50.0%) (69.99s)

Factors of n = 1251293455319733535793 (total 225.43s):
  4218328861 * 296632504613

First 10 full relations:
  [ 1] (a, b) = (  -4340,    1) | N = -19 * 97 * 293 * 617 * 1567 * 9419 * 24097
  [ 2] (a, b) = (  -4181,    1) | N = -2^6 * 43 * 47 * 113 * 137 * 313 * 8329 * 19543
  [ 3] (a, b) = (  -2869,    1) | N = -2^5 * 367 * 1381 * 2887 * 15401 * 31247
  [ 4] (a, b) = (  -2513,    1) | N = -2^2 * 283 * 4211 * 6389 * 15733 * 27653
  [ 5] (a, b) = (  -2301,    1) | N = -2^3 * 47^2 * 167 * 7529 * 10799 * 38791
  [ 6] (a, b) = (  -1633,    1) | N = -2^2 * 137 * 167 * 941 * 1109 * 1783 * 13841
  [ 7] (a, b) = (  -1626,    1) | N = -29 * 127 * 691 * 6803 * 9043 * 14797
  [ 8] (a, b) = (  -1595,    1) | N = -2 * 59 * 193 * 269 * 751 * 14537 * 32069
  [ 9] (a, b) = (  -1091,    1) | N = -2 * 19 * 43 * 61 * 10891 * 16381 * 26371
  [10] (a, b) = (   -471,    1) | N = -2 * 47 * 443 * 2659 * 6301 * 23333
```

## Notes

- `blind_sqrt_hensel` searches for an inert prime $q$ modulo which $f$ is irreducible; polynomials whose Galois group contains no $d$-cycle will trigger an error in this proof of concept.
- This is research/proof-of-concept code intended to demonstrate the algorithm rather than compete with production C/C++ NFS implementations.
