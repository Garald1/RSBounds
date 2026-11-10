// Check (m): |m(n)| log(n+1) <= 0.03 for 11815 <= n <= 6e5, m(n) = sum_{k<=n} mu(k)/k.
// m(n) kept as directed-rounded fixed point (scale 10^30, __int128); log in long double.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

int main(void) {
  const int N = 600000;
  int8_t *mu = malloc(N + 1); int *rem = malloc(sizeof(int) * (N + 1));
  for (int i = 0; i <= N; i++) { mu[i] = 1; rem[i] = i; }
  for (int p = 2; p <= N; p++) if (rem[p] == p) { // p prime (never divided)
    for (int m = p; m <= N; m += p) { mu[m] = -mu[m]; rem[m] /= p; }
    if ((long long)p * p <= N) for (int m = p * p; m <= N; m += p * p) mu[m] = 0;
  }
  // rem[p]==p test: rem only modified by smaller primes, so rem[p]==p iff p prime. ok.
  __int128 S = 1; for (int i = 0; i < 30; i++) S *= 10;
  __int128 lo = 0, hi = 0;
  long double worst = 0; int worstn = 0; int viol = 0;
  long double minmarg = 1;
  for (int k = 1; k <= N; k++) {
    if (mu[k] == 1) { lo += S / k; hi += (S + k - 1) / k; }
    else if (mu[k] == -1) { lo -= (S + k - 1) / k; hi -= S / k; }
    if (k >= 11815) {
      long double a = fabsl((long double)lo), b = fabsl((long double)hi);
      long double mx = (a > b ? a : b) / (long double)S;
      long double v = mx * logl((long double)k + 1);
      if (v > worst) { worst = v; worstn = k; }
      if (v > 0.03L) { viol++; if (viol < 10) printf("VIOLATION n=%d v=%.9Lf\n", k, v); }
    }
  }
  printf("max |m(n)| log(n+1) over [11815,6e5] = %.9Lf at n=%d; violations=%d\n", worst, worstn, viol);
  // print a few values near the worst and the start
  return viol != 0;
}
