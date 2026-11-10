// Independent floating-point-free check of (M): 10^6 M(n)^2 <= 326041 n for 33 <= n <= 10^9.
// Segmented sieve for mu. Also prints the max of M(n)^2/n and M at every multiple of STEP.
// Usage: mertens_check N STEP boundaries.txt
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

int main(int argc, char **argv) {
  int64_t N = argc > 1 ? atoll(argv[1]) : 1000000000LL;
  int64_t STEP = argc > 2 ? atoll(argv[2]) : 1000000LL;
  FILE *bf = argc > 3 ? fopen(argv[3], "w") : NULL;
  int64_t R = (int64_t)sqrt((double)N) + 2;
  char *isc = calloc(R + 1, 1);
  int64_t *pr = malloc(sizeof(int64_t) * (R + 1));
  int np = 0;
  for (int64_t i = 2; i <= R; i++) if (!isc[i]) { pr[np++] = i; for (int64_t j = i * i; j <= R; j += i) isc[j] = 1; }
  const int64_t SEG = 1 << 20;
  int64_t *rem = malloc(sizeof(int64_t) * SEG);
  int8_t *mu = malloc(SEG);
  int64_t M = 0, worstn = 0; double worst = 0; int64_t viol = 0;
  if (bf) fprintf(bf, "0 0\n");
  for (int64_t lo = 1; lo <= N; lo += SEG) {
    int64_t hi = lo + SEG - 1; if (hi > N) hi = N;
    int64_t len = hi - lo + 1;
    for (int64_t i = 0; i < len; i++) { rem[i] = lo + i; mu[i] = 1; }
    for (int k = 0; k < np; k++) {
      int64_t p = pr[k]; if (p * p > hi) break;
      int64_t s = ((lo + p - 1) / p) * p;
      for (int64_t m = s; m <= hi; m += p) { rem[m - lo] /= p; mu[m - lo] = -mu[m - lo]; }
      int64_t p2 = p * p; s = ((lo + p2 - 1) / p2) * p2;
      for (int64_t m = s; m <= hi; m += p2) mu[m - lo] = 0;
    }
    for (int64_t i = 0; i < len; i++) {
      int64_t n = lo + i;
      int m = mu[i];
      if (m != 0 && rem[i] > 1) m = -m;   // one leftover prime factor > sqrt(hi)
      M += m;
      if (n >= 33) {
        // 10^6 M^2 <= 326041 n ?
        __int128 lhs = (__int128)1000000 * M * M, rhs = (__int128)326041 * n;
        if (lhs > rhs) { if (viol < 20) printf("VIOLATION n=%lld M=%lld\n", (long long)n, (long long)M); viol++; }
        double r = fabs((double)M) / sqrt((double)n);
        if (r > worst) { worst = r; worstn = n; }
      }
      if (bf && n % STEP == 0) fprintf(bf, "%lld %lld\n", (long long)n, (long long)M);
    }
  }
  printf("N=%lld M(N)=%lld max|M|/sqrt n on [33,N] = %.6f at n=%lld; violations=%lld\n",
         (long long)N, (long long)M, worst, (long long)worstn, (long long)viol);
  if (bf) fclose(bf);
  return viol != 0;
}
