// Print M(n) for each n listed (sorted ascending) in the input file. Segmented sieve of mu.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); int64_t *q = malloc(sizeof(int64_t) * 100000); int nq = 0;
  while (fscanf(f, "%lld", (long long *)&q[nq]) == 1) nq++;
  int64_t N = q[nq - 1]; int64_t R = (int64_t)sqrt((double)N) + 2;
  char *isc = calloc(R + 1, 1); int64_t *pr = malloc(sizeof(int64_t) * (R + 1)); int np = 0;
  for (int64_t i = 2; i <= R; i++) if (!isc[i]) { pr[np++] = i; for (int64_t j = i * i; j <= R; j += i) isc[j] = 1; }
  const int64_t SEG = 1 << 20; int64_t *rem = malloc(sizeof(int64_t) * SEG); int8_t *mu = malloc(SEG);
  int64_t M = 0; int k = 0;
  while (k < nq && q[k] == 0) { printf("0 0\n"); k++; }
  for (int64_t lo = 1; lo <= N; lo += SEG) {
    int64_t hi = lo + SEG - 1; if (hi > N) hi = N; int64_t len = hi - lo + 1;
    for (int64_t i = 0; i < len; i++) { rem[i] = lo + i; mu[i] = 1; }
    for (int j = 0; j < np; j++) { int64_t p = pr[j]; if (p * p > hi) break;
      int64_t s = ((lo + p - 1) / p) * p; for (int64_t m = s; m <= hi; m += p) { rem[m - lo] /= p; mu[m - lo] = -mu[m - lo]; }
      int64_t p2 = p * p; s = ((lo + p2 - 1) / p2) * p2; for (int64_t m = s; m <= hi; m += p2) mu[m - lo] = 0; }
    for (int64_t i = 0; i < len; i++) { int m = mu[i]; if (m && rem[i] > 1) m = -m; M += m;
      while (k < nq && q[k] == lo + i) { printf("%lld %lld\n", (long long)q[k], (long long)M); k++; } }
  }
  return 0;
}
