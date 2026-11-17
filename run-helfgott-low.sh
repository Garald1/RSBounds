#!/bin/bash
# Laptop run for HelfgottLow: build, axiom check, Comparator. Progress in helfgott-low-status.txt.
cd "$(dirname "$0")"
echo "RUNNING: build started $(date)" > helfgott-low-status.txt
if ! lake build RSBounds.HelfgottLowBook HelfgottLowChallenge HelfgottLowSolution > build-helfgott-low.log 2>&1; then
  echo "STOPPED: the build did not complete, see build-helfgott-low.log" > helfgott-low-status.txt; exit 1
fi
cat > ax-low.lean <<'LEAN'
import RSBounds.HelfgottLowBook
#print axioms TernaryGoldbach.RSBounds.HelfgottLowBook.sum_vonMangoldt_mul_lt_a16
#print axioms TernaryGoldbach.RSBounds.HelfgottLowBook.sum_vonMangoldt_div_sqrt_lt_a18
#print axioms RSBounds.HelfgottLow.sum_vonMangoldt_mul_lt_a16_small
#print axioms RSBounds.HelfgottLow.sum_vonMangoldt_mul_lt_a16_of
#print axioms RSBounds.HelfgottLow.sum_vonMangoldt_div_sqrt_lt_small
#print axioms RSBounds.HelfgottLow.sum_vonMangoldt_div_sqrt_lt_of
#print axioms RSBounds.HelfgottLow.sum_log_sq_primes_le_small
#print axioms RSBounds.HelfgottLow.sum_log_sq_primes_le_of
LEAN
lake env lean ax-low.lean > axioms-low.log 2>&1
if [ "$(tr -d ' \n' < axioms-low.log | grep -o 'dependsonaxioms:\[propext,Classical.choice,Quot.sound\]' | wc -l)" -ne 8 ]; then
  echo "STOPPED: unexpected axioms, see axioms-low.log" > helfgott-low-status.txt; exit 1
fi
echo "RUNNING: build and axioms OK; Comparator started $(date)" > helfgott-low-status.txt
( time lake comparator --config comparator-helfgott-low.json ) > comparator-helfgott-low.log 2>&1
echo "FINISHED $(date): $(tail -5 comparator-helfgott-low.log | tr '\n' ' ')" > helfgott-low-status.txt
