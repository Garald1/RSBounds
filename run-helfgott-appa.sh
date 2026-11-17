#!/bin/bash
# Laptop run for HelfgottAppA: build, axiom check, Comparator. Progress in helfgott-appa-status.txt.
cd "$(dirname "$0")"
echo "RUNNING: build started $(date)" > helfgott-appa-status.txt
if ! lake build RSBounds.HelfgottAppA.EBound HelfgottAppAChallenge HelfgottAppASolution > build-helfgott-appa.log 2>&1; then
  echo "STOPPED: the build did not complete, see build-helfgott-appa.log" > helfgott-appa-status.txt; exit 1
fi
cat > ax-appa.lean <<'LEAN'
import RSBounds.HelfgottAppA.EBound
#print axioms RSBounds.HelfgottAppA.abs_etaPlus_le_1079955
#print axioms RSBounds.HelfgottAppA.mul_abs_etaPlus_le_119073
#print axioms RSBounds.HelfgottAppA.nonprime_input_book
#print axioms RSBounds.HelfgottAppA.E_le_book_formula
#print axioms RSBounds.HelfgottAppA.E_le_14_28_book
LEAN
lake env lean ax-appa.lean > axioms-appa.log 2>&1
if [ "$(tr -d ' \n' < axioms-appa.log | grep -o 'dependsonaxioms:\[propext,Classical.choice,Quot.sound\]' | wc -l)" -ne 5 ]; then
  echo "STOPPED: unexpected axioms, see axioms-appa.log" > helfgott-appa-status.txt; exit 1
fi
echo "RUNNING: build and axioms OK; Comparator started $(date)" > helfgott-appa-status.txt
( time lake comparator --config comparator-helfgott-appa.json ) > comparator-helfgott-appa.log 2>&1
echo "FINISHED $(date): $(tail -5 comparator-helfgott-appa.log | tr '\n' ' ')" > helfgott-appa-status.txt
