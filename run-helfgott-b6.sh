#!/bin/bash
# Laptop run for HelfgottB6: build, axiom check, Comparator. Progress in helfgott-b6-status.txt.
cd "$(dirname "$0")"
echo "RUNNING: build started $(date)" > helfgott-b6-status.txt
if ! lake build RSBounds.HelfgottB6.Main HelfgottB6Challenge HelfgottB6Solution > build-helfgott-b6.log 2>&1; then
  echo "STOPPED: the build did not complete, see build-helfgott-b6.log" > helfgott-b6-status.txt; exit 1
fi
cat > ax-b6.lean <<'LEAN'
import RSBounds.HelfgottB6.Main
#print axioms RSBounds.HelfgottB6.norm_eta2DD_le_31521
#print axioms RSBounds.HelfgottB6.eta2_fourier_bound_31521
LEAN
lake env lean ax-b6.lean > axioms-b6.log 2>&1
if [ "$(tr -d ' \n' < axioms-b6.log | grep -o 'dependsonaxioms:\[propext,Classical.choice,Quot.sound\]' | wc -l)" -ne 2 ]; then
  echo "STOPPED: unexpected axioms, see axioms-b6.log" > helfgott-b6-status.txt; exit 1
fi
echo "RUNNING: build and axioms OK; Comparator started $(date)" > helfgott-b6-status.txt
( time lake comparator --config comparator-helfgott-b6.json ) > comparator-helfgott-b6.log 2>&1
echo "FINISHED $(date): $(tail -5 comparator-helfgott-b6.log | tr '\n' ' ')" > helfgott-b6-status.txt
