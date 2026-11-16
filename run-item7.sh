#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "lake build RSBounds.HelfgottPsiBoundsBook" > /dev/null; do sleep 60; done
if ! lake build --no-build RSBounds.HelfgottPsiBoundsBook HelfgottPsiBookChallenge HelfgottPsiBookSolution > /dev/null 2>&1; then
  echo "STOPPED: the build did not complete" > item7-status.txt; exit 1
fi
printf 'import RSBounds.HelfgottPsiBoundsBook\n#print axioms TernaryGoldbach.RSBounds.HelfgottPsiBoundsBook.psi_le_10004\n#print axioms TernaryGoldbach.RSBounds.HelfgottPsiBoundsBook.sum_vonMangoldt_le_a14\n#print axioms TernaryGoldbach.RSBounds.HelfgottPsiBoundsBook.sum_vonMangoldt_mul_lt_a17\n' > ax-book.lean
lake env lean ax-book.lean > axioms-book.log 2>&1
if [ "$(grep -c 'depends on axioms' axioms-book.log)" -ne 3 ] || [ "$(grep -c '\[propext, Classical.choice, Quot.sound\]' axioms-book.log)" -ne 3 ]; then
  echo "STOPPED: unexpected axioms, see axioms-book.log" > item7-status.txt; exit 1
fi
echo "RUNNING: Comparator started $(date)" > item7-status.txt
( time lake comparator --config comparator-helfgott-psi-book.json ) > comparator-helfgott-psi-book.log 2>&1
echo "FINISHED $(date): $(tail -5 comparator-helfgott-psi-book.log | tr '\n' ' ')" > item7-status.txt
