#!/bin/bash
cd "$(dirname "$0")"
echo "RUNNING: Comparator started $(date)" > item7-status.txt
( time lake comparator --config comparator-helfgott-psi-book.json ) > comparator-helfgott-psi-book.log 2>&1
echo "FINISHED $(date): $(tail -5 comparator-helfgott-psi-book.log | tr '\n' ' ')" > item7-status.txt
