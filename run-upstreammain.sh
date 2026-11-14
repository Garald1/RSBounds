   ( time lake build RSBounds.Moebius003.UpstreamMain TernaryGoldbachChallenge ) > build-upstreammain.log 2>&1 || exit 1
   cat > ax-upstreammain.lean <<'LEAN'
   import RSBounds.Moebius003.UpstreamMain
   #print axioms TernaryGoldbach.RSBounds.Moebius003.ternary_goldbach_of_two_hypotheses
   #print axioms TernaryGoldbach.RSBounds.Moebius003.ternary_goldbach_large_of_plattGRH
   LEAN
   lake env lean ax-upstreammain.lean > axioms-upstreammain.log 2>&1 || exit 1
   ( time lake comparator --config comparator-ternary-goldbach.json ) > comparator-ternary-goldbach.log 2>&1
