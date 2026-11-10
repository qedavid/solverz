#!/bin/sh
# Re-elaborate C37's sources and the probe through the env slot, in two lanes.
P=problems/signed-difference-sets
L=problems/signed-difference-sets/lean/SignedDifferenceSets
OUT=$P/R44/lean-out
mkdir -p $OUT
run() { # <relpath> <GB> <tag>
  echo "start $3 $(date +%H:%M:%S)" >> $OUT/progress.log
  sh $P/scratch/lean-slot.sh env refuter "$1" "$2" > $OUT/$3.log 2>&1
  echo "done $3 $(date +%H:%M:%S) exit=$?" >> $OUT/progress.log
}
laneA() {
  run R44/Probe.lean 5 probe
  run $L/PairRows/N464/Lists.lean 5 lists
  run $L/PairRows/N464/Part0.lean 4 part0
  run $L/PairRows/N464/Part1.lean 4 part1
  run $L/PairRows/N464/Part2.lean 4 part2
  run $L/PairRows/N464/Part3.lean 4 part3
  run $L/Doubling.lean 3 doubling
}
laneB() {
  run $L/PairRows/N464/Part4.lean 4 part4
  run $L/PairRows/N464/Part5.lean 4 part5
  run $L/PairRows/N464/Part6.lean 4 part6
  run $L/PairRows/N464.lean 3 main
  run $L/Tests/PairSearch.lean 5 tests
  run $L/PairSearch.lean 3 pairsearch
  run $L/PairCheck.lean 3 paircheck
}
laneA &
laneB &
wait
echo "all done $(date +%H:%M:%S)" >> $OUT/progress.log
