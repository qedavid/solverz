#!/bin/sh
# own verdict and generator (origin, search) on every exists row with a Z_p^r quotient; 120 s cap each
D=problems/signed-difference-sets
cd "$D"
while read id p r; do
  for mode in own origin search; do
    out=$(timeout 120 nice -n 10 python R49/exists_one.py $id $p $r $mode 2>&1 | tail -1)
    [ -z "$out" ] && out="$id $p $r $mode TIMEOUT"
    echo "$id p=$p r=$r | $out"
  done
done < R49/exists_list.txt
