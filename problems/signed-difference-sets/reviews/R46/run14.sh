#!/bin/sh
# name group c Q t s1 M   (H' = Z_r x prod ks, mixed radix)
while read name grp c Q t s M; do
  r1=$(./vsearch.exe $grp $c $Q $t $s $M 4000000000 | tr '\n' ' ')
  r0=$(./vsearch.exe $grp $c $Q $t $s 0 4000000000 | tr '\n' ' ')
  echo "$name H'=$grp c=$c Q=$Q t=$t s'=$s M=$M | residue: $r1 | no residue: $r0"
done <<'ROWS'
N22390 3,2,2 8 137 112 37 5
N22392 3,2,2 8 137 112 37 5
N25970 2,13 6 289 264 83 5
N26009 2,13 6 181 132 59 7
N31317 2,17 5 69 20 27 7
N43597 3,2,2 11 223 198 49 5
N43641 3,2,2 11 333 308 61 5
N43697 3,2,2 11 443 418 71 5
N43761 3,2,2 11 597 572 83 5
N46887 2,17 6 181 156 73 5
N46914 2,17 6 97 48 41 7
N61800 3,2,2 13 207 182 47 5
N61885 2,13 9 769 720 137 7
N61887 2,13 9 769 720 137 7
ROWS
