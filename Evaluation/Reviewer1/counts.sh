#!/usr/bin/env bash

set -eu

header() {
  echo "rewrites|proof|time"
}

gen_count() {
  python3 ./gen_count.py "$@"
}

warmup() {
  for proof in autorewrite congruence simp; do
    gen_count --proof $proof --time 300 >/dev/null
  done
}

gen_data() {
  for proof in autorewrite congruence simp; do
    for n in $(seq 1 15) $(seq 16 2 24) $(seq 25 3 60); do
      out=$(gen_count --proof $proof --time $((n * n)))
      echo "$out"
      # if proof times out, don't try larger numbers
      if [[ "$out" =~ .*\|inf$ ]]; then
        break
      fi
      if [ "$n" -ge 10 ]; then
        sleep 2
      fi
    done
    # there are big jumps at powers of 2
    for n in $(seq 5 10); do
      gen_count --proof $proof --time $((2 ** n - 1))
      gen_count --proof $proof --time $((2 ** n))
      sleep 2
    done
  done
}

if [ "$#" -ge 0 ]; then
  out="$1"
  # avoid clobbering output in case run is cancelled
  temp=".$out.tmp"
  header | tee "$temp"
  warmup
  gen_data | tee -a "$temp"
  mv "$temp" "$out"
else
  header
  warmup
  gen_data
fi
