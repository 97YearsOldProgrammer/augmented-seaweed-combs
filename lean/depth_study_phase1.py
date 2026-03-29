"""Task 2: Generate exhaustive dataset for the depth column information study.

Covers equal-length AND unequal-length sequence pairs:
  |a| in {1,2,3,4}, |b| in {|a|, ..., 5}, alphabet {0,1,2}
  go in {1,2,3}, ge = 1

For each (a, b, go, ge) computes:
  d_col, depth_col, d_row, depth_row
  lcs, diag, epsilon, gotoh, lcs_gap_structure
  lcs_gotoh = lcs - gap_info.total_penalty

Saves to lean/depth_study_data.json.
Verifies chain: diag <= gotoh <= lcs for ALL cases.
"""
import json
import itertools
import time
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))
from depth_study_lib import (
    augmented_comb, lcs_dp, gotoh_dp, lcs_gap_structure,
    diag_count, lcs_from_dcol,
)

ALPHABET = [0, 1, 2]
GE = 1


def main():
    t0 = time.perf_counter()

    records = []
    chain_violations = []
    epsilon_counts: dict[int, int] = {}

    for m in range(1, 5):           # |a| in {1,2,3,4}
        for n in range(m, 6):       # |b| in {|a|, ..., 5}
            for a_tup in itertools.product(ALPHABET, repeat=m):
                for b_tup in itertools.product(ALPHABET, repeat=n):
                    a = list(a_tup)
                    b = list(b_tup)

                    # Compute comb (independent of go)
                    d_col, depth_col, d_row, depth_row = augmented_comb(a, b)
                    lcs = lcs_from_dcol(d_col, m)
                    diag = diag_count(a, b)
                    epsilon = lcs - diag

                    for go in [1, 2, 3]:
                        gotoh = gotoh_dp(a, b, go, GE)
                        gap_info = lcs_gap_structure(a, b, go, GE)
                        lcs_gotoh = lcs - gap_info.total_penalty

                        # Verify chain: gotoh <= lcs always; diag <= gotoh only for equal-length
                        if gotoh > lcs:
                            chain_violations.append({
                                "type": "gotoh>lcs",
                                "a": a, "b": b, "go": go,
                                "diag": diag, "gotoh": gotoh, "lcs": lcs,
                            })
                        if m == n and diag > gotoh:
                            chain_violations.append({
                                "type": "diag>gotoh (equal-len)",
                                "a": a, "b": b, "go": go,
                                "diag": diag, "gotoh": gotoh, "lcs": lcs,
                            })

                        epsilon_counts[epsilon] = epsilon_counts.get(epsilon, 0) + 1

                        records.append({
                            "a": a, "b": b, "go": go, "ge": GE,
                            "d_col": d_col,
                            "depth_col": depth_col,
                            "d_row": d_row,
                            "depth_row": depth_row,
                            "lcs": lcs,
                            "diag": diag,
                            "epsilon": epsilon,
                            "gotoh": gotoh,
                            "lcs_gotoh": lcs_gotoh,
                            "gap_info": {
                                "num_gaps_a": gap_info.num_gaps_a,
                                "num_gaps_b": gap_info.num_gaps_b,
                                "total_ext_a": gap_info.total_ext_a,
                                "total_ext_b": gap_info.total_ext_b,
                                "total_gaps": gap_info.total_gaps,
                                "total_penalty": gap_info.total_penalty,
                            },
                        })

    t1 = time.perf_counter()
    elapsed = t1 - t0

    out_path = os.path.join(os.path.dirname(__file__), "depth_study_data.json")
    with open(out_path, "w") as f:
        json.dump(records, f, separators=(",", ":"))

    # Stats
    print(f"Cases generated : {len(records)}")
    print(f"Elapsed time    : {elapsed:.2f}s")
    print(f"Chain violations: {len(chain_violations)}")
    if chain_violations:
        print("  FIRST VIOLATION:", chain_violations[0])
    else:
        print("  gotoh <= lcs HOLDS for all cases")
        print("  diag <= gotoh HOLDS for all equal-length cases")

    print("\nEpsilon distribution:")
    for eps in sorted(epsilon_counts):
        pct = 100.0 * epsilon_counts[eps] / len(records)
        print(f"  epsilon={eps}: {epsilon_counts[eps]:6d} ({pct:.1f}%)")

    print(f"\nSaved to {out_path}")
    assert elapsed < 60, f"Generation took {elapsed:.1f}s, exceeds 60s limit"


if __name__ == "__main__":
    main()
