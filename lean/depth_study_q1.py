"""Task 3: What does depth_col encode?

Read JSON dataset. Deduplicate by (a,b) (go is irrelevant for depth/comb output).
Test hypotheses:
  H2: depth_sum == epsilon?
  H3: depth_nonzero == total_gaps?
  H6: depth_col all-zero iff epsilon == 0?
  H7: depth_row carries complementary info?

Print counterexamples for any failed hypothesis.
Print correlation table: (depth_sum, epsilon) distribution.
"""
import json
import sys
import os
from collections import defaultdict

sys.path.insert(0, os.path.dirname(__file__))

DATA_PATH = os.path.join(os.path.dirname(__file__), "depth_study_data.json")


def main():
    with open(DATA_PATH) as f:
        records = json.load(f)

    # Deduplicate by (a, b) — comb output is independent of go/ge
    seen = set()
    unique = []
    for r in records:
        key = (tuple(r["a"]), tuple(r["b"]))
        if key not in seen:
            seen.add(key)
            unique.append(r)

    print(f"Total records   : {len(records)}")
    print(f"Unique (a,b) pairs: {len(unique)}")
    print()

    # Derived fields per unique pair
    for r in unique:
        dc = r["depth_col"]
        dr = r["depth_row"]
        r["depth_sum_col"] = sum(dc)
        r["depth_nonzero_col"] = sum(1 for x in dc if x > 0)
        r["depth_sum_row"] = sum(dr)
        r["depth_nonzero_row"] = sum(1 for x in dr if x > 0)
        r["depth_col_allzero"] = all(x == 0 for x in dc)
        r["depth_row_allzero"] = all(x == 0 for x in dr)

    # -------------------------------------------------------------------
    # H2: depth_sum_col == epsilon?
    # -------------------------------------------------------------------
    h2_fail = [r for r in unique if r["depth_sum_col"] != r["epsilon"]]
    print(f"H2 (depth_sum_col == epsilon): {len(h2_fail)} counterexamples out of {len(unique)}")
    if h2_fail:
        shown = h2_fail[:5]
        for r in shown:
            print(f"  a={r['a']} b={r['b']} depth_col={r['depth_col']} "
                  f"depth_sum={r['depth_sum_col']} epsilon={r['epsilon']}")
    else:
        print("  HOLDS for all unique pairs")
    print()

    # -------------------------------------------------------------------
    # H3: depth_nonzero_col == total_gaps?
    # -------------------------------------------------------------------
    # total_gaps varies by go, so we use go=1 entries for the unique pairs
    go1 = {(tuple(r["a"]), tuple(r["b"])): r for r in records if r["go"] == 1}
    h3_fail = []
    for r in unique:
        key = (tuple(r["a"]), tuple(r["b"]))
        g = go1[key]
        total_gaps = g["gap_info"]["total_gaps"]
        if r["depth_nonzero_col"] != total_gaps:
            h3_fail.append((r, total_gaps))
    print(f"H3 (depth_nonzero_col == total_gaps from LCS path): "
          f"{len(h3_fail)} counterexamples out of {len(unique)}")
    if h3_fail:
        shown = h3_fail[:5]
        for r, total_gaps in shown:
            print(f"  a={r['a']} b={r['b']} depth_col={r['depth_col']} "
                  f"depth_nonzero={r['depth_nonzero_col']} total_gaps={total_gaps}")
    else:
        print("  HOLDS for all unique pairs")
    print()

    # -------------------------------------------------------------------
    # H6: depth_col all-zero iff epsilon == 0?
    # -------------------------------------------------------------------
    h6_fail_fwd = [r for r in unique if r["depth_col_allzero"] and r["epsilon"] != 0]
    h6_fail_rev = [r for r in unique if not r["depth_col_allzero"] and r["epsilon"] == 0]
    print(f"H6a (allzero => epsilon==0): {len(h6_fail_fwd)} failures")
    print(f"H6b (epsilon==0 => allzero): {len(h6_fail_rev)} failures")
    if not h6_fail_fwd and not h6_fail_rev:
        print("  H6 HOLDS: depth_col all-zero IFF epsilon == 0")
    else:
        for r in h6_fail_fwd[:3]:
            print(f"  [H6a fail] a={r['a']} b={r['b']} depth_col={r['depth_col']} eps={r['epsilon']}")
        for r in h6_fail_rev[:3]:
            print(f"  [H6b fail] a={r['a']} b={r['b']} depth_col={r['depth_col']} eps={r['epsilon']}")
    print()

    # -------------------------------------------------------------------
    # H7: depth_row carries complementary info?
    # We check: depth_sum_row vs epsilon, and allzero correlation
    # -------------------------------------------------------------------
    h7_row_allzero_iff_eps0 = (
        sum(1 for r in unique if r["depth_row_allzero"] != (r["epsilon"] == 0))
    )
    print(f"H7 (depth_row all-zero IFF epsilon==0): "
          f"{h7_row_allzero_iff_eps0} failures out of {len(unique)}")

    h7_sum_eq_eps = sum(1 for r in unique if r["depth_sum_row"] == r["epsilon"])
    print(f"  depth_sum_row == epsilon: {h7_sum_eq_eps}/{len(unique)} "
          f"({100*h7_sum_eq_eps/len(unique):.1f}%)")

    # depth_col and depth_row: are they ever different?
    both_zero = sum(1 for r in unique if r["depth_col_allzero"] and r["depth_row_allzero"])
    col_zero_row_nonzero = sum(1 for r in unique if r["depth_col_allzero"] and not r["depth_row_allzero"])
    col_nonzero_row_zero = sum(1 for r in unique if not r["depth_col_allzero"] and r["depth_row_allzero"])
    both_nonzero = sum(1 for r in unique if not r["depth_col_allzero"] and not r["depth_row_allzero"])
    print(f"  col_zero & row_zero : {both_zero}")
    print(f"  col_zero & row_nonzero: {col_zero_row_nonzero}")
    print(f"  col_nonzero & row_zero: {col_nonzero_row_zero}")
    print(f"  both nonzero: {both_nonzero}")
    print()

    # -------------------------------------------------------------------
    # Correlation table: (depth_sum_col, epsilon)
    # -------------------------------------------------------------------
    table: dict[tuple[int,int], int] = defaultdict(int)
    for r in unique:
        table[(r["depth_sum_col"], r["epsilon"])] += 1

    all_eps = sorted(set(r["epsilon"] for r in unique))
    all_ds  = sorted(set(r["depth_sum_col"] for r in unique))

    print("Correlation table: rows=depth_sum_col, cols=epsilon")
    header = f"{'ds\\eps':>8}" + "".join(f"{e:>8}" for e in all_eps)
    print(header)
    for ds in all_ds:
        row_str = f"{ds:>8}" + "".join(f"{table.get((ds,e),0):>8}" for e in all_eps)
        print(row_str)
    print()

    # Summary
    print("=" * 50)
    h2_ok = len(h2_fail) == 0
    h3_ok = len(h3_fail) == 0
    h6_ok = len(h6_fail_fwd) == 0 and len(h6_fail_rev) == 0
    h7_ok = h7_row_allzero_iff_eps0 == 0
    print(f"H2 (depth_sum == epsilon)       : {'HOLDS' if h2_ok else 'FAILS'}")
    print(f"H3 (depth_nonzero == total_gaps): {'HOLDS' if h3_ok else 'FAILS'}")
    print(f"H6 (allzero iff epsilon==0)     : {'HOLDS' if h6_ok else 'FAILS'}")
    print(f"H7 (depth_row allzero iff eps=0): {'HOLDS' if h7_ok else 'FAILS'}")


if __name__ == "__main__":
    main()
