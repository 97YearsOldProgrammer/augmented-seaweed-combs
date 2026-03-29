"""Task 6: What's missing?

Read dataset. Analyze cases where gotoh < lcs (i.e., gap penalties matter).
- Compare lcs_gotoh vs gotoh: how often does the LCS path == Gotoh-optimal path?
- When they differ, what predicts the difference? (by epsilon, by m)
- Print top counterexamples sorted by gap (gotoh - lcs_gotoh)
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

    print(f"Total records: {len(records)}")
    print()

    # Cases where gotoh < lcs (gap penalty is non-trivial)
    gapped = [r for r in records if r["gotoh"] < r["lcs"]]
    print(f"Cases gotoh < lcs (gaps matter): {len(gapped)}/{len(records)} "
          f"({100*len(gapped)/len(records):.1f}%)")
    print()

    # -------------------------------------------------------------------
    # 1. LCS path == Gotoh-optimal: lcs_gotoh == gotoh?
    # -------------------------------------------------------------------
    lcs_path_optimal = [r for r in records if r["lcs_gotoh"] == r["gotoh"]]
    lcs_path_optimal_gapped = [r for r in gapped if r["lcs_gotoh"] == r["gotoh"]]
    print(f"1. LCS path == Gotoh optimal (lcs_gotoh == gotoh):")
    print(f"   All records: {len(lcs_path_optimal)}/{len(records)} "
          f"({100*len(lcs_path_optimal)/len(records):.1f}%)")
    print(f"   Among gapped: {len(lcs_path_optimal_gapped)}/{len(gapped)} "
          f"({100*len(lcs_path_optimal_gapped)/len(gapped) if gapped else 0:.1f}%)")
    print()

    # -------------------------------------------------------------------
    # 2. Difference = gotoh - lcs_gotoh (how much better Gotoh finds)
    # Analyze by epsilon and m
    # -------------------------------------------------------------------
    diff = lambda r: r["gotoh"] - r["lcs_gotoh"]

    # Only consider cases where lcs_gotoh is meaningful (>= 0)
    meaningful = [r for r in gapped if r["lcs_gotoh"] >= 0]
    diff_nonzero = [r for r in meaningful if diff(r) > 0]
    print(f"2. Among gapped cases with lcs_gotoh >= 0: {len(meaningful)}")
    print(f"   gotoh > lcs_gotoh (Gotoh found better path): {len(diff_nonzero)} "
          f"({100*len(diff_nonzero)/len(meaningful) if meaningful else 0:.1f}%)")
    print()

    # By epsilon
    print("   By epsilon:")
    by_eps: dict[int, list] = defaultdict(list)
    by_eps_diff: dict[int, list] = defaultdict(list)
    for r in meaningful:
        by_eps[r["epsilon"]].append(r)
        by_eps_diff[r["epsilon"]].append(diff(r))
    for eps in sorted(by_eps):
        total = len(by_eps[eps])
        diffs = by_eps_diff[eps]
        nonzero = sum(1 for d in diffs if d > 0)
        avg_d = sum(diffs) / total if total else 0
        max_d = max(diffs) if diffs else 0
        print(f"     eps={eps}: {total:5d} cases, gotoh>lcs_gotoh: {nonzero:5d} "
              f"({100*nonzero/total:.1f}%), max_diff={max_d}, avg_diff={avg_d:.3f}")
    print()

    # By m (query length)
    print("   By m (query length):")
    by_m: dict[int, list] = defaultdict(list)
    for r in meaningful:
        by_m[len(r["a"])].append(diff(r))
    for m in sorted(by_m):
        diffs = by_m[m]
        total = len(diffs)
        nonzero = sum(1 for d in diffs if d > 0)
        avg_d = sum(diffs) / total if total else 0
        print(f"     m={m}: {total:5d} cases, gotoh>lcs_gotoh: {nonzero:5d} "
              f"({100*nonzero/total:.1f}%), avg_diff={avg_d:.3f}")
    print()

    # -------------------------------------------------------------------
    # 3. Top counterexamples sorted by (gotoh - lcs_gotoh)
    # -------------------------------------------------------------------
    print("3. Top 10 cases sorted by (gotoh - lcs_gotoh):")
    top = sorted(records, key=diff, reverse=True)[:10]
    print(f"   {'a':>20}  {'b':>20}  {'go':>4}  {'lcs':>4}  {'lcs_gotoh':>10}  "
          f"{'gotoh':>6}  {'diff':>5}  {'eps':>4}  {'diag':>5}")
    for r in top:
        a_str = str(r["a"])
        b_str = str(r["b"])
        d = diff(r)
        print(f"   {a_str:>20}  {b_str:>20}  {r['go']:>4}  {r['lcs']:>4}  "
              f"{r['lcs_gotoh']:>10}  {r['gotoh']:>6}  {d:>5}  "
              f"{r['epsilon']:>4}  {r['diag']:>5}")
    print()

    # -------------------------------------------------------------------
    # 4. Summary: when does the LCS-path-as-alignment fail?
    # -------------------------------------------------------------------
    print("4. Summary:")
    print(f"   LCS path is Gotoh-optimal in "
          f"{len(lcs_path_optimal)}/{len(records)} = "
          f"{100*len(lcs_path_optimal)/len(records):.1f}% of all cases")

    # equal-length vs unequal-length breakdown
    eq = [r for r in records if len(r["a"]) == len(r["b"])]
    uneq = [r for r in records if len(r["a"]) != len(r["b"])]
    eq_opt = sum(1 for r in eq if diff(r) == 0)
    uneq_opt = sum(1 for r in uneq if diff(r) == 0)
    print(f"   Equal-length  : LCS path optimal in {eq_opt}/{len(eq)} "
          f"({100*eq_opt/len(eq):.1f}%)")
    print(f"   Unequal-length: LCS path optimal in {uneq_opt}/{len(uneq)} "
          f"({100*uneq_opt/len(uneq):.1f}%)")
    print()

    # Insight: for equal-length, when does LCS path fail?
    eq_fail = [r for r in eq if diff(r) > 0 and r["lcs_gotoh"] >= 0]
    print(f"   Equal-length failures (diff>0 & lcs_gotoh>=0): {len(eq_fail)}")
    if eq_fail:
        shown = sorted(eq_fail, key=diff, reverse=True)[:5]
        for r in shown:
            print(f"     a={r['a']} b={r['b']} go={r['go']} lcs={r['lcs']} "
                  f"lcs_gotoh={r['lcs_gotoh']} gotoh={r['gotoh']} eps={r['epsilon']}")


if __name__ == "__main__":
    main()
