"""Task 4: Tighter lower bound?

Read dataset. Check:
1. Validity: gotoh >= lcs_gotoh for ALL cases? (LCS path is a feasible Gotoh alignment)
2. Tightness: lcs_gotoh > diag for SOME cases? (only when lcs_gotoh >= 0)
3. How often is lcs_gotoh negative (useless)?
"""
import json
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))

DATA_PATH = os.path.join(os.path.dirname(__file__), "depth_study_data.json")


def main():
    with open(DATA_PATH) as f:
        records = json.load(f)

    print(f"Total records: {len(records)}")
    print()

    # -------------------------------------------------------------------
    # 1. Validity: gotoh >= lcs_gotoh for ALL cases?
    # -------------------------------------------------------------------
    validity_fail = [r for r in records if r["gotoh"] < r["lcs_gotoh"]]
    print(f"1. Validity (gotoh >= lcs_gotoh): {len(validity_fail)} violations")
    if validity_fail:
        for r in validity_fail[:5]:
            print(f"  a={r['a']} b={r['b']} go={r['go']} "
                  f"lcs={r['lcs']} lcs_gotoh={r['lcs_gotoh']} gotoh={r['gotoh']}")
    else:
        print("  HOLDS: LCS path is always a feasible Gotoh alignment")
    print()

    # -------------------------------------------------------------------
    # 2. Tightness: lcs_gotoh > diag for SOME cases? (only count lcs_gotoh >= 0)
    # -------------------------------------------------------------------
    useful = [r for r in records if r["lcs_gotoh"] >= 0]
    tighter = [r for r in useful if r["lcs_gotoh"] > r["diag"]]
    print(f"2. Tightness (lcs_gotoh > diag, among lcs_gotoh >= 0):")
    print(f"   Records with lcs_gotoh >= 0: {len(useful)}/{len(records)} "
          f"({100*len(useful)/len(records):.1f}%)")
    print(f"   lcs_gotoh > diag: {len(tighter)}/{len(useful)} "
          f"({100*len(tighter)/len(useful) if useful else 0:.1f}%)")
    if tighter:
        shown = sorted(tighter, key=lambda r: r["lcs_gotoh"] - r["diag"], reverse=True)[:5]
        print("   Top 5 cases where lcs_gotoh > diag:")
        for r in shown:
            print(f"    a={r['a']} b={r['b']} go={r['go']} "
                  f"diag={r['diag']} lcs_gotoh={r['lcs_gotoh']} gotoh={r['gotoh']} "
                  f"lcs={r['lcs']} eps={r['epsilon']}")
    print()

    # -------------------------------------------------------------------
    # 3. How often is lcs_gotoh negative?
    # -------------------------------------------------------------------
    negative = [r for r in records if r["lcs_gotoh"] < 0]
    zero = [r for r in records if r["lcs_gotoh"] == 0]
    positive = [r for r in records if r["lcs_gotoh"] > 0]
    print(f"3. lcs_gotoh distribution:")
    print(f"   lcs_gotoh < 0  : {len(negative):6d} ({100*len(negative)/len(records):.1f}%)")
    print(f"   lcs_gotoh == 0 : {len(zero):6d} ({100*len(zero)/len(records):.1f}%)")
    print(f"   lcs_gotoh > 0  : {len(positive):6d} ({100*len(positive)/len(records):.1f}%)")
    print()

    # By go value
    for go in [1, 2, 3]:
        sub = [r for r in records if r["go"] == go]
        neg = sum(1 for r in sub if r["lcs_gotoh"] < 0)
        print(f"   go={go}: lcs_gotoh < 0 in {neg}/{len(sub)} "
              f"({100*neg/len(sub):.1f}%)")
    print()

    # By equal vs unequal length
    eq = [r for r in records if len(r["a"]) == len(r["b"])]
    uneq = [r for r in records if len(r["a"]) != len(r["b"])]
    eq_neg = sum(1 for r in eq if r["lcs_gotoh"] < 0)
    uneq_neg = sum(1 for r in uneq if r["lcs_gotoh"] < 0)
    print(f"   equal-length  : lcs_gotoh < 0 in {eq_neg}/{len(eq)} "
          f"({100*eq_neg/len(eq):.1f}%)")
    print(f"   unequal-length: lcs_gotoh < 0 in {uneq_neg}/{len(uneq)} "
          f"({100*uneq_neg/len(uneq):.1f}%)")
    print()

    # -------------------------------------------------------------------
    # Summary
    # -------------------------------------------------------------------
    print("=" * 50)
    print(f"Validity (gotoh >= lcs_gotoh): {'HOLDS' if not validity_fail else 'FAILS'}")
    print(f"Tighter than diag (lcs_gotoh >= 0): {len(tighter)} cases = "
          f"{'YES, tighter bound exists' if tighter else 'NO'}")
    print(f"Useful (lcs_gotoh >= 0): {len(useful)}/{len(records)} = "
          f"{100*len(useful)/len(records):.1f}%")


if __name__ == "__main__":
    main()
