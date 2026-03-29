"""Task 5: Tighter upper bound?

Read dataset. Search for f(depth) such that gotoh <= lcs - f(depth) universally.
Candidate functions:
  f1: min(go, depth_sum * ge) when depth_sum > 0
  f2: go * depth_nonzero
  f3: go * (number of 0->nonzero transitions in depth_col)
  f4: min(go, depth_max * ge)

For each: count violations, print first counterexample if any.
Also: empirical max correction by depth_sum.
Tightness ratio for valid candidates.
"""
import json
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))

DATA_PATH = os.path.join(os.path.dirname(__file__), "depth_study_data.json")


def transitions_count(depth_col: list[int]) -> int:
    """Count 0->nonzero transitions in depth_col."""
    count = 0
    prev_zero = True
    for x in depth_col:
        if x > 0 and prev_zero:
            count += 1
        prev_zero = (x == 0)
    return count


def main():
    with open(DATA_PATH) as f:
        records = json.load(f)

    print(f"Total records: {len(records)}")
    print()

    # Precompute per-record derived fields
    for r in records:
        dc = r["depth_col"]
        r["depth_sum"] = sum(dc)
        r["depth_nonzero"] = sum(1 for x in dc if x > 0)
        r["depth_max"] = max(dc) if dc else 0
        r["depth_transitions"] = transitions_count(dc)

    # -------------------------------------------------------------------
    # For each candidate, check: gotoh <= lcs - f(depth)?
    # (f can depend on go/ge)
    # -------------------------------------------------------------------

    def check_candidate(name, f_fn):
        """f_fn(r) -> correction value. Check gotoh <= lcs - f_fn(r)."""
        violations = []
        tight_count = 0
        total_nonzero_f = 0
        for r in records:
            fval = f_fn(r)
            if fval > 0:
                total_nonzero_f += 1
                if r["gotoh"] <= r["lcs"] - fval:
                    tight_count += 1
                else:
                    violations.append((r, fval))

        print(f"Candidate {name}:")
        print(f"  Violations   : {len(violations)}")
        if violations:
            r, fval = violations[0]
            print(f"  First counter: a={r['a']} b={r['b']} go={r['go']} "
                  f"lcs={r['lcs']} gotoh={r['gotoh']} f={fval} "
                  f"lcs-f={r['lcs']-fval} depth_col={r['depth_col']}")
        if total_nonzero_f > 0:
            ratio = 100.0 * tight_count / total_nonzero_f
            print(f"  Tight (gotoh == lcs - f): {tight_count}/{total_nonzero_f} "
                  f"({ratio:.1f}%) [among f > 0 cases]")
        print()

    # f1: min(go, depth_sum * ge) when depth_sum > 0
    check_candidate(
        "f1 = min(go, depth_sum*ge)",
        lambda r: min(r["go"], r["depth_sum"] * r["ge"]) if r["depth_sum"] > 0 else 0
    )

    # f2: go * depth_nonzero
    check_candidate(
        "f2 = go * depth_nonzero",
        lambda r: r["go"] * r["depth_nonzero"]
    )

    # f3: go * transitions
    check_candidate(
        "f3 = go * transitions(depth_col)",
        lambda r: r["go"] * r["depth_transitions"]
    )

    # f4: min(go, depth_max * ge)
    check_candidate(
        "f4 = min(go, depth_max*ge)",
        lambda r: min(r["go"], r["depth_max"] * r["ge"]) if r["depth_max"] > 0 else 0
    )

    # -------------------------------------------------------------------
    # Empirical: what IS the max correction = lcs - gotoh, by depth_sum?
    # -------------------------------------------------------------------
    print("Empirical: max(lcs - gotoh) grouped by depth_sum:")
    from collections import defaultdict
    by_ds: dict[int, list] = defaultdict(list)
    for r in records:
        by_ds[r["depth_sum"]].append(r["lcs"] - r["gotoh"])

    print(f"  {'depth_sum':>12}  {'count':>8}  {'max_corr':>10}  {'min_corr':>10}  {'mean_corr':>10}")
    for ds in sorted(by_ds):
        vals = by_ds[ds]
        print(f"  {ds:>12}  {len(vals):>8}  {max(vals):>10}  {min(vals):>10}  "
              f"{sum(vals)/len(vals):>10.2f}")
    print()

    # -------------------------------------------------------------------
    # Bonus: depth_sum vs (lcs - gotoh) scatter
    # How tight is depth_sum as an upper bound for the correction?
    # -------------------------------------------------------------------
    print("Depth_sum vs (lcs - gotoh) analysis:")
    ds_ge_correction = sum(1 for r in records if r["depth_sum"] >= r["lcs"] - r["gotoh"])
    print(f"  depth_sum >= (lcs - gotoh): {ds_ge_correction}/{len(records)} "
          f"({100*ds_ge_correction/len(records):.1f}%)")
    ds_lt_correction = [r for r in records if r["depth_sum"] < r["lcs"] - r["gotoh"]]
    if ds_lt_correction:
        print(f"  depth_sum < (lcs - gotoh): {len(ds_lt_correction)} cases (counterexamples to depth_sum as upper bound)")
        for r in ds_lt_correction[:3]:
            print(f"    a={r['a']} b={r['b']} go={r['go']} depth_sum={r['depth_sum']} "
                  f"lcs-gotoh={r['lcs']-r['gotoh']} lcs={r['lcs']} gotoh={r['gotoh']}")
    print()


if __name__ == "__main__":
    main()
