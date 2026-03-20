#!/usr/bin/env python3
"""Computational exploration: what is the relationship between
augmented comb depth values and excess = LCS - diag?

Traces the augmented seaweed comb cell-by-cell on small examples,
then checks every alignment window position for the depth-excess relationship.
"""
import itertools
from typing import NamedTuple


class CombState(NamedTuple):
    """Labels and depths for all m+n wires."""
    labels: list[int]    # m+n wire labels
    col_depth: list[int] # n column depths
    row_depth: list[int] # m row depths


def augmented_comb(a: str, b: str) -> tuple[list[int], list[int], list[int], list[int]]:
    """Run the augmented seaweed comb on strings a (query, m) and b (ref, n).

    Returns (d_col, depth_col, d_row, depth_row) at the boundary.
    Wire indexing: wires 0..m-1 are row wires, m..m+n-1 are column wires.
    Cell (r, c) connects wires at t = c - r + m - 1 and t + 1.
    """
    m, n = len(a), len(b)
    total = m + n

    # Initialize labels: identity permutation
    labels = list(range(total))
    # Initialize depths: all zero
    depths = [0] * total

    # Process cells column by column, row by row
    for c in range(n):
        for r in range(m):
            t = c - r + m - 1
            if t < 0 or t + 1 >= total:
                continue

            is_match = (a[r] == b[c])

            l_left = labels[t]
            l_right = labels[t + 1]
            d_left = depths[t]
            d_right = depths[t + 1]

            if is_match:
                # Swap labels, reset both depths
                labels[t] = l_right
                labels[t + 1] = l_left
                depths[t] = 0
                depths[t + 1] = 0
            elif l_left > l_right:
                # Mismatch + swap: swap labels, swap+increment depths
                labels[t] = l_right
                labels[t + 1] = l_left
                depths[t] = d_right + 1
                depths[t + 1] = d_left + 1
            else:
                # Mismatch + stay: keep labels, increment depths
                depths[t] = d_left + 1
                depths[t + 1] = d_right + 1

    # Extract boundary values
    # d_col[j] = label at wire position m + j (column wires at boundary)
    # d_row[i] = label at wire position i (row wires at boundary)
    d_col = [labels[m + j] for j in range(n)]
    depth_col = [depths[m + j] for j in range(n)]
    d_row = [labels[i] for i in range(m)]
    depth_row = [depths[i] for i in range(m)]

    return d_col, depth_col, d_row, depth_row


def lcs_dp(a: str, b: str) -> int:
    """Standard LCS via DP."""
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i-1] == b[j-1]:
                dp[i][j] = dp[i-1][j-1] + 1
            else:
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
    return dp[m][n]


def diag_matches(a: str, b: str, pos: int) -> int:
    """Count diagonal matches: #{i : a[i] == b[pos+i]}."""
    m = len(a)
    count = 0
    for i in range(m):
        if pos + i < len(b) and a[i] == b[pos + i]:
            count += 1
    return count


def semi_local_lcs(a: str, b: str, pos: int) -> int:
    """LCS of a against b[pos:pos+m]."""
    m = len(a)
    window = b[pos:pos + m]
    if len(window) < m:
        return 0
    return lcs_dp(a, window)


def count_transform_lcs(d_col: list[int], m: int, n: int, pos: int) -> int:
    """Extract LCS at position pos from d_col via count transform.

    For semi-local LCS(a, b[pos:pos+m]):
    LCS = #{j in [pos, pos+m) : d_col[j] < m} ... actually this is tricky.

    Let's just verify against DP.
    """
    # The semi-local string-substring LCS for b[i..j] is:
    # lcs(i, j) = (j - i) - |{k in [i,j) : d_col[k] >= m}|
    # Wait no, the count transform is:
    # c[t] = t - h[t] where h is the permutation
    # For the string-substring problem, LCS(a, b[i..j]) involves
    # the d_col values in a specific way.
    #
    # Actually, for a contiguous window b[pos..pos+m-1]:
    # LCS = m - #{k in d_col[pos..pos+m-1] : d_col[k] >= m}
    # No that's not right either.
    #
    # Let me just use DP for verification.
    return semi_local_lcs(d_col, m, n, pos)  # placeholder


def explore(a: str, b: str):
    """Explore depth-excess relationship for strings a, b."""
    m, n = len(a), len(b)
    d_col, depth_col, d_row, depth_row = augmented_comb(a, b)

    print(f"\na = '{a}' (m={m})")
    print(f"b = '{b}' (n={n})")
    print(f"d_col    = {d_col}")
    print(f"depth_col = {depth_col}")
    print(f"d_row    = {d_row}")
    print(f"depth_row = {depth_row}")

    # For each window position, compute LCS, diag, excess
    print(f"\n{'pos':>4} {'LCS':>4} {'diag':>5} {'excess':>7} | depth_col window | relationship")
    print("-" * 75)

    for pos in range(n - m + 1):
        lcs_val = semi_local_lcs(a, b, pos)
        diag_val = diag_matches(a, b, pos)
        excess_val = lcs_val - diag_val

        # Depth values in the window
        window_depths = depth_col[pos:pos + m]
        sum_depths = sum(window_depths)
        max_depth = max(window_depths) if window_depths else 0
        min_depth = min(window_depths) if window_depths else 0
        zero_count = sum(1 for d in window_depths if d == 0)

        # Try various relationships
        relationships = []
        if excess_val == sum_depths:
            relationships.append(f"excess == sum_depths")
        if excess_val == max_depth:
            relationships.append(f"excess == max_depth")
        if excess_val == m - zero_count - diag_val:
            relationships.append(f"excess == m-zeros-diag")

        rel_str = ", ".join(relationships) if relationships else ""

        print(f"{pos:>4} {lcs_val:>4} {diag_val:>5} {excess_val:>7} | "
              f"{window_depths} sum={sum_depths} max={max_depth} zeros={zero_count} | {rel_str}")


def exhaustive_binary(max_m: int, max_n: int):
    """Exhaustive search over binary strings for depth-excess patterns."""
    print(f"\n{'='*70}")
    print(f"Exhaustive search: binary strings m≤{max_m}, n≤{max_n}")
    print(f"{'='*70}")

    # Track which relationships hold universally
    relationships_hold = {
        "excess_le_sum_depths": True,
        "excess_le_max_depth": True,
        "sum_depths_le_m_times_excess": True,
    }
    counterexamples = {k: [] for k in relationships_hold}

    total_cases = 0
    for m in range(1, max_m + 1):
        for n in range(m, max_n + 1):
            for a_bits in itertools.product("AB", repeat=m):
                a = "".join(a_bits)
                for b_bits in itertools.product("AB", repeat=n):
                    b = "".join(b_bits)

                    d_col, depth_col, d_row, depth_row = augmented_comb(a, b)

                    for pos in range(n - m + 1):
                        total_cases += 1
                        lcs_val = semi_local_lcs(a, b, pos)
                        diag_val = diag_matches(a, b, pos)
                        excess_val = lcs_val - diag_val

                        window_depths = depth_col[pos:pos + m]
                        sum_depths = sum(window_depths)
                        max_depth = max(window_depths) if window_depths else 0

                        if excess_val > sum_depths:
                            relationships_hold["excess_le_sum_depths"] = False
                            if len(counterexamples["excess_le_sum_depths"]) < 3:
                                counterexamples["excess_le_sum_depths"].append(
                                    (a, b, pos, excess_val, sum_depths, window_depths))

                        if excess_val > max_depth:
                            relationships_hold["excess_le_max_depth"] = False
                            if len(counterexamples["excess_le_max_depth"]) < 3:
                                counterexamples["excess_le_max_depth"].append(
                                    (a, b, pos, excess_val, max_depth, window_depths))

                        if sum_depths > m * excess_val and excess_val > 0:
                            relationships_hold["sum_depths_le_m_times_excess"] = False
                            if len(counterexamples["sum_depths_le_m_times_excess"]) < 3:
                                counterexamples["sum_depths_le_m_times_excess"].append(
                                    (a, b, pos, excess_val, sum_depths, window_depths))

    print(f"\nTotal cases tested: {total_cases}")
    for rel, holds in relationships_hold.items():
        status = "HOLDS" if holds else "FAILS"
        print(f"  {rel}: {status}")
        if not holds and counterexamples[rel]:
            for ce in counterexamples[rel]:
                a, b, pos, exc, val, wd = ce
                print(f"    counterexample: a='{a}' b='{b}' pos={pos} excess={exc} val={val} depths={wd}")


def find_exact_formula(max_m: int, max_n: int):
    """Try to find an exact formula: excess = f(depth_col, d_col, position)."""
    print(f"\n{'='*70}")
    print(f"Searching for exact formula: m≤{max_m}, n≤{max_n}")
    print(f"{'='*70}")

    # Collect all (excess, features) pairs
    records = []
    for m in range(2, max_m + 1):  # m≥2 for non-trivial cases
        for n in range(m, max_n + 1):
            for a_bits in itertools.product("AB", repeat=m):
                a = "".join(a_bits)
                for b_bits in itertools.product("AB", repeat=n):
                    b = "".join(b_bits)

                    d_col, depth_col, d_row, depth_row = augmented_comb(a, b)

                    for pos in range(n - m + 1):
                        lcs_val = semi_local_lcs(a, b, pos)
                        diag_val = diag_matches(a, b, pos)
                        excess_val = lcs_val - diag_val

                        if excess_val == 0:
                            continue  # Skip trivial cases

                        window_depths = depth_col[pos:pos + m]
                        window_dcol = d_col[pos:pos + m]
                        sum_depths = sum(window_depths)
                        max_depth = max(window_depths)
                        min_depth = min(window_depths)
                        zero_count = sum(1 for d in window_depths if d == 0)
                        nonzero_count = m - zero_count

                        # Count wires with d_col < m (these participate in LCS)
                        lcs_wires = sum(1 for d in window_dcol if d < m)

                        records.append({
                            "a": a, "b": b, "pos": pos, "m": m,
                            "lcs": lcs_val, "diag": diag_val, "excess": excess_val,
                            "sum_depths": sum_depths, "max_depth": max_depth,
                            "min_depth": min_depth, "zero_count": zero_count,
                            "nonzero_count": nonzero_count,
                            "lcs_wires": lcs_wires,
                            "depths": window_depths, "dcol": window_dcol,
                        })

    if not records:
        print("No non-trivial cases found.")
        return

    print(f"Non-trivial cases (excess > 0): {len(records)}")

    # Check candidate formulas
    candidates = {
        "excess == nonzero_count - (m - lcs)": lambda r: r["excess"] == r["nonzero_count"] - (r["m"] - r["lcs"]),
        "excess == lcs - zero_count": lambda r: r["excess"] == r["lcs"] - r["zero_count"],
        "excess == sum_depths - (m - lcs) * ?": None,  # placeholder
    }

    # Brute force: check excess == lcs - zero_count
    formula1_holds = all(r["excess"] == r["lcs"] - r["zero_count"] for r in records)
    print(f"\n  excess == lcs - zero_count: {'HOLDS' if formula1_holds else 'FAILS'}")
    if not formula1_holds:
        for r in records[:5]:
            if r["excess"] != r["lcs"] - r["zero_count"]:
                print(f"    a='{r['a']}' b='{r['b']}' pos={r['pos']} excess={r['excess']} "
                      f"lcs-zeros={r['lcs'] - r['zero_count']} depths={r['depths']}")

    # Check: excess == lcs_wires - diag
    formula2_holds = all(r["excess"] == r["lcs_wires"] - r["diag"] for r in records)
    print(f"  excess == lcs_wires - diag: {'HOLDS' if formula2_holds else 'FAILS'}")
    if not formula2_holds:
        for r in records[:5]:
            if r["excess"] != r["lcs_wires"] - r["diag"]:
                print(f"    a='{r['a']}' b='{r['b']}' pos={r['pos']} excess={r['excess']} "
                      f"lcs_wires-diag={r['lcs_wires'] - r['diag']} depths={r['depths']} dcol={r['dcol']}")

    # Print some examples for manual inspection
    print(f"\nSample cases (excess > 0):")
    print(f"{'a':>6} {'b':>8} {'pos':>4} {'m':>2} {'lcs':>4} {'diag':>5} {'exc':>4} "
          f"{'sum_d':>6} {'max_d':>6} {'zeros':>6} {'depths':>15} {'dcol':>15}")
    for r in records[:20]:
        print(f"{r['a']:>6} {r['b']:>8} {r['pos']:>4} {r['m']:>2} {r['lcs']:>4} {r['diag']:>5} {r['excess']:>4} "
              f"{r['sum_depths']:>6} {r['max_depth']:>6} {r['zero_count']:>6} "
              f"{str(r['depths']):>15} {str(r['dcol']):>15}")


if __name__ == "__main__":
    # Manual examples
    print("=== Manual examples ===")
    explore("AB", "AABB")
    explore("AB", "BA")
    explore("ABA", "BABAB")
    explore("ABC", "ACBC")

    # Exhaustive binary search
    exhaustive_binary(max_m=4, max_n=6)

    # Formula search
    find_exact_formula(max_m=4, max_n=6)
