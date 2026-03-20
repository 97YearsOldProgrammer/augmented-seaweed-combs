#!/usr/bin/env python3
"""Explore depth-excess relationship for SINGLE-WINDOW augmented comb.

In the production pipeline, Phase 2 runs Krusche on specific candidate
windows, not the full reference. So the depth values from a single-window
augmented comb might relate to excess = LCS - diag for that window.
"""
import itertools


def augmented_comb_single(a: str, b: str) -> tuple[list[int], list[int], list[int], list[int]]:
    """Augmented comb on a (m) vs b (n), where n = m (single window)."""
    m, n = len(a), len(b)
    total = m + n
    labels = list(range(total))
    depths = [0] * total

    for c in range(n):
        for r in range(m):
            t = c - r + m - 1
            if t < 0 or t + 1 >= total:
                continue
            is_match = (a[r] == b[c])
            l_left, l_right = labels[t], labels[t + 1]
            d_left, d_right = depths[t], depths[t + 1]

            if is_match:
                labels[t], labels[t + 1] = l_right, l_left
                depths[t], depths[t + 1] = 0, 0
            elif l_left > l_right:
                labels[t], labels[t + 1] = l_right, l_left
                depths[t], depths[t + 1] = d_right + 1, d_left + 1
            else:
                depths[t], depths[t + 1] = d_left + 1, d_right + 1

    d_col = [labels[m + j] for j in range(n)]
    depth_col = [depths[m + j] for j in range(n)]
    d_row = [labels[i] for i in range(m)]
    depth_row = [depths[i] for i in range(m)]
    return d_col, depth_col, d_row, depth_row


def lcs_dp(a: str, b: str) -> int:
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i-1] == b[j-1]:
                dp[i][j] = dp[i-1][j-1] + 1
            else:
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
    return dp[m][n]


def diag_matches(a: str, b: str) -> int:
    return sum(1 for i in range(min(len(a), len(b))) if a[i] == b[i])


def exhaustive_single_window(max_m: int, alphabet: str = "AB"):
    """For each (a, b) with |a| = |b| = m, compute augmented comb
    and check depth-excess relationships."""
    print(f"Exhaustive single-window search: m ≤ {max_m}, alphabet = '{alphabet}'")
    print(f"{'='*80}")

    records = []
    for m in range(2, max_m + 1):
        for a_bits in itertools.product(alphabet, repeat=m):
            a = "".join(a_bits)
            for b_bits in itertools.product(alphabet, repeat=m):
                b = "".join(b_bits)

                d_col, depth_col, d_row, depth_row = augmented_comb_single(a, b)
                lcs_val = lcs_dp(a, b)
                diag_val = diag_matches(a, b)
                excess_val = lcs_val - diag_val

                # Derive quantities from depth
                sum_depth_col = sum(depth_col)
                sum_depth_row = sum(depth_row)
                max_depth_col = max(depth_col)
                min_depth_col = min(depth_col)
                zero_count_col = sum(1 for d in depth_col if d == 0)
                zero_count_row = sum(1 for d in depth_row if d == 0)

                # Count wires that crossed (d_col[j] < m means wire j participated in LCS)
                crossed_col = sum(1 for d in d_col if d < m)

                records.append({
                    "a": a, "b": b, "m": m,
                    "lcs": lcs_val, "diag": diag_val, "excess": excess_val,
                    "d_col": d_col, "depth_col": depth_col,
                    "d_row": d_row, "depth_row": depth_row,
                    "sum_dc": sum_depth_col, "sum_dr": sum_depth_row,
                    "max_dc": max_depth_col, "zeros_c": zero_count_col,
                    "zeros_r": zero_count_row, "crossed": crossed_col,
                })

    nontrivial = [r for r in records if r["excess"] > 0]
    print(f"Total cases: {len(records)}, non-trivial (excess>0): {len(nontrivial)}")

    # ---- Test candidate formulas ----

    formulas = {
        # Simple depth formulas
        "excess == sum_depth_col": lambda r: r["excess"] == r["sum_dc"],
        "excess == sum_depth_row": lambda r: r["excess"] == r["sum_dr"],
        "excess == max_depth_col": lambda r: r["excess"] == r["max_dc"],

        # Crossed-wire formulas
        "excess == crossed - diag": lambda r: r["excess"] == r["crossed"] - r["diag"],
        "excess == lcs - zeros_col": lambda r: r["excess"] == r["lcs"] - r["zeros_c"],
        "excess == lcs - zeros_row": lambda r: r["excess"] == r["lcs"] - r["zeros_r"],

        # Combined formulas
        "excess == crossed - zeros_col": lambda r: r["excess"] == r["crossed"] - r["zeros_c"],
        "excess == m - zeros_col - (m - lcs)": lambda r: r["excess"] == r["zeros_c"] - (r["m"] - r["lcs"]),

        # Bounds
        "excess <= sum_depth_col": lambda r: r["excess"] <= r["sum_dc"],
        "excess <= max_depth_col": lambda r: r["excess"] <= r["max_dc"],
        "excess >= max_depth_col - (m - lcs)": lambda r: r["excess"] >= r["max_dc"] - (r["m"] - r["lcs"]),
    }

    print(f"\n--- Formula tests (on ALL cases including trivial) ---")
    for name, fn in formulas.items():
        holds = all(fn(r) for r in records)
        fails_on = sum(1 for r in records if not fn(r))
        status = "HOLDS" if holds else f"FAILS ({fails_on}/{len(records)})"
        print(f"  {name}: {status}")
        if not holds:
            for r in records:
                if not fn(r):
                    print(f"    CE: a='{r['a']}' b='{r['b']}' excess={r['excess']} "
                          f"dc={r['depth_col']} dr={r['depth_row']} d={r['d_col']} "
                          f"lcs={r['lcs']} diag={r['diag']} crossed={r['crossed']} "
                          f"zeros_c={r['zeros_c']} zeros_r={r['zeros_r']}")
                    break

    # ---- Detailed examples ----
    print(f"\n--- Non-trivial cases (excess > 0), first 25 ---")
    print(f"{'a':>6} {'b':>6} {'m':>2} {'lcs':>4} {'diag':>5} {'exc':>4} "
          f"{'sumd_c':>6} {'sumd_r':>6} {'maxd':>5} {'z_c':>4} {'z_r':>4} {'xd':>3} "
          f"{'depth_col':>12} {'depth_row':>12}")
    for r in nontrivial[:25]:
        print(f"{r['a']:>6} {r['b']:>6} {r['m']:>2} {r['lcs']:>4} {r['diag']:>5} {r['excess']:>4} "
              f"{r['sum_dc']:>6} {r['sum_dr']:>6} {r['max_dc']:>5} {r['zeros_c']:>4} {r['zeros_r']:>4} "
              f"{r['crossed']:>3} "
              f"{str(r['depth_col']):>12} {str(r['depth_row']):>12}")

    # ---- Deeper analysis: look at depth_col[j] for crossed vs non-crossed wires ----
    print(f"\n--- Depth of crossed vs non-crossed wires ---")
    crossed_depths_total = []
    noncrossed_depths_total = []
    for r in nontrivial:
        m = r["m"]
        for j in range(m):
            if r["d_col"][j] < m:  # crossed wire
                crossed_depths_total.append(r["depth_col"][j])
            else:
                noncrossed_depths_total.append(r["depth_col"][j])

    if crossed_depths_total:
        print(f"  Crossed wire depths: {len(crossed_depths_total)} values")
        print(f"    zero count: {sum(1 for d in crossed_depths_total if d == 0)} "
              f"({sum(1 for d in crossed_depths_total if d == 0)/len(crossed_depths_total)*100:.1f}%)")
        print(f"    mean: {sum(crossed_depths_total)/len(crossed_depths_total):.2f}")
    if noncrossed_depths_total:
        print(f"  Non-crossed wire depths: {len(noncrossed_depths_total)} values")
        print(f"    zero count: {sum(1 for d in noncrossed_depths_total if d == 0)} "
              f"({sum(1 for d in noncrossed_depths_total if d == 0)/len(noncrossed_depths_total)*100:.1f}%)")
        print(f"    mean: {sum(noncrossed_depths_total)/len(noncrossed_depths_total):.2f}")

    # ---- Key test: for crossed wires, does depth=0 ↔ diagonal match? ----
    print(f"\n--- Crossed wires: depth=0 vs diagonal match ---")
    cross_diag_match = 0  # crossed wire at diagonal position AND depth=0
    cross_diag_nomatch = 0  # crossed wire at diagonal position AND depth>0
    cross_offdiag_zero = 0  # crossed wire NOT at diagonal AND depth=0
    cross_offdiag_nonzero = 0  # crossed wire NOT at diagonal AND depth>0

    for r in nontrivial:
        m = r["m"]
        for j in range(m):
            if r["d_col"][j] < m:  # crossed wire
                is_diag_match = (r["a"][r["d_col"][j]] == r["b"][j]) if r["d_col"][j] < m else False
                # Actually, "diagonal match at j" means a[j] == b[j]
                is_diag_pos = (r["a"][j] == r["b"][j])
                if r["depth_col"][j] == 0:
                    if is_diag_pos:
                        cross_diag_match += 1
                    else:
                        cross_offdiag_zero += 1
                else:
                    if is_diag_pos:
                        cross_diag_nomatch += 1
                    else:
                        cross_offdiag_nonzero += 1

    print(f"  depth=0 + diag_match: {cross_diag_match}")
    print(f"  depth=0 + off-diag:   {cross_offdiag_zero}")
    print(f"  depth>0 + diag_match: {cross_diag_nomatch}")
    print(f"  depth>0 + off-diag:   {cross_offdiag_nonzero}")


if __name__ == "__main__":
    exhaustive_single_window(max_m=5, alphabet="AB")
