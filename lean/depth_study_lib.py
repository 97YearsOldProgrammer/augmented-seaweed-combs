"""Shared computation library for the depth column information study.

Provides: gotoh_dp, lcs_dp, lcs_alignment_path, lcs_gap_structure,
          diag_count, augmented_comb, lcs_from_dcol.

Comb convention (Krusche distance representation):
  d_col[j] = displacement distance of the seaweed at column j.
  d_row per row = displacement of the row seaweed after each row.
  LCS extraction: #{j : d_col[j] > j}  (global full-sequence LCS).
  Depth tracking follows explore_depth_excess.py semantics:
    match      -> swap distances, reset both depths to 0.
    mismatch+swap (d_col > d_row) -> swap distances, swap+increment depths.
    mismatch+stay                 -> keep distances, increment both depths.
"""
from typing import NamedTuple
import itertools


# ---------------------------------------------------------------------------
# Public types
# ---------------------------------------------------------------------------

class GapInfo(NamedTuple):
    """Gap structure extracted from an LCS alignment path.

    Gaps in a: positions where j advances but i stays (insertions into a).
    Gaps in b: positions where i advances but j stays (deletions from a).
    """
    num_gaps_a: int       # number of gap runs in a (insertions)
    num_gaps_b: int       # number of gap runs in b (deletions)
    total_ext_a: int      # total extension length of gaps in a
    total_ext_b: int      # total extension length of gaps in b
    total_gaps: int       # num_gaps_a + num_gaps_b
    total_penalty: int    # sum of gap penalties (go per run + ge per extension)


# ---------------------------------------------------------------------------
# 1. Gotoh DP (global affine gap alignment)
# ---------------------------------------------------------------------------

def gotoh_dp(a: list, b: list, go: int, ge: int) -> int:
    """Global Gotoh affine gap DP returning H[m][n].

    Scoring: +1 match, 0 mismatch, -go gap open, -ge gap extend.
    A gap of length k costs go + k*ge (open + extend * length).

    Initializes both row direction (H[i][0], E[i][0]) and column direction
    (H[0][j], F[0][j]) with gap penalties for global alignment.
    """
    m, n = len(a), len(b)
    NEG_INF = -(10 ** 9)

    # H[i][j] = best score for a[:i] vs b[:j]
    # E[i][j] = best score ending with gap in b (i advances, j stays = deletion from a)
    # F[i][j] = best score ending with gap in a (j advances, i stays = insertion)
    H = [[NEG_INF] * (n + 1) for _ in range(m + 1)]
    E = [[NEG_INF] * (n + 1) for _ in range(m + 1)]
    F = [[NEG_INF] * (n + 1) for _ in range(m + 1)]

    H[0][0] = 0

    # Initialize column direction: gaps in a (j advances, i stays)
    for j in range(1, n + 1):
        H[0][j] = -(go + j * ge)
        F[0][j] = -(go + j * ge)

    # Initialize row direction: gaps in b (i advances, j stays)
    for i in range(1, m + 1):
        H[i][0] = -(go + i * ge)
        E[i][0] = -(go + i * ge)

    for i in range(1, m + 1):
        for j in range(1, n + 1):
            # E: gap in b (deletion from a) — i advances, j fixed
            E[i][j] = max(
                H[i - 1][j] - go - ge,   # open new gap
                E[i - 1][j] - ge,         # extend existing gap
            )
            # F: gap in a (insertion into a) — j advances, i fixed
            F[i][j] = max(
                H[i][j - 1] - go - ge,   # open new gap
                F[i][j - 1] - ge,         # extend existing gap
            )
            match_score = 1 if a[i - 1] == b[j - 1] else 0
            H[i][j] = max(
                H[i - 1][j - 1] + match_score,
                E[i][j],
                F[i][j],
            )

    return H[m][n]


# ---------------------------------------------------------------------------
# 2. LCS DP
# ---------------------------------------------------------------------------

def lcs_dp(a: list, b: list) -> int:
    """Standard LCS via DP."""
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i - 1] == b[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
    return dp[m][n]


# ---------------------------------------------------------------------------
# 3. LCS alignment path (traceback)
# ---------------------------------------------------------------------------

def lcs_alignment_path(a: list, b: list) -> list[tuple[int, int]]:
    """Traceback one LCS alignment path.

    Returns list of (i, j) pairs (0-indexed) where a[i] == b[j] is matched.
    """
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i - 1] == b[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])

    # Traceback
    path = []
    i, j = m, n
    while i > 0 and j > 0:
        if a[i - 1] == b[j - 1] and dp[i][j] == dp[i - 1][j - 1] + 1:
            path.append((i - 1, j - 1))
            i -= 1
            j -= 1
        elif dp[i - 1][j] >= dp[i][j - 1]:
            i -= 1
        else:
            j -= 1

    path.reverse()
    return path


# ---------------------------------------------------------------------------
# 4. LCS gap structure
# ---------------------------------------------------------------------------

def lcs_gap_structure(a: list, b: list, go: int, ge: int) -> GapInfo:
    """Extract gap structure from LCS alignment.

    Tracks gaps in a (insertions: j advances, i stays) and gaps in b
    (deletions: i advances, j stays) separately. When both di > 0 and
    dj > 0 between consecutive matches, counts as TWO gap-opens.
    Includes head gaps (before first match) and tail gaps (after last match).

    total_penalty = go * total_gaps + ge * (total_ext_a + total_ext_b)
    """
    path = lcs_alignment_path(a, b)
    m, n = len(a), len(b)

    num_gaps_a = 0
    num_gaps_b = 0
    total_ext_a = 0
    total_ext_b = 0

    def _account_gap(di: int, dj: int):
        """Account for the gap segment between two anchor points.

        di = number of steps in a (gap in b / deletions from a).
        dj = number of steps in b (gap in a / insertions).
        Both can be nonzero: counts as two separate gap opens.
        """
        nonlocal num_gaps_a, num_gaps_b, total_ext_a, total_ext_b
        if dj > 0:
            num_gaps_a += 1
            total_ext_a += dj
        if di > 0:
            num_gaps_b += 1
            total_ext_b += di

    if not path:
        # No matches: entire a and b are gaps
        _account_gap(m, n)
    else:
        # Head gap: before first match
        first_i, first_j = path[0]
        _account_gap(first_i, first_j)

        # Gaps between consecutive matches
        for k in range(len(path) - 1):
            i1, j1 = path[k]
            i2, j2 = path[k + 1]
            di = i2 - i1 - 1   # steps in a between matches (excluding match positions)
            dj = j2 - j1 - 1   # steps in b between matches
            _account_gap(di, dj)

        # Tail gap: after last match
        last_i, last_j = path[-1]
        di_tail = m - 1 - last_i
        dj_tail = n - 1 - last_j
        _account_gap(di_tail, dj_tail)

    total_gaps = num_gaps_a + num_gaps_b
    total_penalty = go * total_gaps + ge * (total_ext_a + total_ext_b)

    return GapInfo(
        num_gaps_a=num_gaps_a,
        num_gaps_b=num_gaps_b,
        total_ext_a=total_ext_a,
        total_ext_b=total_ext_b,
        total_gaps=total_gaps,
        total_penalty=total_penalty,
    )


# ---------------------------------------------------------------------------
# 5. Diagonal match count
# ---------------------------------------------------------------------------

def diag_count(a: list, b: list) -> int:
    """Count diagonal matches #{i : a[i] == b[i]}."""
    return sum(1 for i in range(min(len(a), len(b))) if a[i] == b[i])


# ---------------------------------------------------------------------------
# 6. Augmented comb (Krusche distance representation)
# ---------------------------------------------------------------------------

def augmented_comb(
    a: list, b: list
) -> tuple[list[int], list[int], list[int], list[int]]:
    """Run the augmented seaweed comb on sequences a (query, m) and b (ref, n).

    Uses the Krusche distance representation (ported from explore_depth_excess.py
    depth semantics, aligned with the Lean CombComposition.lean definition).

    Returns (d_col, depth_col, d_row, depth_row) where:
      d_col[j]     = displacement distance of seaweed at column j (length n).
      depth_col[j] = depth of seaweed at column j (length n).
      d_row[r]     = final displacement distance of row seaweed r (length m).
      depth_row[r] = final depth of row seaweed r (length m).

    Wire indexing: m+n wires, d_row seaweed r starts at displacement r+1.
    Cell (r, c): row seaweed d_row interacts with column seaweed d_col[c].

    Rules per cell (matching explore_depth_excess.py depth semantics):
      match         -> swap distances, reset both depths to 0.
      mismatch+swap (d_col[c] > d_row) -> swap, swap+increment depths.
      mismatch+stay                     -> no swap, increment both depths.
    """
    m, n = len(a), len(b)
    d_col = [0] * n
    depth_col = [0] * n
    d_row_out = []
    depth_row_out = []

    for r, qchar in enumerate(a):
        d_row = r + 1
        dr_depth = 0

        for c in range(n):
            dc = d_col[c]
            dc_depth = depth_col[c]
            is_match = (qchar == b[c])

            if is_match:
                # Swap distances, reset both depths
                d_col[c], d_row = d_row, dc + 1
                depth_col[c], dr_depth = 0, 0
            elif dc > d_row:
                # Mismatch + swap: swap distances, swap+increment depths
                d_col[c], d_row = d_row, dc + 1
                depth_col[c], dr_depth = dr_depth + 1, dc_depth + 1
            else:
                # Mismatch + stay: no swap, increment both depths
                d_row = d_row + 1
                dr_depth += 1
                depth_col[c] = dc_depth + 1

        d_row_out.append(d_row)
        depth_row_out.append(dr_depth)

    return d_col, depth_col, d_row_out, depth_row_out


# ---------------------------------------------------------------------------
# 7. LCS from d_col
# ---------------------------------------------------------------------------

def lcs_from_dcol(d_col: list[int], m: int) -> int:
    """Global LCS from Krusche d_col: #{j : d_col[j] > j}.

    For the full-sequence LCS(a, b) with m = len(a), n = len(b):
    d_col[j] > j counts seaweeds that have advanced past their starting column.

    Note: the m parameter is accepted for API compatibility but the formula
    #{j : d_col[j] > j} does not depend on m (see CrossingCountLCS.lean).
    """
    return sum(1 for j, v in enumerate(d_col) if v > j)


# ---------------------------------------------------------------------------
# Module-level verification
# ---------------------------------------------------------------------------

# --- gotoh_dp assertions ---
assert gotoh_dp([0, 1, 0], [0, 1, 0], 2, 1) == 3, (
    f"gotoh_dp([0,1,0],[0,1,0],2,1) = {gotoh_dp([0,1,0],[0,1,0],2,1)}, expected 3"
)
assert gotoh_dp([0], [0], 1, 1) == 1, (
    f"gotoh_dp([0],[0],1,1) = {gotoh_dp([0],[0],1,1)}, expected 1"
)
assert gotoh_dp([0], [1], 1, 1) == 0, (
    f"gotoh_dp([0],[1],1,1) = {gotoh_dp([0],[1],1,1)}, expected 0"
)
assert gotoh_dp([0, 0, 0], [1, 1, 1], 1, 1) == 0, (
    f"gotoh_dp([0,0,0],[1,1,1],1,1) = {gotoh_dp([0,0,0],[1,1,1],1,1)}, expected 0"
)

# --- lcs_dp assertions ---
assert lcs_dp([0, 1, 0], [0, 1, 0]) == 3, (
    f"lcs_dp([0,1,0],[0,1,0]) = {lcs_dp([0,1,0],[0,1,0])}, expected 3"
)

# --- diag_count assertions ---
assert diag_count([0, 1, 0], [1, 0, 1]) == 0, (
    f"diag_count([0,1,0],[1,0,1]) = {diag_count([0,1,0],[1,0,1])}, expected 0"
)

# --- Cross-check: augmented_comb LCS matches lcs_dp for all |a|=3,|b|=4,alphabet={0,1,2} ---
_failures = []
for _a_tup in itertools.product(range(3), repeat=3):
    for _b_tup in itertools.product(range(3), repeat=4):
        _a = list(_a_tup)
        _b = list(_b_tup)
        _d_col, _, _, _ = augmented_comb(_a, _b)
        _comb_lcs = lcs_from_dcol(_d_col, len(_a))
        _dp_lcs = lcs_dp(_a, _b)
        if _comb_lcs != _dp_lcs:
            _failures.append((_a, _b, _comb_lcs, _dp_lcs))

assert not _failures, (
    f"augmented_comb LCS mismatch in {len(_failures)} cases; "
    f"first: a={_failures[0][0]} b={_failures[0][1]} "
    f"comb={_failures[0][2]} dp={_failures[0][3]}"
)
